#!/usr/bin/env bun

import { appendFileSync, chmodSync, constants, existsSync, mkdirSync, realpathSync, writeFileSync } from "node:fs";
import { access } from "node:fs/promises";
import { dirname, resolve } from "node:path";
import {
	createAgentSession,
	createBashTool,
	DefaultResourceLoader,
	getAgentDir,
	ModelRuntime,
	SessionManager,
	SettingsManager,
	type AgentSessionEvent,
} from "@earendil-works/pi-coding-agent";
import { Database } from "bun:sqlite";

const ROOT = resolve(import.meta.dir, "../..");
const MODEL = "openai-codex/gpt-5.6-luna";
const PROMPT = `Optimize the stack schedule for canonical hash {hash} (initial cost {cost}).
Run ./inspect {hash} first. graph.json is available for scratch scripts.
Submit improvements using ./submit {hash}, passing whitespace-separated operations
on stdin: swapN dupN pop opN opNf storeN loadN. Stacks are top-first;
swap/dup depths are 1..16, operation IDs and sequential spill slots start at 0.
Costs: swap/dup/pop=3, store=9, load=6, op/op-flipped=0.
Respect data/effect dependencies and finalization. Use rejection traces to fix
candidates. Submit improvements promptly; only cheaper valid schedules are saved.
Your private scratch folder is ./scratch. Put all solver scripts, candidates,
and temporary files there. Do not use /tmp or any shared scratch directory.
Work only in this job directory. Do not edit the repository or database directly,
invoke Cargo, launch other agents, or leave background processes running.
Use single-process searches. Python is only for quick checks, preprocessing,
and short searches. Every Python script must be run with a timeout of at most
300 seconds. If you expect a search to take longer, write it in standalone Rust
from the start. If a Python search reaches its timeout, do not rerun it or extend
the timeout: port it to Rust and compile it with optimization:
rustc -O ./scratch/search.rs -o ./scratch/search
Keep source and executables in ./scratch. Long Rust searches may run without a
timeout. Stop when useful approaches are exhausted.
`;

interface Options {
	concurrency: number;
	limit: number;
	database: string;
	runsDatabase: string;
}

interface CanonicalRow {
	canonical_hash: string;
	canonical_graph: string;
	best_gas_cost: number;
	manually_optimized: boolean;
}

interface Totals {
	initial: number;
	final: number;
}

export interface WorkerSession {
	subscribe(listener: (event: AgentSessionEvent) => void): () => void;
	prompt(text: string): Promise<void>;
	abort(): Promise<void>;
	dispose(): void;
	readonly state: { messages: readonly unknown[] };
}

export interface WorkerJob {
	hash: string;
	cost: number;
	directory: string;
	scratch: string;
}

export type SessionFactory = (job: WorkerJob) => Promise<WorkerSession>;

function usage(): string {
	return `Usage: bun scripts/ssch-batch/run.ts [options]

Options:
  --concurrency N       Number of concurrent sessions (default: 6)
  --limit N             Limit unrun positive-cost blocks; 0 means all
  --database PATH       Canonical schedule database
  --runs-database PATH  Run history database (default: beside canonical DB)
  -h, --help            Show this help`;
}

function parseInteger(name: string, value: string | undefined): number {
	const parsed = value === undefined || !/^\d+$/.test(value) ? Number.NaN : Number(value);
	if (!Number.isSafeInteger(parsed)) throw new Error(`${name} requires a nonnegative integer`);
	return parsed;
}

function parseOptions(argv: string[]): Options | null {
	let concurrency = 6;
	let limit = 0;
	let database = resolve(ROOT, "corpus/stack-scheduling-db/canonical-blocks.sqlite3");
	let runsDatabase: string | undefined;

	for (let index = 0; index < argv.length; index++) {
		const argument = argv[index];
		if (argument === "-h" || argument === "--help") return null;
		const equals = argument.indexOf("=");
		const name = equals === -1 ? argument : argument.slice(0, equals);
		const value = equals === -1 ? argv[++index] : argument.slice(equals + 1);
		switch (name) {
			case "--concurrency":
				concurrency = parseInteger(name, value);
				break;
			case "--limit":
				limit = parseInteger(name, value);
				break;
			case "--database":
				if (!value) throw new Error(`${name} requires a path`);
				database = resolve(value);
				break;
			case "--runs-database":
				if (!value) throw new Error(`${name} requires a path`);
				runsDatabase = resolve(value);
				break;
			default:
				throw new Error(`unknown option: ${name}`);
		}
	}

	if (concurrency < 1) throw new Error("concurrency must be positive");
	if (!existsSync(database)) throw new Error(`canonical database does not exist: ${database}`);
	database = realpathSync(database);
	runsDatabase ??= resolve(dirname(database), "luna-runs.sqlite3");
	if (resolve(runsDatabase) === database || (existsSync(runsDatabase) && realpathSync(runsDatabase) === database)) {
		throw new Error("run stats must use a separate database");
	}

	return { concurrency, limit, database, runsDatabase: resolve(runsDatabase) };
}

function shellQuote(value: string): string {
	return `'${value.replaceAll("'", `'"'"'`)}'`;
}

function cleanActivity(text: string): string {
	return Array.from(text.replaceAll(/\s+/g, " ").trim())
		.filter((character) => !/\p{Cc}|\p{Cf}/u.test(character))
		.join("");
}

function activity(event: AgentSessionEvent): string | undefined {
	if (event.type === "tool_execution_start") {
		const args = event.args as Record<string, unknown>;
		return `${event.toolName}: ${String(args.command ?? args.path ?? "")}`;
	}
	if (event.type === "tool_execution_end") return `${event.toolName}: ${event.isError ? "failed" : "done"}`;
	if (event.type === "message_update") {
		const type = event.assistantMessageEvent.type;
		if (type === "thinking_start") return "thinking...";
		if (type === "text_start") return "responding...";
	}
	if (event.type === "message_end" && event.message.role === "assistant") {
		if (event.message.stopReason === "error" || event.message.stopReason === "aborted") {
			return `${event.message.stopReason}: ${event.message.errorMessage ?? ""}`;
		}
	}
	if (event.type === "auto_retry_start") return `provider retry: ${event.errorMessage}`;
	if (event.type === "compaction_start") return "compacting context...";
	return undefined;
}

function lastAssistantStopReason(session: WorkerSession): string | undefined {
	for (let index = session.state.messages.length - 1; index >= 0; index--) {
		const message = session.state.messages[index] as { role?: string; stopReason?: string };
		if (message.role === "assistant") return message.stopReason;
	}
	return undefined;
}

export async function createRealSessionFactory(): Promise<SessionFactory> {
	const [provider, modelId] = MODEL.split("/", 2);
	const modelRuntime = await ModelRuntime.create();
	const model = modelRuntime.getModel(provider, modelId);
	if (!model) throw new Error(`model is unavailable: ${MODEL}`);
	const agentDir = getAgentDir();

	return async (job) => {
		const bashTool = createBashTool(job.directory, {
			spawnHook: ({ command, cwd, env }) => ({
				command,
				cwd,
				env: { ...env, TMPDIR: job.scratch, TMP: job.scratch, TEMP: job.scratch },
			}),
		});
		const settingsManager = SettingsManager.inMemory({}, { projectTrusted: true });
		const resourceLoader = new DefaultResourceLoader({
			cwd: job.directory,
			agentDir,
			settingsManager,
			noExtensions: true,
			noSkills: true,
			noPromptTemplates: true,
			noThemes: true,
			noContextFiles: true,
			extensionFactories: [
				(pi) => {
					pi.registerTool({
						...bashTool,
						execute: (id, params, signal, onUpdate) => bashTool.execute(id, params, signal, onUpdate),
					});
				},
			],
		});
		await resourceLoader.reload();
		const { session } = await createAgentSession({
			cwd: job.directory,
			agentDir,
			modelRuntime,
			model,
			thinkingLevel: "high",
			tools: ["read", "bash", "edit", "write"],
			resourceLoader,
			sessionManager: SessionManager.inMemory(job.directory),
			settingsManager,
		});
		return session;
	};
}

function completedTotals(database: Database): Totals {
	return database
		.query<{ initial: number; final: number }, []>(
			"SELECT COALESCE(SUM(initial_gas_cost), 0) AS initial, " +
				"COALESCE(SUM(final_gas_cost), 0) AS final FROM ssch_runs WHERE status = 'completed'",
		)
		.get()!;
}

export async function runBatch(argv = process.argv.slice(2), injectedFactory?: SessionFactory): Promise<number> {
	let options: Options | null;
	try {
		options = parseOptions(argv);
	} catch (error) {
		console.error(`error: ${error instanceof Error ? error.message : String(error)}\n\n${usage()}`);
		return 2;
	}
	if (!options) {
		console.log(usage());
		return 0;
	}

	const binaries = new Map(
		["inspect", "submit"].map((name) => [name, resolve(ROOT, `target/release/sir-stack-scheduling-db-${name}`)]),
	);
	for (const binary of binaries.values()) {
		try {
			await access(binary, constants.X_OK);
		} catch {
			console.error(`error: build the release tools first: ${binary}`);
			return 2;
		}
	}

	process.env.PI_OFFLINE = "1";
	const runs = new Database(options.runsDatabase, { create: true });
	const canonical = new Database(options.database);
	runs.exec("PRAGMA journal_mode = WAL");
	runs.exec("PRAGMA busy_timeout = 30000");
	canonical.exec("PRAGMA busy_timeout = 30000");
	runs.exec(`CREATE TABLE IF NOT EXISTS ssch_runs (
		canonical_hash TEXT PRIMARY KEY,
		status TEXT NOT NULL CHECK (status IN ('completed', 'failed')),
		exit_code INTEGER NOT NULL,
		finished_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
		initial_gas_cost INTEGER CHECK (initial_gas_cost >= 0),
		final_gas_cost INTEGER CHECK (final_gas_cost >= 0)
	)`);

	let completed = completedTotals(runs);
	const alreadyRun = new Set(
		runs.query<{ canonical_hash: string }, []>("SELECT canonical_hash FROM ssch_runs").all().map((row) => row.canonical_hash),
	);
	const markManuallyOptimized = canonical.query(
		"UPDATE canonical_blocks SET manually_optimized = TRUE WHERE canonical_hash = ?",
	);
	canonical.transaction((hashes: string[]) => {
		for (const hash of hashes) markManuallyOptimized.run(hash);
	})(Array.from(alreadyRun));
	let rows = canonical
		.query<CanonicalRow, []>(
			"SELECT canonical_hash, canonical_graph, best_gas_cost, manually_optimized FROM canonical_blocks " +
				"WHERE best_gas_cost > 0 AND NOT manually_optimized ORDER BY canonical_hash",
		)
		.all();
	if (options.limit) rows = rows.slice(0, options.limit);

	const previousRuns = canonical
		.query<{ value: number }, []>("SELECT COUNT(*) AS value FROM canonical_blocks WHERE manually_optimized")
		.get()!.value;
	let finished = previousRuns;
	const total = previousRuns + rows.length;
	let currentGas = canonical
		.query<{ value: number }, []>("SELECT COALESCE(SUM(best_gas_cost), 0) AS value FROM canonical_blocks")
		.get()!.value;
	const baselineGas = currentGas + completed.initial - completed.final;
	const inline = process.stdout.isTTY;
	const workerRows = Array.from({ length: Math.min(options.concurrency, rows.length) }, (_, index) =>
		`worker ${index + 1}: waiting`,
	);
	const activeSessions = new Map<number, WorkerSession>();
	let nextRow = 0;
	let draining = false;
	let forcing = false;
	let forcePromise: Promise<void> | undefined;

	const draw = () => {
		const saved = baselineGas - currentGas;
		const percent = baselineGas ? (saved / baselineGas) * 100 : 0;
		const state = forcing ? " | stopping" : draining ? " | draining (Ctrl+C again to force)" : "";
		const header = `finished ${finished}/${total} | DB gas ${baselineGas} -> ${currentGas} | saved ${saved} (${percent.toFixed(2)}%)${state}`;
		const completedSaved = completed.initial - completed.final;
		const completedPercent = completed.initial ? (completedSaved / completed.initial) * 100 : 0;
		const summary = `completed gas ${completed.initial} -> ${completed.final} | saved ${completedSaved} (${completedPercent.toFixed(2)}%)`;
		if (inline) {
			const width = Math.max(1, (process.stdout.columns ?? 80) - 1);
			const frame = [header, summary, ...workerRows]
				.map((line) => `\r\x1b[2K${line.slice(0, width)}\n`)
				.join("");
			process.stdout.write(`\x1b[${workerRows.length + 2}A${frame}`);
		} else {
			console.log(`${header}\n${summary}`);
		}
	};

	const refresh = () => {
		const gas = canonical
			.query<{ value: number }, []>("SELECT COALESCE(SUM(best_gas_cost), 0) AS value FROM canonical_blocks")
			.get()!.value;
		const nextCompleted = completedTotals(runs);
		const changed =
			gas !== currentGas || nextCompleted.initial !== completed.initial || nextCompleted.final !== completed.final;
		currentGas = gas;
		completed = nextCompleted;
		if (changed) draw();
		return changed;
	};

	const forceStop = (): Promise<void> => {
		if (forcePromise) return forcePromise;
		draining = true;
		forcing = true;
		draw();
		forcePromise = Promise.all(
			Array.from(activeSessions.values(), async (session) => {
				try {
					await session.abort();
				} catch (error) {
					console.error(`failed to abort worker: ${error instanceof Error ? error.message : String(error)}`);
				}
			}),
		).then(() => undefined);
		return forcePromise;
	};
	const onInterrupt = () => {
		if (draining) void forceStop();
		else {
			draining = true;
			draw();
		}
	};
	const onTerminate = () => void forceStop();
	process.on("SIGINT", onInterrupt);
	process.on("SIGTERM", onTerminate);
	process.on("SIGHUP", onTerminate);

	console.log(`dispatching ${rows.length} blocks with ${options.concurrency} workers; ${previousRuns} already ran`);
	if (inline) process.stdout.write("\n".repeat(workerRows.length + 2));
	draw();

	let sessionFactoryPromise: Promise<SessionFactory> | undefined = injectedFactory
		? Promise.resolve(injectedFactory)
		: undefined;
	const getSessionFactory = () => (sessionFactoryPromise ??= createRealSessionFactory());
	const insertRun = runs.query(
		"INSERT INTO ssch_runs " +
			"(canonical_hash, status, exit_code, initial_gas_cost, final_gas_cost) VALUES (?, ?, ?, ?, ?)",
	);
	const finalCost = canonical.query<{ best_gas_cost: number }, [string]>(
		"SELECT best_gas_cost FROM canonical_blocks WHERE canonical_hash = ?",
	);

	const dispatch = async (row: CanonicalRow, slot: number) => {
		const hash = row.canonical_hash;
		const shortHash = hash.replace(/^ssb1:/, "").slice(0, 12);
		const directory = resolve(ROOT, "tmp/ssch-batch", hash);
		const scratch = resolve(directory, "scratch");
		const report = (raw: string) => {
			const text = `worker ${slot + 1} [${shortHash}]: ${cleanActivity(raw)}`;
			if (inline) {
				workerRows[slot] = text.replaceAll(/[^\x20-\x7e]/g, "?");
				draw();
			} else console.log(text.slice(0, 240));
		};

		mkdirSync(scratch, { recursive: true });
		await Bun.write(resolve(directory, "graph.json"), row.canonical_graph);
		for (const [name, binary] of binaries) {
			const wrapper = resolve(directory, name);
			writeFileSync(wrapper, `#!/bin/sh\nexec ${shellQuote(binary)} --database ${shellQuote(options.database)} "$@"\n`);
			chmodSync(wrapper, 0o755);
		}
		const eventLog = resolve(directory, "pi.jsonl");
		const errorLog = resolve(directory, "stderr.log");
		writeFileSync(eventLog, "");
		writeFileSync(errorLog, "");

		let session: WorkerSession | undefined;
		let unsubscribe: (() => void) | undefined;
		let promptError: unknown;
		let stopReason: string | undefined;
		try {
			const factory = await getSessionFactory();
			session = await factory({ hash, cost: row.best_gas_cost, directory, scratch });
			activeSessions.set(slot, session);
			unsubscribe = session.subscribe((event) => {
				appendFileSync(eventLog, `${JSON.stringify(event)}\n`);
				const message = activity(event);
				if (message) report(message);
				if (event.type === "tool_execution_end") refresh();
			});
			if (forcing) await session.abort();
			else {
				report(`started (gas ${row.best_gas_cost})`);
				await session.prompt(PROMPT.replace("{hash}", hash).replace("{cost}", String(row.best_gas_cost)));
				stopReason = lastAssistantStopReason(session);
			}
		} catch (error) {
			promptError = error;
			appendFileSync(errorLog, `${error instanceof Error ? error.stack ?? error.message : String(error)}\n`);
		} finally {
			unsubscribe?.();
			if (session) {
				if (activeSessions.get(slot) === session) activeSessions.delete(slot);
				session.dispose();
			}
		}

		const interrupted = forcing || stopReason === "aborted";
		if (interrupted) {
			report("stopped; logs: " + directory);
			return;
		}
		const status = promptError === undefined && stopReason === "stop" ? "completed" : "failed";
		const cost = finalCost.get(hash)!.best_gas_cost;
		insertRun.run(hash, status, status === "completed" ? 0 : 1, row.best_gas_cost, cost);
		markManuallyOptimized.run(hash);
		finished++;
		report(`${status}; logs: ${directory}`);
		if (!refresh() && !inline) draw();
	};

	const worker = async (slot: number) => {
		while (!draining) {
			const index = nextRow++;
			if (index >= rows.length) return;
			try {
				await dispatch(rows[index], slot);
			} catch (error) {
				await forceStop();
				throw error;
			}
		}
	};

	try {
		const outcomes = await Promise.allSettled(workerRows.map((_, slot) => worker(slot)));
		if (forcePromise) await forcePromise;
		const failure = outcomes.find((outcome) => outcome.status === "rejected");
		if (failure?.status === "rejected") throw failure.reason;
		refresh();
		return 0;
	} finally {
		process.off("SIGINT", onInterrupt);
		process.off("SIGTERM", onTerminate);
		process.off("SIGHUP", onTerminate);
		for (const session of activeSessions.values()) session.dispose();
		canonical.close();
		runs.close();
	}
}

if (import.meta.main) {
	process.exitCode = await runBatch();
}
