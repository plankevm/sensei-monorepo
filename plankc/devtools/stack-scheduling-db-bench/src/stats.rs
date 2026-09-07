use std::{fmt::Write, time::Duration};

const PERCENTILES: &[usize] = &[1, 5, 20, 50, 80, 95, 99];
const METRIC_WIDTH: usize = 30;
const VALUE_WIDTH: usize = 16;
const SUBSET_VALUE_WIDTH: usize = 18;
const DELTA_LABEL_WIDTH: usize = 20;
const DELTA_WIDTH: usize = 7;

pub struct Stats {
    entire_corpus: ComparisonStats,
    manually_optimized: ComparisonStats,
}

struct ComparisonStats {
    graph_count: usize,
    best_known_total_gas: u64,
    local_total_gas: u64,
    improvements: usize,
    gas_saved: u64,
    capped_searches: usize,
    deltas: Vec<i64>,
}

impl Stats {
    pub fn new(graph_count: usize, manually_optimized_count: usize) -> Self {
        assert!(manually_optimized_count <= graph_count);
        Self {
            entire_corpus: ComparisonStats::new(graph_count),
            manually_optimized: ComparisonStats::new(manually_optimized_count),
        }
    }

    pub fn record(
        &mut self,
        best_known_gas: u64,
        local_gas: u64,
        candidate_limit_reached: bool,
        manually_optimized: bool,
    ) {
        self.entire_corpus.record(best_known_gas, local_gas, candidate_limit_reached);
        if manually_optimized {
            self.manually_optimized.record(best_known_gas, local_gas, candidate_limit_reached);
        }
    }

    pub fn render(mut self, elapsed: Duration) -> String {
        self.entire_corpus.prepare();
        self.manually_optimized.prepare();

        let mut output = String::new();
        writeln!(output, "Stack scheduling benchmark").unwrap();
        writeln!(
            output,
            "Processed {} graphs in {:.2}s",
            format_usize(self.entire_corpus.graph_count),
            elapsed.as_secs_f64()
        )
        .unwrap();

        writeln!(
            output,
            "\n{:<METRIC_WIDTH$} {:>VALUE_WIDTH$} {:>SUBSET_VALUE_WIDTH$}",
            "Metric", "Entire corpus", "Hand-optimized"
        )
        .unwrap();
        writeln!(output, "{}", "─".repeat(METRIC_WIDTH + VALUE_WIDTH + SUBSET_VALUE_WIDTH + 2))
            .unwrap();
        for (label, entire, manually_optimized) in [
            (
                "Graphs",
                format_usize(self.entire_corpus.graph_count),
                format_usize(self.manually_optimized.graph_count),
            ),
            (
                "Best-known gas",
                format_u64(self.entire_corpus.best_known_total_gas),
                format_u64(self.manually_optimized.best_known_total_gas),
            ),
            (
                "Current scheduler gas",
                format_u64(self.entire_corpus.local_total_gas),
                format_u64(self.manually_optimized.local_total_gas),
            ),
            (
                "Relative score",
                self.entire_corpus.score_percent(),
                self.manually_optimized.score_percent(),
            ),
            (
                "Scheduler improvements",
                format_usize(self.entire_corpus.improvements),
                format_usize(self.manually_optimized.improvements),
            ),
            (
                "Gas saved",
                format_u64(self.entire_corpus.gas_saved),
                format_u64(self.manually_optimized.gas_saved),
            ),
            (
                "Candidate limit reached",
                format_usize(self.entire_corpus.capped_searches),
                format_usize(self.manually_optimized.capped_searches),
            ),
        ] {
            writeln!(
                output,
                "{label:<METRIC_WIDTH$} {entire:>VALUE_WIDTH$} {manually_optimized:>SUBSET_VALUE_WIDTH$}"
            )
            .unwrap();
        }

        writeln!(output, "\nGas delta: best known − current scheduler").unwrap();
        writeln!(output, "Negative values mean the current scheduler is worse.\n").unwrap();
        write!(output, "{:<DELTA_LABEL_WIDTH$}", "Subset").unwrap();
        for percentile in PERCENTILES {
            write!(output, "{percentile:>DELTA_WIDTH$}", percentile = format!("p{percentile}"))
                .unwrap();
        }
        writeln!(output).unwrap();
        writeln!(output, "{}", "─".repeat(DELTA_LABEL_WIDTH + DELTA_WIDTH * PERCENTILES.len()))
            .unwrap();
        self.entire_corpus.render_deltas(&mut output, "Entire corpus");
        self.manually_optimized.render_deltas(&mut output, "Hand-optimized");
        output.pop();
        output
    }
}

impl ComparisonStats {
    fn new(graph_count: usize) -> Self {
        Self {
            graph_count,
            best_known_total_gas: 0,
            local_total_gas: 0,
            improvements: 0,
            gas_saved: 0,
            capped_searches: 0,
            deltas: Vec::with_capacity(graph_count),
        }
    }

    fn record(&mut self, best_known_gas: u64, local_gas: u64, candidate_limit_reached: bool) {
        self.best_known_total_gas = self
            .best_known_total_gas
            .checked_add(best_known_gas)
            .expect("best-known total gas overflow");
        self.local_total_gas =
            self.local_total_gas.checked_add(local_gas).expect("local total gas overflow");
        let best_known = i64::try_from(best_known_gas).expect("best-known gas does not fit i64");
        let local = i64::try_from(local_gas).expect("local gas does not fit i64");
        let delta = best_known.checked_sub(local).expect("gas delta overflow");
        self.deltas.push(delta);
        if delta > 0 {
            self.improvements += 1;
            self.gas_saved = self
                .gas_saved
                .checked_add(u64::try_from(delta).expect("positive gas delta does not fit u64"))
                .expect("saved gas overflow");
        }
        self.capped_searches += usize::from(candidate_limit_reached);
    }

    fn prepare(&mut self) {
        assert_eq!(self.deltas.len(), self.graph_count);
        self.deltas.sort_unstable();
    }

    fn score_percent(&self) -> String {
        if self.graph_count == 0 {
            return "n/a".to_owned();
        }
        if self.local_total_gas == 0 {
            return if self.best_known_total_gas == 0 {
                "100.00%".to_owned()
            } else {
                "∞%".to_owned()
            };
        }
        format!("{:.2}%", self.best_known_total_gas as f64 / self.local_total_gas as f64 * 100.0)
    }

    fn render_deltas(&self, output: &mut String, label: &str) {
        write!(output, "{label:<DELTA_LABEL_WIDTH$}").unwrap();
        for &percentile in PERCENTILES {
            let delta = if self.deltas.is_empty() {
                "—".to_owned()
            } else {
                format_i64(nearest_rank(&self.deltas, percentile))
            };
            write!(output, "{delta:>DELTA_WIDTH$}").unwrap();
        }
        writeln!(output).unwrap();
    }
}

fn nearest_rank(sorted: &[i64], percentile: usize) -> i64 {
    assert!(!sorted.is_empty());
    assert!((1..=100).contains(&percentile));
    let rank =
        percentile.checked_mul(sorted.len()).expect("percentile rank overflow").div_ceil(100);
    sorted[rank - 1]
}

fn format_usize(value: usize) -> String {
    format_u64(u64::try_from(value).expect("count does not fit u64"))
}

fn format_i64(value: i64) -> String {
    if value < 0 {
        format!("-{}", format_u64(value.unsigned_abs()))
    } else {
        format_u64(u64::try_from(value).expect("nonnegative value does not fit u64"))
    }
}

fn format_u64(mut value: u64) -> String {
    if value == 0 {
        return "0".to_owned();
    }
    let mut groups = Vec::new();
    while value != 0 {
        groups.push(value % 1_000);
        value /= 1_000;
    }
    let mut output = groups.pop().expect("nonzero value has at least one digit group").to_string();
    while let Some(group) = groups.pop() {
        write!(output, ",{group:03}").unwrap();
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use plank_test_utils::dedent_preserve_indent;

    #[test]
    fn renders_complete_statistics_for_the_corpus_and_manually_optimized_subset() {
        let mut stats = Stats::new(5, 3);
        stats.record(10, 15, false, false);
        stats.record(10, 12, true, true);
        stats.record(10, 10, false, false);
        stats.record(10, 8, false, true);
        stats.record(10, 3, false, true);

        let expected = dedent_preserve_indent(
            r#"
            Stack scheduling benchmark
            Processed 5 graphs in 1.25s

            Metric                            Entire corpus     Hand-optimized
            ──────────────────────────────────────────────────────────────────
            Graphs                                        5                  3
            Best-known gas                               50                 30
            Current scheduler gas                        48                 23
            Relative score                          104.17%            130.43%
            Scheduler improvements                        2                  2
            Gas saved                                     9                  9
            Candidate limit reached                       1                  1

            Gas delta: best known − current scheduler
            Negative values mean the current scheduler is worse.

            Subset                   p1     p5    p20    p50    p80    p95    p99
            ─────────────────────────────────────────────────────────────────────
            Entire corpus            -5     -5     -5      0      2      7      7
            Hand-optimized           -2     -2     -2      2      7      7      7
            "#,
        );
        assert_eq!(stats.render(Duration::from_millis(1250)), expected);
    }

    #[test]
    fn renders_an_empty_manually_optimized_subset() {
        let mut stats = Stats::new(1, 0);
        stats.record(10, 10, false, false);

        let expected = dedent_preserve_indent(
            r#"
            Stack scheduling benchmark
            Processed 1 graphs in 0.00s

            Metric                            Entire corpus     Hand-optimized
            ──────────────────────────────────────────────────────────────────
            Graphs                                        1                  0
            Best-known gas                               10                  0
            Current scheduler gas                        10                  0
            Relative score                          100.00%                n/a
            Scheduler improvements                        0                  0
            Gas saved                                     0                  0
            Candidate limit reached                       0                  0

            Gas delta: best known − current scheduler
            Negative values mean the current scheduler is worse.

            Subset                   p1     p5    p20    p50    p80    p95    p99
            ─────────────────────────────────────────────────────────────────────
            Entire corpus             0      0      0      0      0      0      0
            Hand-optimized            —      —      —      —      —      —      —
            "#,
        );
        assert_eq!(stats.render(Duration::ZERO), expected);
    }

    #[test]
    fn groups_large_numbers() {
        assert_eq!(format_u64(1_234_567), "1,234,567");
        assert_eq!(format_i64(-12_345), "-12,345");
    }
}
