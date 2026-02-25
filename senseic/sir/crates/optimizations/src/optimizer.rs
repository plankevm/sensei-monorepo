use sir_analyses::DefUse;
use sir_data::EthIRProgram;

use crate::{
    constant_propagation::SCCPAnalysis, copy_propagation::CopyPropagation,
    defragmenter::Defragmenter, unused_operation_elimination::UnusedOperationElimination,
};

use with_analysis::WithAnalysis;
mod with_analysis {

    pub(super) struct WithAnalysis<P> {
        inner: P,
        valid: bool,
    }

    impl<P> WithAnalysis<P> {
        pub(super) fn new(inner: P) -> Self {
            Self { inner, valid: false }
        }

        pub(super) fn get_valid(&self) -> Option<&P> {
            self.valid.then_some(&self.inner)
        }

        pub(super) fn invalidate(&mut self) {
            self.valid = false;
        }

        pub(super) fn validate(&mut self) {
            self.valid = true;
        }

        pub(super) fn get_ignoring_validity_mut(&mut self) -> &mut P {
            &mut self.inner
        }
    }
}

pub struct Optimizer {
    src: EthIRProgram,
    dst: Option<EthIRProgram>,

    uses: Option<DefUse>,

    sccp: Option<WithAnalysis<SCCPAnalysis>>,
    copy_prop: Option<CopyPropagation>,
    unused_elim: Option<UnusedOperationElimination>,
    defragmenter: Option<Defragmenter>,
}

impl Optimizer {
    pub fn new(program: EthIRProgram) -> Self {
        Self {
            src: program,
            dst: None,
            uses: None,
            sccp: None,
            copy_prop: None,
            unused_elim: None,
            defragmenter: None,
        }
    }

    pub fn run_passes(&mut self, passes: &str) {
        for c in passes.chars() {
            // Defensively invalidating the analysis is the default.
            let mut invalidates_sccp = true;

            match c {
                's' => {
                    self.run_sccp();
                    invalidates_sccp = false;
                }
                'c' => {
                    self.run_copy_prop();
                    invalidates_sccp = false;
                }
                'u' => {
                    self.run_unused_elim();
                    invalidates_sccp = false;
                }
                'd' => self.run_defragment(),
                _ => unreachable!("should've been validated"),
            }

            if invalidates_sccp && let Some(sccp) = self.sccp.as_mut() {
                sccp.invalidate();
            }
        }
    }

    pub fn finish(self) -> EthIRProgram {
        self.src
    }

    fn run_sccp(&mut self) {
        let sccp = self.sccp.get_or_insert_with(|| WithAnalysis::new(SCCPAnalysis::new()));
        let uses = self.uses.get_or_insert_with(DefUse::new);
        {
            let sccp = sccp.get_ignoring_validity_mut();
            sccp.analysis(&self.src, uses);
            sccp.apply(&mut self.src);
        }
        sccp.validate();
    }

    fn run_copy_prop(&mut self) {
        let copy_prop = self.copy_prop.get_or_insert_with(CopyPropagation::new);
        copy_prop.run(&mut self.src);
    }

    fn run_unused_elim(&mut self) {
        let unused_elim = self.unused_elim.get_or_insert_with(UnusedOperationElimination::new);
        let uses = self.uses.get_or_insert_with(DefUse::new);
        unused_elim.run(&mut self.src, uses);
    }

    fn run_defragment(&mut self) {
        let dst = self.dst.get_or_insert_with(EthIRProgram::default);
        let defragmenter = self.defragmenter.get_or_insert_with(Defragmenter::new);
        defragmenter.run(
            &self.src,
            dst,
            self.sccp.as_ref().and_then(|sccp| sccp.get_valid()).map(|sccp| &sccp.reachable),
        );
        std::mem::swap(&mut self.src, dst);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sir_analyses::legalize;
    use sir_parser::{EmitConfig, parse_or_panic};
    use sir_test_utils::assert_trim_strings_eq_with_diff;

    fn optimize(source: &str, passes: &str) -> String {
        let program = parse_or_panic(source, EmitConfig::init_only());
        let mut optimizer = Optimizer::new(program);
        optimizer.run_passes(passes);
        let program = optimizer.finish();
        legalize(&program).expect("optimized IR should be legal");
        sir_data::display_program(&program)
    }

    const SWITCH_ON_COPY_WITH_DEAD_CODE: &str = r#"
        fn init:
            entry {
                x = const 1
                y = copy x
                switch y {
                    1 => @one
                    default => @other
                }
            }
            one {
                dead = const 42
                stop
            }
            other {
                cond = const 0
                => cond ? @other_yes : @one
            }
            other_yes { stop }
    "#;

    #[test]
    fn test_csud() {
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        => @1
    }

    @1 {
        stop
    }
        "#;

        let actual = optimize(SWITCH_ON_COPY_WITH_DEAD_CODE, "csud");
        assert_trim_strings_eq_with_diff(&actual, expected, "csud");
    }

    #[test]
    fn test_cusd() {
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        => @1
    }

    @1 {
        stop
    }
        "#;

        let actual = optimize(SWITCH_ON_COPY_WITH_DEAD_CODE, "cusd");
        assert_trim_strings_eq_with_diff(&actual, expected, "cusd");
    }

    #[test]
    fn test_ucsd() {
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        $1 = copy $0
        => @1
    }

    @1 {
        stop
    }
        "#;

        let actual = optimize(SWITCH_ON_COPY_WITH_DEAD_CODE, "ucsd");
        assert_trim_strings_eq_with_diff(&actual, expected, "ucsd");
    }

    #[test]
    fn test_uscd() {
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        $0 = const 0x1
        $1 = copy $0
        switch $0 {
            1 => @1,
            else => @2
        }

    }

    @1 {
        stop
    }

    @2 {
        $2 = const 0x0
        => @1
    }
        "#;

        let actual = optimize(SWITCH_ON_COPY_WITH_DEAD_CODE, "uscd");
        assert_trim_strings_eq_with_diff(&actual, expected, "uscd");
    }

    #[test]
    fn test_scsud() {
        let expected = r#"
Functions:
    fn @0 -> entry @0  (outputs: 0)

Basic Blocks:
    @0 {
        => @1
    }

    @1 {
        stop
    }
        "#;

        let actual = optimize(SWITCH_ON_COPY_WITH_DEAD_CODE, "scsud");
        assert_trim_strings_eq_with_diff(&actual, expected, "scsud");
    }
}
