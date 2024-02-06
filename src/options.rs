use std::{ffi::CString, fmt, time::Duration};

use bitwuzla_sys::{
    bitwuzla_options_delete,
    bitwuzla_options_new,
    bitwuzla_set_option,
    bitwuzla_set_option_mode,
    BITWUZLA_OPT_PRODUCE_MODELS,
    BITWUZLA_OPT_TIME_LIMIT_PER, BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS,
};

use crate::option::*;

pub struct BitwuzlaOptions(*mut bitwuzla_sys::BitwuzlaOptions);

impl BitwuzlaOptions {
    pub fn new() -> Self {
        Self(unsafe { bitwuzla_options_new() })
    }

    pub fn build(self) -> crate::Bitwuzla {
        crate::Bitwuzla::new_from_options(self)
    }

    pub(crate) fn as_raw(&mut self) -> *mut bitwuzla_sys::BitwuzlaOptions {
        self.0
    }

    pub fn with_model_gen(self) -> Self {
        self.model_gen(ModelGen::All)
    }

    /// Whether to generate a model (set of concrete solution values) for
    /// satisfiable instances
    pub fn model_gen(mut self, mg: ModelGen) -> Self {
        let val = match mg {
            ModelGen::Disabled => 0,
            ModelGen::Asserted => 1,
            ModelGen::All => 2,
        };
        unsafe { bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PRODUCE_MODELS, val) };
        self
    }

    /// Solver timeout. If `Some`, then operations lasting longer than the given
    /// `Duration` will be aborted and return `SolverResult::Unknown`.
    ///
    /// If `None`, then any previously set solver timeout will be removed, and
    /// there will be no time limit to solver operations.
    pub fn solver_timeout(mut self, duration: Option<Duration>) -> Self {
        unsafe {
            bitwuzla_set_option(
                self.as_raw(),
                BITWUZLA_OPT_TIME_LIMIT_PER,
                duration.map(|x| x.as_millis() as u64).unwrap_or(0),
            )
        };
        self
    }

    /// Solver engine. The default is `SolverEngine::Fun`.
    pub fn solver_engine(mut self, se: SolverEngine) -> Self {
        let val = match se {
            SolverEngine::Fun => "fun",
            SolverEngine::SLS => "sls",
            SolverEngine::Prop => "prop",
            SolverEngine::AIGProp => "aigprop",
            SolverEngine::Quant => "quant",
        };
        let val = CString::new(val).unwrap();
        unsafe {
            bitwuzla_set_option_mode(
                self.as_raw(),
                bitwuzla_sys::BITWUZLA_OPT_BV_SOLVER,
                val.as_ptr(),
            );
        }
        self
    }

    /// SAT solver. Each option requires that bitwuzla was compiled with support
    /// for the corresponding solver.
    pub fn sat_engine(mut self, se: SatEngine) -> Self {
        let val = match se {
            SatEngine::CaDiCaL => "cadical",
            SatEngine::CMS => "cms",
            SatEngine::Gimsatul => "gimsatul",
            SatEngine::Kissat => "kissat",
            SatEngine::Lingeling => "lingeling",
            SatEngine::MiniSAT => "minisat",
            SatEngine::PicoSAT => "picosat",
        };
        let target_engine = CString::new(val).unwrap();
        unsafe {
            bitwuzla_set_option_mode(
                self.as_raw(),
                bitwuzla_sys::BITWUZLA_OPT_SAT_SOLVER,
                target_engine.as_ptr(),
            );
        }
        self
    }

    /// Seed for bitwuzla's internal random number generator. The default is 0.
    pub fn seed(mut self, seed: u64) -> Self {
        unsafe {
            bitwuzla_set_option(self.as_raw(), bitwuzla_sys::BITWUZLA_OPT_SEED, seed);
        }
        self
    }

    /// Rewrite level. The default is `RewriteLevel::Full`.
    ///
    /// bitwuzla's docs say to not change this setting after creating expressions.
    pub fn rewrite_level(mut self, rl: RewriteLevel) -> Self {
        let val = match rl {
            RewriteLevel::None => 0,
            RewriteLevel::TermLevel => 1,
            RewriteLevel::More => 2,
            RewriteLevel::Full => 3,
        };
        unsafe {
            bitwuzla_set_option(self.as_raw(), bitwuzla_sys::BITWUZLA_OPT_REWRITE_LEVEL, val)
        };
        self
    }

    pub fn produce_unsat_assumptions(mut self, v: bool) -> Self {
        unsafe {
            bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PRODUCE_UNSAT_ASSUMPTIONS, v as u64);
        }
        self
    }
}

impl Drop for BitwuzlaOptions {
    fn drop(&mut self) {
        unsafe {
            bitwuzla_options_delete(self.as_raw());
        }
    }
}
