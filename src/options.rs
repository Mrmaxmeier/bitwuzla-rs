use std::{ffi::CString, fmt};

use bitwuzla_sys::{
    bitwuzla_options_new,
    bitwuzla_set_option_mode,
    BITWUZLA_OPT_BV_SOLVER,
    BITWUZLA_OPT_PRODUCE_MODELS,
    BITWUZLA_OPT_TIME_LIMIT_PER,
};

use crate::option::*;

pub struct BitwuzlaOptions(*mut bitwuzla_sys::BitwuzlaOptions);
impl fmt::Debug for BitwuzlaOptions {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<bitwuzla_options {:?}>", self.0)
    }
}

impl BitwuzlaOptions {
    pub fn new() -> Self {
        Self(unsafe { bitwuzla_options_new() })
    }

    pub(crate) fn as_raw(&self) -> *mut bitwuzla_sys::BitwuzlaOptions {
        self.0
    }

    /// Set an option to a particular value.
    #[allow(clippy::cognitive_complexity)]
    pub fn set_opt(&self, opt: BtorOption) {
        use bitwuzla_sys::bitwuzla_set_option;
        match opt {
            BtorOption::ModelGen(mg) => {
                let val = match mg {
                    ModelGen::Disabled => 0,
                    ModelGen::Asserted => 1,
                    ModelGen::All => 2,
                };
                unsafe { bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PRODUCE_MODELS, val) }
            },
            BtorOption::SolverTimeout(duration) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_TIME_LIMIT_PER,
                    duration.map(|x| x.as_millis() as u64).unwrap_or(0),
                )
            },
            BtorOption::SolverEngine(se) => {
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
                    )
                }
            },
            BtorOption::SatEngine(se) => {
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
                    )
                }
            },
            BtorOption::Seed(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), bitwuzla_sys::BITWUZLA_OPT_SEED, u)
            },
            BtorOption::RewriteLevel(rl) => {
                let val = match rl {
                    RewriteLevel::None => 0,
                    RewriteLevel::TermLevel => 1,
                    RewriteLevel::More => 2,
                    RewriteLevel::Full => 3,
                };
                unsafe {
                    bitwuzla_set_option(
                        self.as_raw(),
                        bitwuzla_sys::BITWUZLA_OPT_REWRITE_LEVEL,
                        val,
                    )
                }
            },
        }
    }
}
