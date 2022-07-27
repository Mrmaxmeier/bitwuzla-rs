use crate::node::{Array, BV};
use crate::option::BtorOption;
use crate::option::*;
use crate::timeout::{self, TimeoutState};
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::{c_char, c_void};
use std::pin::Pin;

/// A `Btor` represents an instance of the bitwuzla solver.
/// Each `BV` and `Array` is created in a particular `Btor` instance.
pub struct Bitwuzla {
    btor: *mut bitwuzla_sys::Bitwuzla,
    pub(crate) timeout_state: Pin<Box<timeout::TimeoutState>>, // needs to be `Pin`, because the bitwuzla callback will expect to continue to find the `TimeoutState` at the same location
}
pub type Btor = Bitwuzla;

// Two `Btor`s are equal if they have the same underlying Btor pointer.
// We disregard the `timeout_state` for this purpose.
impl PartialEq for Bitwuzla {
    fn eq(&self, other: &Self) -> bool {
        self.btor == other.btor
    }
}

impl Eq for Bitwuzla {}

impl fmt::Debug for Bitwuzla {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<bitwuzla {:?}>", self.btor)
    }
}

/// According to
/// https://groups.google.com/forum/#!msg/bitwuzla/itYGgJxU3mY/AC2O0898BAAJ,
/// the boolector library is thread-safe, so we make `Bitwuzla` both `Send` and
/// `Sync`. (Note that `TimeoutState` is also careful to be both `Send` and
/// `Sync`.)
unsafe impl Send for Bitwuzla {}
unsafe impl Sync for Bitwuzla {}

impl Bitwuzla {
    /// Create a new `Bitwuzla` instance with no variables and no constraints.
    pub fn new() -> Self {
        Self {
            btor: unsafe { bitwuzla_new() },
            timeout_state: Pin::new(Box::new(timeout::TimeoutState::new())),
        }
    }

    pub(crate) fn as_raw(&self) -> *mut bitwuzla_sys::Bitwuzla {
        self.btor
    }

    /// Set an option to a particular value.
    #[allow(clippy::cognitive_complexity)]
    pub fn set_opt(&self, opt: BtorOption) {
        match opt {
            BtorOption::ModelGen(mg) => {
                let val = match mg {
                    ModelGen::Disabled => 0,
                    ModelGen::Asserted => 1,
                    ModelGen::All => 2,
                };
                unsafe { bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PRODUCE_MODELS, val) }
            },
            BtorOption::Incremental(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_INCREMENTAL,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::InputFileFormat(iff) => {
                let val = match iff {
                    InputFileFormat::Autodetect => "none",
                    InputFileFormat::Btor => "btor",
                    InputFileFormat::Btor2 => "btor2",
                    InputFileFormat::SMTLIBv1 => "smt1",
                    InputFileFormat::SMTLIBv2 => "smt2",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(self.as_raw(), BITWUZLA_OPT_INPUT_FORMAT, val.as_ptr())
                }
            },
            BtorOption::OutputNumberFormat(nf) => {
                let val = match nf {
                    NumberFormat::Binary => "bin",
                    NumberFormat::Decimal => "dec",
                    NumberFormat::Hexadecimal => "hex",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT,
                        val.as_ptr(),
                    )
                }
            },
            BtorOption::OutputFileFormat(off) => {
                let val = match off {
                    OutputFileFormat::BTOR => "btor",
                    OutputFileFormat::SMTLIBv2 => "smt2",
                    OutputFileFormat::AigerASCII => "aiger",
                    OutputFileFormat::AigerBinary => "aigerbin",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(self.as_raw(), BITWUZLA_OPT_OUTPUT_FORMAT, val.as_ptr())
                }
            },
            BtorOption::SolverTimeout(duration) => {
                self.timeout_state.set_timeout_duration(duration);
                match duration {
                    None => {
                        // remove any existing timeout
                        unsafe {
                            bitwuzla_set_termination_callback(
                                self.as_raw(),
                                None,
                                std::ptr::null_mut(),
                            )
                        }
                    },
                    Some(_) => {
                        let ptr_to_ts: Pin<&TimeoutState> = (&self.timeout_state).as_ref();
                        let raw_ptr_to_ts: *const TimeoutState =
                            Pin::into_inner(ptr_to_ts) as *const TimeoutState;
                        let void_ptr_to_ts: *mut c_void = raw_ptr_to_ts as *mut c_void;
                        unsafe {
                            bitwuzla_set_termination_callback(
                                self.as_raw(),
                                Some(timeout::callback),
                                void_ptr_to_ts,
                            )
                        }
                    },
                }
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
                unsafe { bitwuzla_set_option_str(self.as_raw(), BITWUZLA_OPT_ENGINE, val.as_ptr()) }
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
                    bitwuzla_set_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_SAT_ENGINE,
                        target_engine.as_ptr(),
                    )
                }
                let engine = unsafe {
                    CStr::from_ptr(bitwuzla_get_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_SAT_ENGINE,
                    ))
                };
                assert_eq!(engine, target_engine.as_c_str());
            },
            BtorOption::PrettyPrint(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PRETTY_PRINT,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::Seed(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SEED, u)
            },
            BtorOption::RewriteLevel(rl) => {
                let val = match rl {
                    RewriteLevel::None => 0,
                    RewriteLevel::TermLevel => 1,
                    RewriteLevel::More => 2,
                    RewriteLevel::Full => 3,
                };
                unsafe { bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_RW_LEVEL, val) }
            },
            BtorOption::SkeletonPreproc(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_SKELETON_PREPROC,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::Ackermann(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_ACKERMANN,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::BetaReduce(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_BETA_REDUCE,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::VariableSubst(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_VAR_SUBST,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::UnconstrainedOpt(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_UNCONSTRAINED_OPTIMIZATION,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::MergeLambdas(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_MERGE_LAMBDAS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::ExtractLambdas(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PP_EXTRACT_LAMBDAS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::Normalize(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_RW_NORMALIZE,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::NormalizeAdd(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_RW_NORMALIZE_ADD,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::FunPreProp(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_FUN_PREPROP,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::FunPreSLS(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_FUN_PRESLS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::FunDualProp(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_FUN_DUAL_PROP,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::FunDualPropQsortOrder(dpqo) => {
                let val = match dpqo {
                    DualPropQsortOrder::Just => "just",
                    DualPropQsortOrder::Asc => "asc",
                    DualPropQsortOrder::Desc => "desc",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_FUN_DUAL_PROP_QSORT,
                        val.as_ptr(),
                    )
                }
            },
            BtorOption::FunJustification(b) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_FUN_JUST, if b { 1 } else { 0 })
            },
            BtorOption::FunJustificationHeuristic(jh) => {
                let val = match jh {
                    JustificationHeuristic::Left => "left",
                    JustificationHeuristic::MinApp => "applies",
                    JustificationHeuristic::MinDepth => "depth",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_FUN_JUST_HEURISTIC,
                        val.as_ptr(),
                    )
                }
            },
            BtorOption::FunLazySynthesize(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_FUN_LAZY_SYNTHESIZE,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::FunEagerLemmas(el) => {
                let val = match el {
                    EagerLemmas::None => "none",
                    EagerLemmas::Conf => "conf",
                    EagerLemmas::All => "all",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(
                        self.as_raw(),
                        BITWUZLA_OPT_FUN_EAGER_LEMMAS,
                        val.as_ptr(),
                    )
                }
            },
            BtorOption::SLSNumFlips(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_NFLIPS, u)
            },
            BtorOption::SLSMoveStrategy(sms) => {
                let val = match sms {
                    SLSMoveStrategy::BestMove => 0,
                    SLSMoveStrategy::RandomWalk => 1,
                    SLSMoveStrategy::FirstBestMove => 2,
                    SLSMoveStrategy::BestSameMove => 3,
                    SLSMoveStrategy::AlwaysProp => 4,
                };
                unsafe { bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_STRATEGY, val) }
            },
            BtorOption::SLSJustification(b) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_JUST, if b { 1 } else { 0 })
            },
            BtorOption::SLSGroupWiseMoves(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_GW,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSRangeWiseMoves(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_RANGE,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSSegmentWiseMoves(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_SEGMENT,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSRandomWalkMoves(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_RAND_WALK,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSRandomWalkProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_PROB_MOVE_RAND_WALK, u)
            },
            BtorOption::SLSRandomizeAll(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_RAND_ALL,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSRandomizeRange(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_RAND_RANGE,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSPropagationMoves(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_PROP,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSPropagationMovesNumProp(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_MOVE_PROP_NPROPS, u)
            },
            BtorOption::SLSPropagationMovesNumRegular(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_SLS_MOVE_PROP_NSLSS, u)
            },
            BtorOption::SLSForceRandomWalks(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_PROP_FORCE_RW,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSIncMoveTest(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_MOVE_INC_MOVE_TEST,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSRestarts(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_USE_RESTARTS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::SLSBanditScheme(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_SLS_USE_BANDIT,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::PropNumSteps(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_NPROPS, u)
            },
            BtorOption::PropRestarts(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PROP_USE_RESTARTS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::PropBanditScheme(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_PROP_USE_BANDIT,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::PropPathSelectionMode(pathsel) => {
                let val = match pathsel {
                    PropPathSelection::Controlling => unimplemented!(),
                    PropPathSelection::Essential => "essential",
                    PropPathSelection::Random => "random",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(self.as_raw(), BITWUZLA_OPT_PROP_PATH_SEL, val.as_ptr())
                }
            },
            BtorOption::PropInvValueProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_USE_INV_VALUE, u)
            },
            BtorOption::PropFlipConditionProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_FLIP_COND, u)
            },
            BtorOption::PropFlipConditionProbabilityConstant(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_FLIP_COND_CONST, u)
            },
            BtorOption::PropFlipConditionNumPaths(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_FLIP_COND_CONST_NPATHSEL, u)
            },
            BtorOption::PropFlipConditionProbabilityConstantDelta(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_FLIP_COND_CONST_DELTA, u)
            },
            BtorOption::PropSliceKeepDCProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_SLICE_KEEP_DC, u)
            },
            BtorOption::PropSliceFlipProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_SLICE_FLIP, u)
            },
            BtorOption::PropEqFlipProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_EQ_FLIP, u)
            },
            BtorOption::PropAndFlipProbability(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_PROP_PROB_AND_FLIP, u)
            },
            BtorOption::AIGPropUseRestarts(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_AIGPROP_USE_RESTARTS,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::AIGPropQuantSynthesis(pqs) => {
                let val = match pqs {
                    AIGPropQuantSynthesis::None => "none",
                    AIGPropQuantSynthesis::EL => "el",
                    AIGPropQuantSynthesis::ELMC => "elmc",
                    AIGPropQuantSynthesis::ELELMC => "elelmc",
                    AIGPropQuantSynthesis::ELMR => "elmr",
                };
                let val = CString::new(val).unwrap();
                unsafe {
                    bitwuzla_set_option_str(self.as_raw(), BITWUZLA_OPT_QUANT_SYNTH, val.as_ptr())
                }
            },
            BtorOption::AIGPropQuantDualSolver(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_QUANT_DUAL_SOLVER,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::AIGPropQuantSynthLimit(u) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_QUANT_SYNTH_LIMIT, u)
            },
            BtorOption::AIGPropSynthQI(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_QUANT_SYNTH_QI,
                    if b { 1 } else { 0 },
                )
            },
            BtorOption::AIGPropQuantDER(b) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_QUANT_DER, if b { 1 } else { 0 })
            },
            BtorOption::AIGPropQuantCER(b) => unsafe {
                bitwuzla_set_option(self.as_raw(), BITWUZLA_OPT_QUANT_CER, if b { 1 } else { 0 })
            },
            BtorOption::AIGPropQuantMiniscope(b) => unsafe {
                bitwuzla_set_option(
                    self.as_raw(),
                    BITWUZLA_OPT_QUANT_MINISCOPE,
                    if b { 1 } else { 0 },
                )
            },
            _ => panic!("unsupported option"),
        }
    }

    /// Solve the current input (defined by the constraints which have been added
    /// via [`BV::assert()`](struct.BV.html#method.assert) and
    /// [`BV::assume()`](struct.BV.html#method.assume)). All assertions and
    /// assumptions are implicitly combined via Boolean `and`.
    ///
    /// Calling this function multiple times requires incremental usage to be
    /// enabled via [`Btor::set_opt()`](struct.Btor.html#method.set_opt).
    /// If incremental usage is not enabled, this function may only be called
    /// once.
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::Incremental(true));
    ///
    /// // An 8-bit unconstrained `BV` with the symbol "foo"
    /// let foo = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // Assert that "foo" must be greater than `3`
    /// foo.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // This state is satisfiable
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    ///
    /// // Assert that "foo" must also be less than `2`
    /// foo.ult(&BV::from_u32(btor.clone(), 2, 8)).assert();
    ///
    /// // State is now unsatisfiable
    /// assert_eq!(btor.sat(), SolverResult::Unsat);
    ///
    /// // Repeat the first step above with the solver timeout set to something
    /// // extremely high (say, 200 sec) - should still be `Sat`
    /// # use std::time::Duration;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::Incremental(true));
    /// btor.set_opt(BtorOption::SolverTimeout(Some(Duration::from_secs(200))));
    /// let foo = BV::new(btor.clone(), 8, Some("foo"));
    /// foo.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    ///
    /// // But, if we make the second assertion and then set the solver timeout to
    /// // something extremely low (say, 2 ns), we'll get `SolverResult::Unknown`
    /// foo.ugt(&BV::from_u32(btor.clone(), 5, 8)).assert();
    /// btor.set_opt(BtorOption::SolverTimeout(Some(Duration::from_nanos(2))));
    /// assert_eq!(btor.sat(), SolverResult::Unknown);
    /// ```
    pub fn sat(&self) -> SolverResult {
        self.timeout_state.restart_timer();
        match unsafe { bitwuzla_check_sat(self.as_raw()) } {
            BITWUZLA_SAT => SolverResult::Sat,
            BITWUZLA_UNSAT => SolverResult::Unsat,
            BITWUZLA_UNKNOWN => SolverResult::Unknown,
            _ => unreachable!(),
        }
    }

    /// Push `n` context levels. `n` must be at least 1.
    pub fn push(&self, n: u32) {
        unsafe { bitwuzla_push(self.as_raw(), n) }
    }

    /// Pop `n` context levels. `n` must be at least 1.
    pub fn pop(&self, n: u32) {
        unsafe { bitwuzla_pop(self.as_raw(), n) }
    }

    /// Given a `BV` originally created for any `Btor`, get the corresponding
    /// `BV` in the given `btor`. This only works if the `BV` was created before
    /// the relevant `Btor::duplicate()` was called; that is, it is intended to
    /// be used to find the copied version of a given `BV` in the new `Btor`.
    ///
    /// It's also fine to call this with a `BV` created for the given `Btor`
    /// itself, in which case you'll just get back `Some(bv.clone())`.
    ///
    /// For a code example, see
    /// [`Btor::duplicate()`](struct.Btor.html#method.duplicate).
    #[allow(clippy::if_same_then_else)]
    pub fn get_matching_bv<R: Borrow<Bitwuzla> + Clone>(_btor: R, _bv: &BV<R>) -> Option<BV<R>> {
        unimplemented!()
        /*
        let node = unsafe { bitwuzla_match_node(btor.borrow().as_raw(), bv.node) };
        if node.is_null() {
            None
        } else if unsafe { bitwuzla_is_array(btor.borrow().as_raw(), node) } {
            None
        } else {
            Some(BV { btor, node })
        }
        */
    }

    /// Given an `Array` originally created for any `Btor`, get the corresponding
    /// `Array` in the given `btor`. This only works if the `Array` was created
    /// before the relevant `Btor::duplicate()` was called; that is, it is
    /// intended to be used to find the copied version of a given `Array` in the
    /// new `Btor`.
    ///
    /// It's also fine to call this with an `Array` created for the given `Btor`
    /// itself, in which case you'll just get back `Some(array.clone())`.
    pub fn get_matching_array<R: Borrow<Bitwuzla> + Clone>(
        _btor: R,
        _array: &Array<R>,
    ) -> Option<Array<R>> {
        unimplemented!()
        /*
        let node = unsafe { bitwuzla_match_node(btor.borrow().as_raw(), array.node) };
        if node.is_null() {
            None
        } else if unsafe { bitwuzla_is_array(btor.borrow().as_raw(), node) } {
            Some(Array { btor, node })
        } else {
            None
        }
        */
    }

    /// Given a symbol, find the `BV` in the given `Btor` which has that symbol.
    ///
    /// Since `Btor::duplicate()` copies all `BV`s to the new `Btor` including
    /// their symbols, this can also be used to find the copied version of a
    /// given `BV` in the new `Btor`.
    #[allow(clippy::if_same_then_else)]
    pub fn get_bv_by_symbol<R: Borrow<Bitwuzla> + Clone>(_btor: R, _symbol: &str) -> Option<BV<R>> {
        unimplemented!()
        /*
        let cstring = CString::new(symbol).unwrap();
        let symbol = cstring.as_ptr() as *const c_char;
        let node = unsafe { bitwuzla_match_node_by_symbol(btor.borrow().as_raw(), symbol) };
        if node.is_null() {
            None
        } else if unsafe { bitwuzla_is_array(btor.borrow().as_raw(), node) } {
            None
        } else {
            Some(BV { btor, node })
        }
        */
    }

    /// Given a symbol, find the `Array` in the given `Btor` which has that
    /// symbol.
    ///
    /// Since `Btor::duplicate()` copies all `Array`s to the new `Btor` including
    /// their symbols, this can also be used to find the copied version of a
    /// given `Array` in the new `Btor`.
    pub fn get_array_by_symbol<R: Borrow<Bitwuzla> + Clone>(
        _btor: R,
        _symbol: &str,
    ) -> Option<Array<R>> {
        unimplemented!()
        /*
        let cstring = CString::new(symbol).unwrap();
        let symbol = cstring.as_ptr() as *const c_char;
        let node = unsafe { bitwuzla_match_node_by_symbol(btor.borrow().as_raw(), symbol) };
        if node.is_null() {
            None
        } else if unsafe { bitwuzla_is_array(btor.borrow().as_raw(), node) } {
            Some(Array { btor, node })
        } else {
            None
        }
        */
    }

    /// Add all current assumptions as assertions
    pub fn fixate_assumptions(&self) {
        unsafe { bitwuzla_fixate_assumptions(self.as_raw()) }
    }

    /// Remove all added assumptions
    pub fn reset_assumptions(&self) {
        unsafe { bitwuzla_reset_assumptions(self.as_raw()) }
    }

    /// Reset all statistics other than time statistics
    pub fn reset_stats(&self) {
        todo!()
        // unsafe { bitwuzla_reset_stats(self.as_raw()) }
    }

    /// Reset time statistics
    pub fn reset_time(&self) {
        // No-op. Time is reset when solving anyways?
        // todo!()
        // unsafe { bitwuzla_reset_time(self.as_raw()) }
    }

    /// Get a `String` describing the current constraints
    pub fn print_constraints(&self) -> String {
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            let format = CString::new("smt2").unwrap();
            // Write the data to `tmpfile`
            bitwuzla_dump_formula(self.as_raw(), format.as_ptr(), tmpfile);
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let mut buffer = Vec::with_capacity(length as usize);
            libc::fread(
                buffer.as_mut_ptr() as *mut c_void,
                1,
                length as usize,
                tmpfile,
            );
            libc::fclose(tmpfile);
            buffer.set_len(length as usize);
            String::from_utf8_unchecked(buffer)
        }
    }

    /// Get a `String` describing the current model, including a set of
    /// satisfying assignments for all variables
    pub fn print_model(&self) -> String {
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            // Write the data to `tmpfile`
            let format_cstring = CString::new("btor").unwrap();
            bitwuzla_print_model(
                self.as_raw(),
                format_cstring.as_ptr() as *mut c_char,
                tmpfile,
            );
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let mut buffer = Vec::with_capacity(length as usize);
            libc::fread(
                buffer.as_mut_ptr() as *mut c_void,
                1,
                length as usize,
                tmpfile,
            );
            libc::fclose(tmpfile);
            buffer.set_len(length as usize);
            String::from_utf8_unchecked(buffer)
        }
    }

    /// Get bitwuzla's version string
    pub fn get_version(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(bitwuzla_version(self.as_raw())) };
        cstr.to_str().unwrap().to_owned()
    }

    /// Get bitwuzla's copyright notice
    pub fn get_copyright(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(bitwuzla_copyright(self.as_raw())) };
        cstr.to_str().unwrap().to_owned()
    }
}

impl Default for Bitwuzla {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Bitwuzla {
    fn drop(&mut self) {
        unsafe {
            bitwuzla_delete(self.as_raw());
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}
