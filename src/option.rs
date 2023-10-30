//! This module exposes options which can be set on a `Btor` instance.

/// Documentation for individual options and their possible values are
/// more-or-less taken verbatim from the bitwuzla 3.0.0 docs.
pub enum BtorOption {
    /// Whether to generate a model (set of concrete solution values) for
    /// satisfiable instances
    ModelGen(ModelGen),
    /// Solver timeout. If `Some`, then operations lasting longer than the given
    /// `Duration` will be aborted and return `SolverResult::Unknown`.
    ///
    /// If `None`, then any previously set solver timeout will be removed, and
    /// there will be no time limit to solver operations.
    SolverTimeout(Option<std::time::Duration>),
    /// Solver engine. The default is `SolverEngine::Fun`.
    SolverEngine(SolverEngine),
    /// SAT solver. Each option requires that bitwuzla was compiled with support
    /// for the corresponding solver.
    SatEngine(SatEngine),
    /// Seed for bitwuzla's internal random number generator. The default is 0.
    Seed(u64),
    /// Rewrite level. The default is `RewriteLevel::Full`.
    ///
    /// bitwuzla's docs say to not change this setting after creating expressions.
    RewriteLevel(RewriteLevel),
}

pub enum ModelGen {
    /// Do not generate models
    Disabled,
    /// Generate models for asserted expressions only
    Asserted,
    /// Generate models for all expressions
    All,
}

pub enum IncrementalSMT1 {
    /// Stop after first satisfiable formula
    Basic,
    /// Solve all formulas
    Continue,
}

pub enum NumberFormat {
    Binary,
    Decimal,
    Hexadecimal,
}

pub enum OutputFileFormat {
    BTOR,
    SMTLIBv2,
    AigerASCII,
    AigerBinary,
}

pub enum SolverEngine {
    /// Default engine for all combinations of QF_AUFBV; uses lemmas on demand
    /// for QF_AUFBV and eager bit-blasting for QF_BV
    Fun,
    /// Score-based local search QF_BV engine
    SLS,
    /// Propagation-based local search QF_BV engine
    Prop,
    /// Propagation-based local search QF_BV engine that operates on the bit-blasted formula (the AIG layer)
    AIGProp,
    /// Quantifier engine (BV only)
    Quant,
}

pub enum SatEngine {
    /// CaDiCaL
    CaDiCaL,
    /// CryptoMiniSat
    CMS,
    /// Gimsatul
    Gimsatul,
    /// Kissat
    Kissat,
    /// Lingeling
    Lingeling,
    /// MiniSAT
    MiniSAT,
    /// PicoSAT
    PicoSAT,
}

pub enum RewriteLevel {
    /// "no rewriting"
    None,
    /// "term level rewriting"
    TermLevel,
    /// "more simplification techniques"
    More,
    /// "full rewriting/simplification"
    Full,
}

pub enum DualPropQsortOrder {
    /// Order by score, highest score first
    Just,
    /// Order by input id, ascending
    Asc,
    /// Order by input id, descending
    Desc,
}

pub enum JustificationHeuristic {
    /// Always choose the left branch
    Left,
    /// Choose the branch with the minimum number of applies
    MinApp,
    /// Choose the branch with the minimum depth
    MinDepth,
}

pub enum EagerLemmas {
    /// Do not generate lemmas eagerly (generate one single lemma per refinement
    /// iteration)
    None,
    /// Only generate lemmas eagerly until the first conflict dependent on
    /// another conflict is found
    Conf,
    /// In each refinement iterations, generate lemmas for all conflicts
    All,
}

pub enum SLSMoveStrategy {
    /// Always choose the best score improving move
    BestMove,
    /// Perform a random walk weighted by score
    RandomWalk,
    /// Always choose the first best move, even if another move may be better
    FirstBestMove,
    /// Choose a move even if its score is not better but the same as the score
    /// of the previous best move
    BestSameMove,
    /// Always choose propagation move, and recover with SLS move in case of
    /// conflict
    AlwaysProp,
}

pub enum PropPathSelection {
    /// Select path based on controlling inputs
    Controlling,
    /// Select path based on essential inputs
    Essential,
    /// Select path based on random inputs
    Random,
}

pub enum AIGPropQuantSynthesis {
    /// Do not synthesize skolem functions (use model values for instantiation)
    None,
    /// Use enumerative learning to synthesize skolem functions
    EL,
    /// Use enumerative learning modulo the predicates in the cone of influence
    /// of the existential variables to synthesize skolem functions
    ELMC,
    /// Chain the `EL` and `ELMC` approaches to synthesize skolem functions
    ELELMC,
    /// Use enumerative learning modulo the given root constraints to synthesize
    /// skolem functions
    ELMR,
}