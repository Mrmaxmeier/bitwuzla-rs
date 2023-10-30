use crate::option::BtorOption;
use crate::option::*;
use crate::timeout::{self, TimeoutState};
use crate::{Array, BV};
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::{c_char, c_void};
use std::pin::Pin;

/// A `Btor` represents an instance of the bitwuzla solver.
/// Each `BV` and `Array` is created in a particular `Btor` instance.
pub struct Bitwuzla {
    options: crate::BitwuzlaOptions,
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

// https://github.com/bitwuzla/bitwuzla/issues/86
// unsafe impl Send for Bitwuzla {}
// unsafe impl Sync for Bitwuzla {}

impl Bitwuzla {
    /// Create a new `Bitwuzla` instance with no variables and no constraints.
    pub fn new() -> Self {
        Self::new_from_options(crate::BitwuzlaOptions::new())
    }

    /// Create a new `Bitwuzla` instance with no variables and no constraints.
    pub fn new_from_options(options: crate::BitwuzlaOptions) -> Self {
        Self {
            btor: unsafe { bitwuzla_new(options.as_raw()) },
            timeout_state: Pin::new(Box::new(timeout::TimeoutState::new())),
            options,
        }
    }

    pub fn set_opt(&self, opt: BtorOption) {
        self.options.set_opt(opt);
    }

    pub(crate) fn as_raw(&self) -> *mut bitwuzla_sys::Bitwuzla {
        self.btor
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
        let result = unsafe { bitwuzla_check_sat(self.as_raw()) };
        SolverResult::from_raw(result)
    }

    pub fn check_sat_assuming<R: Borrow<Bitwuzla> + Clone>(&self, assumptions: &[crate::Bool<R>]) -> SolverResult {
        self.timeout_state.restart_timer();
        let assumptions = assumptions.iter().map(|x| x.node).collect::<Vec<_>>();
        let result = unsafe { bitwuzla_check_sat_assuming(self.as_raw(), assumptions.len() as u32, assumptions.as_ptr() as *mut _) };
        SolverResult::from_raw(result)
    }

    /// Push `n` context levels. `n` must be at least 1.
    pub fn push(&self, n: u64) {
        unsafe { bitwuzla_push(self.as_raw(), n) }
    }

    /// Pop `n` context levels. `n` must be at least 1.
    pub fn pop(&self, n: u64) {
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
        todo!()
        // unsafe { bitwuzla_fixate_assumptions(self.as_raw()) }
    }

    /// Remove all added assumptions
    pub fn reset_assumptions(&self) {
        todo!()
        // unsafe { bitwuzla_reset_assumptions(self.as_raw()) }
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
        let format = CString::new("smt2").unwrap();
        crate::util::tmp_file_to_string(
            |tmpfile| unsafe {
                bitwuzla_print_formula(self.as_raw(), format.as_ptr(), tmpfile, 10);
            },
            false,
        )
    }

    /// Get a `String` describing the current model, including a set of
    /// satisfying assignments for all variables
    pub fn print_model(&self) -> String {
        /*
        let format_cstring = CString::new("btor").unwrap();
        crate::util::tmp_file_to_string(
            |tmpfile| unsafe {
                bitwuzla_print_model(
                    self.as_raw(),
                    format_cstring.as_ptr() as *mut c_char,
                    tmpfile,
                );
            },
            false,
        )
         */
        todo!()
    }

    /// Get bitwuzla's version string
    pub fn get_version(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(bitwuzla_version()) };
        cstr.to_str().unwrap().to_owned()
    }

    /// Get bitwuzla's copyright notice
    pub fn get_copyright(&self) -> String {
        let cstr = unsafe { CStr::from_ptr(bitwuzla_copyright()) };
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
    Sat = BITWUZLA_SAT as isize,
    Unsat = BITWUZLA_UNSAT as isize,
    Unknown = BITWUZLA_UNKNOWN as isize,
}

impl SolverResult {
    fn from_raw(result: bitwuzla_sys::BitwuzlaResult) -> Self {
        match result {
            BITWUZLA_SAT => SolverResult::Sat,
            BITWUZLA_UNSAT => SolverResult::Unsat,
            BITWUZLA_UNKNOWN => SolverResult::Unknown,
            _ => unreachable!(),
        }
    }

    pub fn to_string(&self) -> String {
        let cstr = unsafe {
            CStr::from_ptr(bitwuzla_sys::bitwuzla_result_to_string(*self as u32))
        };
        cstr.to_str().unwrap().to_owned()
    }
}
