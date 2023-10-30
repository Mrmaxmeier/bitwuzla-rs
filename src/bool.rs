use crate::btor::Bitwuzla;
use crate::sort::Sort;
use crate::{Array, BV, FP};
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::c_char;

/// A boolean object: that is, a single symbolic value usually originating from a comparison.
///
/// This is generic in the `Bitwuzla` reference type.
#[derive(PartialEq, Eq)]
pub struct Bool<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: BitwuzlaTerm,
}

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! unop {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self) -> Self {
            Self {
                btor: self.btor.clone(),
                node: unsafe { bitwuzla_mk_term1($kind, self.node) },
            }
        }
    };
}

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! binop {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self, other: &Self) -> Self {
            Self {
                btor: self.btor.clone(),
                node:  unsafe { bitwuzla_mk_term2($kind, self.node, other.node) },
            }
        }
    };
}

impl<R: Borrow<Bitwuzla> + Clone> Bool<R> {
    /// Create a new unconstrained `Bool` variable.
    ///
    /// The `symbol`, if present, will be used to identify the `BV` when printing
    /// a model or dumping to file. It must be unique if it is present.
    pub fn new(btor: R, symbol: Option<&str>) -> Self {
        let sort = Sort::bool(btor.clone());
        let node = match symbol {
            None => unsafe {
                bitwuzla_mk_const(sort.as_raw(), std::ptr::null())
            },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_mk_const(sort.as_raw(), symbol) }
            },
        };
        Self { btor, node }
    }

    /// Create a new constant `BV` representing the given `bool` (either constant
    /// `true` or constant `false`).
    pub fn from_bool(btor: R, b: bool) -> Self {
        let node = if b {
            unsafe { bitwuzla_mk_true() }
        } else {
            unsafe { bitwuzla_mk_false() }
        };
        Self { btor, node }
    }

    /// Create a one-bit-wide bitvector from this boolean.
    pub fn to_bv(&self) -> BV<R> {
        // TODO: there should be/is a better way!
        self.cond_bv(&BV::from_bool(self.btor.clone(), true), &BV::from_bool(self.btor.clone(), false))
    }

    pub fn uext(&self, n: u64) -> BV<R> {
        self.to_bv().uext(n)
    }

    /// Get a solution for the `BV` according to the current model.
    ///
    /// This requires that model generation is enabled (see
    /// [`Btor::set_opt`](struct.Btor.html#method.set_opt)), and that the most
    /// recent call to [`Btor::sat()`](struct.Btor.html#method.sat) returned
    /// `SolverResult::Sat`.
    ///
    /// Calling this multiple times on the same `BV` or different arbitrary `BV`s
    /// (for the same `Btor` instance) will produce a consistent set of solutions
    /// as long as the `Btor`'s state is not otherwise changed. That is, this
    /// queries an underlying model which won't change unless the `Btor` state
    /// changes.
    ///
    /// For a code example, see [`BV::new()`](struct.BV.html#method.new).
    pub fn get_a_solution(&self) -> bool {
        let bv_val = unsafe {
            bitwuzla_get_value(self.btor.borrow().as_raw(), self.node)
        };
        unsafe {
            bitwuzla_term_value_get_bool(bv_val)
        }
    }

    /// Get the `Btor` which this `BV` belongs to
    pub fn get_btor(&self) -> R {
        self.btor.clone()
    }

    /// Get the id of the `BV`
    pub fn get_id(&self) -> i32 {
        todo!()
        // unsafe { bitwuzla_get_node_id(self.node) }
    }

    /// Get the symbol of the `BV`, if one was assigned
    pub fn get_symbol(&self) -> Option<&str> {
        let raw = unsafe { bitwuzla_term_get_symbol(self.node) };
        if raw.is_null() {
            None
        } else {
            let cstr = unsafe { CStr::from_ptr(raw) };
            Some(cstr.to_str().unwrap())
        }
    }

    /// Set the symbol of the `BV`. See notes on
    /// [`BV::new()`](struct.BV.html#method.new).
    pub fn set_symbol(&mut self, symbol: Option<&str>) {
        todo!()
        /*
        match symbol {
            None => unsafe { bitwuzla_term_set_symbol(self.node, std::ptr::null()) },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_term_set_symbol(self.node, symbol) }
            },
        }
         */
    }

    /// Does the `Bool` have a constant value?
    pub fn is_const(&self) -> bool {
        unsafe { bitwuzla_term_is_value(self.node) }
    }

    /// Assert that `self` is true.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, Bool, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // Create an unconstrained `BV`
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // (you may prefer this alternate style for assertions)
    /// Bool::assert(&bv.ugt(&BV::from_u32(btor.clone(), 3, 8)));
    ///
    /// // The state is satisfiable, and any solution we get
    /// // for `bv` must be greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// let solution = bv.get_a_solution().as_u64().unwrap();
    /// assert!(solution > 3);
    ///
    /// // Now we assert that `bv` must be less than `2`
    /// bv.ult(&BV::from_u32(btor.clone(), 2, 8)).assert();
    ///
    /// // The state is now unsatisfiable
    /// assert_eq!(btor.sat(), SolverResult::Unsat);
    /// ```
    pub fn assert(&self) {
        unsafe { bitwuzla_assert(self.btor.borrow().as_raw(), self.node) }
    }

    binop!(
        /// Returns the `BV` which is true if `self <=> other`, else false.
        /// `self` and `other` must have bitwidth 1.
        => iff, BITWUZLA_KIND_IFF
    );
    binop!(
        /// Returns the `BV` which is true if `self` implies `other`, else false.
        /// `self` and `other` must have bitwidth 1.
        => implies, BITWUZLA_KIND_IMPLIES
    );


    unop!(
        /// Bitwise `not` operation (one's complement)
        => not, BITWUZLA_KIND_NOT
    );
    binop!(
        /// Bitwise `and` operation. `self` and `other` must have the same bitwidth.
        => and, BITWUZLA_KIND_AND
    );
    binop!(
        /// Bitwise `or` operation. `self` and `other` must have the same bitwidth.
        => or, BITWUZLA_KIND_OR
    );
    binop!(
        /// Bitwise `xor` operation. `self` and `other` must have the same bitwidth.
        => xor, BITWUZLA_KIND_XOR
    );

    /// Create an if-then-else `BV` node.
    /// If `self` is true, then `truebv` is returned, else `falsebv` is returned.
    ///
    /// `self` must have bitwidth 1.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, Bool, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // Create an unconstrained `BV` `x`
    /// let x = BV::new(btor.clone(), 8, Some("x"));
    ///
    /// // `y` will be `5` if `x > 10`, else it will be `1`
    /// let five = BV::from_u32(btor.clone(), 5, 8);
    /// let one = BV::one(btor.clone(), 8);
    /// let cond = x.ugt(&BV::from_u32(btor.clone(), 10, 8));
    /// let y = cond.cond_bv(&five, &one);
    /// // (you may prefer this alternate style)
    /// let _y = Bool::cond_bv(&cond, &five, &one);
    ///
    /// // Now assert that `x < 7`
    /// x.ult(&BV::from_u32(btor.clone(), 7, 8)).assert();
    ///
    /// // As a result, `y` must be `1`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// assert_eq!(y.get_a_solution().as_u64().unwrap(), 1);
    /// ```
    pub fn cond_bv(&self, truebv: &BV<R>, falsebv: &BV<R>) -> BV<R> {
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    BITWUZLA_KIND_ITE,
                    self.node,
                    truebv.node,
                    falsebv.node,
                )
            },
        }
    }

    /// Create an if-then-else `Array` node.
    /// If `self` is true, then `true_array` is returned, else `false_array` is returned.
    ///
    /// `self` must have bitwidth 1.
    pub fn cond_array(&self, true_array: &Array<R>, false_array: &Array<R>) -> Array<R> {
        Array {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    BITWUZLA_KIND_ITE,
                    self.node,
                    true_array.node,
                    false_array.node,
                )
            },
        }
    }

    /// Create an if-then-else `FP` node.
    /// If `self` is true, then `true_fp` is returned, else `false_fp` is returned.
    ///
    /// `self` must have bitwidth 1.
    pub fn cond_fp(&self, true_fp: &FP<R>, false_fp: &FP<R>) -> FP<R> {
        FP {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    BITWUZLA_KIND_ITE,
                    self.node,
                    true_fp.node,
                    false_fp.node,
                )
            },
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Clone for Bool<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            node: self.node,
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for Bool<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let string = crate::util::tmp_file_to_string(
            |tmpfile| unsafe {
                bitwuzla_term_print(self.node, tmpfile);
            },
            true,
        )
        .trim()
        .to_owned();
        write!(f, "{}", string)
    }
}