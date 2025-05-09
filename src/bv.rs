use crate::btor::Bitwuzla;
use crate::sort::Sort;
use crate::{Bool, FP};
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::c_char;

/// A bitvector object: that is, a single symbolic value, consisting of some
/// number of symbolic bits.
///
/// This is generic in the `Bitwuzla` reference type.
/// For instance, you could use `BV<Rc<Bitwuzla>>` for single-threaded applications,
/// or `BV<Arc<Bitwuzla>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct BV<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: BitwuzlaTerm,
}

// According to
// https://groups.google.com/forum/#!msg/boolector/itYGgJxU3mY/AC2O0898BAAJ,
// the boolector library is thread-safe, meaning `*const BitwuzlaTerm` can be
// both `Send` and `Sync`.
// So as long as `R` is `Send` and/or `Sync`, we can mark `BV` as `Send` and/or
// `Sync` respectively.
// unsafe impl<R: Borrow<Bitwuzla> + Clone + Send> Send for BV<R> {}
// unsafe impl<R: Borrow<Bitwuzla> + Clone + Sync> Sync for BV<R> {}

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! unop {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self) -> Self {
            let tm = self.btor.borrow().tm;
            Self {
                btor: self.btor.clone(),
                node: unsafe { bitwuzla_mk_term1(tm, $kind, self.node) },
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
            let tm = self.btor.borrow().tm;
            Self {
                btor: self.btor.clone(),
                node:  unsafe { bitwuzla_mk_term2(tm, $kind, self.node, other.node) },
            }
        }
    };
}

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! binop_cmp {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self, other: &Self) -> Bool<R> {
            let tm = self.btor.borrow().tm;
            Bool {
                btor: self.btor.clone(),
                node:  unsafe { bitwuzla_mk_term2(tm, $kind, self.node, other.node) },
            }
        }
    };
}

impl<R: Borrow<Bitwuzla> + Clone> BV<R> {
    /// Create a new unconstrained `BV` variable of the given `width`.
    ///
    /// The `symbol`, if present, will be used to identify the `BV` when printing
    /// a model or dumping to file. It must be unique if it is present.
    ///
    /// `width` must not be 0.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Bitwuzla, BV, SolverResult};
    /// let btor = Bitwuzla::new();
    ///
    /// // An 8-bit unconstrained `BV` with the symbol "foo"
    /// let bv = BV::new(&btor, 8, Some("foo"));
    /// assert_eq!(format!("{:?}", bv), "foo");
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(&btor, 3, 8)).assert();
    ///
    /// // Now any solution must give it a value greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// let solution = bv.get_a_solution().as_u64().unwrap();
    /// assert!(solution > 3);
    /// ```
    pub fn new(btor: R, width: u64, symbol: Option<&str>) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        let node = match symbol {
            None => unsafe { bitwuzla_mk_const(tm, sort.as_raw(), std::ptr::null()) },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_mk_const(tm, sort.as_raw(), symbol) }
            },
        };
        Self { btor, node }
    }

    /// Create a new constant `BV` representing the given `bool` (either constant
    /// `true` or constant `false`).
    ///
    /// The resulting `BV` will be either constant `0` or constant `1`, and will
    /// have bitwidth 1.
    pub fn from_bool(btor: R, b: bool) -> Self {
        Self::from_u32(btor, b as u32, 1)
    }

    /// Create a new constant `BV` representing the given signed integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_i32(btor: R, val: i32, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_value_int64(tm, sort.as_raw(), val as i64) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` representing the given unsigned integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    ///
    /// For a code example, see [`BV::new()`](struct.BV.html#method.new).
    pub fn from_u32(btor: R, u: u32, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_value_uint64(tm, sort.as_raw(), u as u64) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` representing the given signed integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_i64(btor: R, val: i64, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_value_int64(tm, sort.as_raw(), val) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` representing the given unsigned integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_u64(btor: R, u: u64, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_value_uint64(tm, sort.as_raw(), u) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create the constant `0` of the given width.
    /// This is equivalent to `from_i32(btor, 0, width)`, but may be more efficient.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Btor::new();
    /// let zero = BV::zero(&btor, 8);
    /// assert_eq!(zero.as_u64().unwrap(), 0);
    /// ```
    pub fn zero(btor: R, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_zero(tm, sort.as_raw()) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create the constant `1` of the given width.
    /// This is equivalent to `from_i32(btor, 1, width)`, but may be more efficient.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// let one = BV::one(btor.clone(), 8);
    /// assert_eq!(one.as_u64().unwrap(), 1);
    /// ```
    pub fn one(btor: R, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_one(tm, sort.as_raw()) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a bitvector constant of the given width, where all bits are set to one.
    /// This is equivalent to `from_i32(btor, -1, width)`, but may be more efficient.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// let ones = BV::ones(btor.clone(), 8);
    /// assert_eq!(ones.as_binary_str().unwrap(), "11111111");
    /// ```
    pub fn ones(btor: R, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_ones(tm, sort.as_raw()) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` from the given string `bits` representing a
    /// binary number.
    ///
    /// `bits` must be non-empty and consist only of '0' and/or '1' characters.
    ///
    /// The resulting `BV` will have bitwidth equal to the length of `bits`.
    pub fn from_binary_str(btor: R, bits: &str) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), bits.len() as u64);
        let cstring = CString::new(bits).unwrap();
        Self {
            node: unsafe { bitwuzla_mk_bv_value(tm, sort.as_raw(), cstring.as_ptr(), 2) },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` from the given string `num` representing a
    /// (signed) decimal number. The new `BV` will have the width `width`, which
    /// must not be 0.
    pub fn from_dec_str(btor: R, num: &str, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        let cstring = CString::new(num).unwrap();
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value(tm, sort.as_raw(), cstring.as_ptr() as *const c_char, 10)
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` from the given string `num` representing a
    /// hexadecimal number. The new `BV` will have the width `width`, which must
    /// not be 0.
    pub fn from_hex_str(btor: R, num: &str, width: u64) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::bitvector(btor.clone(), width);
        let cstring = CString::new(num).unwrap();
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value(tm, sort.as_raw(), cstring.as_ptr() as *const c_char, 16)
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Simplify the `BV` using the current state of the `Btor`.
    pub fn simplify(&self) -> Self {
        Self {
            node: unsafe { bitwuzla_simplify_term(self.btor.borrow().as_raw(), self.node) },
            btor: self.btor.clone(),
        }
    }

    /// Get the value of the `BV` as a string of '0's and '1's. This method is
    /// only effective for `BV`s which are constant, as indicated by
    /// [`BV::is_const()`](struct.BV.html#method.is_const).
    ///
    /// This method does not require the current state to be satisfiable. To get
    /// the value of nonconstant `BV` objects given the current constraints, see
    /// [`get_a_solution()`](struct.BV.html#method.get_a_solution), which does
    /// require that the current state be satisfiable.
    ///
    /// Returns `None` if the `BV` is not constant.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // This `BV` is constant, so we get a `Some`
    /// let five = BV::from_u32(btor.clone(), 5, 8);
    /// assert_eq!(five.as_binary_str(), Some("00000101".to_owned()));
    ///
    /// // This `BV` is not constant, so we get `None`
    /// let unconstrained = BV::new(btor.clone(), 8, Some("foo"));
    /// assert_eq!(unconstrained.as_binary_str(), None);
    /// ```
    pub fn as_binary_str(&self) -> Option<String> {
        if self.is_const() {
            let string = unsafe { CStr::from_ptr(bitwuzla_term_to_string_fmt(self.node, 2)) };
            let string = string.to_string_lossy();
            assert!(string.starts_with("#b"));
            let string = string[2 ..].to_string();
            Some(string)
        } else {
            None
        }
    }

    /// Get the value of the `BV` as a `u64`. This method is only effective for
    /// `BV`s which are constant, as indicated by
    /// [`BV::is_const()`](struct.BV.html#method.is_const).
    ///
    /// This method does not require the current state to be satisfiable. To get
    /// the value of nonconstant `BV` objects given the current constraints, see
    /// [`get_a_solution()`](struct.BV.html#method.get_a_solution), which does
    /// require that the current state be satisfiable.
    ///
    /// Returns `None` if the `BV` is not constant, or if the value does not fit
    /// in 64 bits.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // This `BV` is constant, so we get a `Some`
    /// let five = BV::from_u32(btor.clone(), 5, 8);
    /// assert_eq!(five.as_u64(), Some(5));
    ///
    /// // This `BV` is not constant, so we get `None`
    /// let unconstrained = BV::new(btor.clone(), 8, Some("foo"));
    /// assert_eq!(unconstrained.as_u64(), None);
    /// ```
    pub fn as_u64(&self) -> Option<u64> {
        if self.is_const() {
            let binary_string = self.as_binary_str()?;
            Some(u64::from_str_radix(&binary_string, 2).unwrap())
        } else {
            None
        }
    }

    /// Get the value of the `BV` as a `bool`. This method is only effective for
    /// `BV`s which are constant, as indicated by
    /// [`BV::is_const()`](struct.BV.html#method.is_const).
    ///
    /// Returns `true` if the `BV` has a constant nonzero value, or `false` if
    /// the `BV` has a constant zero value.
    /// Returns `None` if the `BV` is not constant.
    pub fn as_bool(&self) -> Option<bool> {
        if self.is_const() {
            let binary_string = self.as_binary_str()?;
            for c in binary_string.chars() {
                if c != '0' {
                    return Some(true);
                }
            }
            Some(false)
        } else {
            None
        }
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
    pub fn get_a_solution(&self) -> BVSolution {
        let bv_val = unsafe { bitwuzla_get_value(self.btor.borrow().as_raw(), self.node) };
        let bv_str = unsafe { bitwuzla_term_value_get_str(bv_val) };
        BVSolution::from_raw(bv_str)
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

    /// Get the bitwidth of the `BV`
    pub fn get_width(&self) -> u64 {
        unsafe { bitwuzla_term_bv_get_size(self.node) }
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
    pub fn set_symbol(&mut self, _symbol: Option<&str>) {
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

    /// Does the `BV` have a constant value?
    ///
    /// # Examples
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use bitwuzla::option::ModelGen;
    /// let btor = Btor::builder().model_gen(ModelGen::All).build();
    ///
    /// // This `BV` is constant
    /// let five = BV::from_u32(&btor, 5, 8);
    /// assert!(five.is_const());
    ///
    /// // This `BV` is not constant
    /// let unconstrained = BV::new(&btor, 8, Some("foo"));
    /// assert!(!unconstrained.is_const());
    ///
    /// // 5 + [unconstrained] is also not constant
    /// let sum = five.add(&unconstrained);
    /// assert!(!sum.is_const());
    ///
    /// // Note that 5 + 5 is not considered a constant
    /// let sum = five.add(&five);
    /// assert!(!sum.is_const());
    /// ```
    pub fn is_const(&self) -> bool {
        // let node = unsafe { bitwuzla_get_value(self.btor.borrow().as_raw(), self.node)};
        unsafe { bitwuzla_term_is_value(self.node) }
    }

    /// Does `self` have the same width as `other`?
    pub fn has_same_width(&self, other: &Self) -> bool {
        unsafe { bitwuzla_term_is_equal_sort(self.node, other.node) }
    }

    /// Assert that `self != 0`.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, Bool, BV, SolverResult};
    /// let btor = Btor::new();
    ///
    /// // Create an unconstrained `BV`
    /// let bv = BV::new(&btor, 8, Some("foo"));
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(&btor, 3, 8)).assert();
    ///
    /// // (you may prefer this alternate style for assertions)
    /// Bool::assert(&bv.ugt(&BV::from_u32(&btor, 3, 8)));
    ///
    /// // The state is satisfiable, and any solution we get
    /// // for `bv` must be greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// let solution = bv.get_a_solution().as_u64().unwrap();
    /// assert!(solution > 3);
    ///
    /// // Now we assert that `bv` must be less than `2`
    /// bv.ult(&BV::from_u32(&btor, 2, 8)).assert();
    ///
    /// // The state is now unsatisfiable
    /// assert_eq!(btor.sat(), SolverResult::Unsat);
    /// ```
    pub fn assert(&self) {
        let zero = Self::from_u32(self.btor.clone(), 0, self.get_width());
        self._ne(&zero).assert();
    }

    binop_cmp!(
        /// Bitvector equality. `self` and `other` must have the same bitwidth.
        => _eq, BITWUZLA_KIND_EQUAL
    );
    binop_cmp!(
        /// Bitvector inequality. `self` and `other` must have the same bitwidth.
        => _ne, BITWUZLA_KIND_DISTINCT
    );

    binop!(
        /// Bitvector addition. `self` and `other` must have the same bitwidth.
        => add, BITWUZLA_KIND_BV_ADD
    );
    binop!(
        /// Bitvector subtraction. `self` and `other` must have the same bitwidth.
        => sub, BITWUZLA_KIND_BV_SUB
    );
    binop!(
        /// Bitvector multiplication. `self` and `other` must have the same bitwidth.
        => mul, BITWUZLA_KIND_BV_MUL
    );
    binop!(
        /// Unsigned division. `self` and `other` must have the same bitwidth.
        /// Division by `0` produces `-1`.
        => udiv, BITWUZLA_KIND_BV_UDIV
    );
    binop!(
        /// Signed division. `self` and `other` must have the same bitwidth.
        => sdiv, BITWUZLA_KIND_BV_SDIV
    );
    binop!(
        /// Unsigned remainder. `self` and `other` must have the same bitwidth.
        /// If `other` is `0`, the result will be `self`.
        => urem, BITWUZLA_KIND_BV_UREM
    );
    binop!(
        /// Signed remainder. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have positive sign.
        => srem, BITWUZLA_KIND_BV_SREM
    );
    binop!(
        /// Signed remainder. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have sign matching the divisor.
        => smod, BITWUZLA_KIND_BV_SMOD
    );
    unop!(
        /// Increment operation
        => inc, BITWUZLA_KIND_BV_INC
    );
    unop!(
        /// Decrement operation
        => dec, BITWUZLA_KIND_BV_DEC
    );
    unop!(
        /// Two's complement negation
        => neg, BITWUZLA_KIND_BV_NEG
    );

    binop!(
        /// Unsigned addition overflow detection. Resulting `BV` will have bitwidth
        /// one, and be `true` if adding `self` and `other` would overflow when
        /// interpreting both `self` and `other` as unsigned.
        => uaddo, BITWUZLA_KIND_BV_UADD_OVERFLOW
    );
    binop!(
        /// Signed addition overflow detection. Resulting `BV` will have bitwidth
        /// one, and be `true` if adding `self` and `other` would overflow when
        /// interpreting both `self` and `other` as signed.
        => saddo, BITWUZLA_KIND_BV_SADD_OVERFLOW
    );
    binop!(
        /// Unsigned subtraction overflow detection. Resulting `BV` will have bitwidth
        /// one, and be `true` if subtracting `self` and `other` would overflow when
        /// interpreting both `self` and `other` as unsigned.
        => usubo, BITWUZLA_KIND_BV_USUB_OVERFLOW
    );
    binop!(
        /// Signed subtraction overflow detection. Resulting `BV` will have bitwidth
        /// one, and be `true` if subtracting `self` and `other` would overflow when
        /// interpreting both `self` and `other` as signed.
        => ssubo, BITWUZLA_KIND_BV_SSUB_OVERFLOW
    );
    binop!(
        /// Unsigned multiplication overflow detection. Resulting `BV` will have
        /// bitwidth 1, and be `true` if multiplying `self` and `other` would
        /// overflow when interpreting both `self` and `other` as unsigned.
        => umulo, BITWUZLA_KIND_BV_UMUL_OVERFLOW
    );
    binop!(
        /// Signed multiplication overflow detection. Resulting `BV` will have
        /// bitwidth 1, and be `true` if multiplying `self` and `other` would
        /// overflow when interpreting both `self` and `other` as signed.
        => smulo, BITWUZLA_KIND_BV_SMUL_OVERFLOW
    );
    binop!(
        /// Signed division overflow detection. Resulting `BV` will have bitwidth
        /// one, and be `true` if dividing `self` by `other` would overflow when
        /// interpreting both `self` and `other` as signed.
        ///
        /// Signed division can overflow if `self` is `INT_MIN` and `other` is `-1`.
        /// Note that unsigned division cannot overflow.
        => sdivo, BITWUZLA_KIND_BV_SDIV_OVERFLOW
    );

    unop!(
        /// Bitwise `not` operation (one's complement)
        => not, BITWUZLA_KIND_BV_NOT
    );
    binop!(
        /// Bitwise `and` operation. `self` and `other` must have the same bitwidth.
        => and, BITWUZLA_KIND_BV_AND
    );
    binop!(
        /// Bitwise `or` operation. `self` and `other` must have the same bitwidth.
        => or, BITWUZLA_KIND_BV_OR
    );
    binop!(
        /// Bitwise `xor` operation. `self` and `other` must have the same bitwidth.
        => xor, BITWUZLA_KIND_BV_XOR
    );
    binop!(
        /// Bitwise `nand` operation. `self` and `other` must have the same bitwidth.
        => nand, BITWUZLA_KIND_BV_NAND
    );
    binop!(
        /// Bitwise `nor` operation. `self` and `other` must have the same bitwidth.
        => nor, BITWUZLA_KIND_BV_NOR
    );
    binop!(
        /// Bitwise `xnor` operation. `self` and `other` must have the same bitwidth.
        => xnor, BITWUZLA_KIND_BV_XNOR
    );

    binop!(
        /// Logical shift left: shift `self` left by `other` bits.
        /// Either `self` and `other` must have the same bitwidth, or `self` must
        /// have a bitwidth which is a power of two and the bitwidth of `other` must
        /// be log2 of the bitwidth of `self`.
        ///
        /// Resulting `BV` will have the same bitwidth as `self`.
        => sll, BITWUZLA_KIND_BV_SHL
    );
    binop!(
        /// Logical shift right: shift `self` right by `other` bits.
        /// Either `self` and `other` must have the same bitwidth, or `self` must
        /// have a bitwidth which is a power of two and the bitwidth of `other` must
        /// be log2 of the bitwidth of `self`.
        ///
        /// Resulting `BV` will have the same bitwidth as `self`.
        => srl, BITWUZLA_KIND_BV_SHR
    );
    binop!(
        /// Arithmetic shift right: shift `self` right by `other` bits.
        /// Either `self` and `other` must have the same bitwidth, or `self` must
        /// have a bitwidth which is a power of two and the bitwidth of `other` must
        /// be log2 of the bitwidth of `self`.
        ///
        /// Resulting `BV` will have the same bitwidth as `self`.
        => sra, BITWUZLA_KIND_BV_ASHR
    );
    binop!(
        /// Rotate `self` left by `other` bits.
        /// `self` must have a bitwidth which is a power of two, and the bitwidth of
        /// `other` must be log2 of the bitwidth of `self`.
        ///
        /// Resulting `BV` will have the same bitwidth as `self`.
        => rol, BITWUZLA_KIND_BV_ROL
    );
    binop!(
        /// Rotate `self` right by `other` bits.
        /// `self` must have a bitwidth which is a power of two, and the bitwidth of
        /// `other` must be log2 of the bitwidth of `self`.
        ///
        /// Resulting `BV` will have the same bitwidth as `self`.
        => ror, BITWUZLA_KIND_BV_ROR
    );

    unop!(
        /// `and` reduction operation: take the Boolean `and` of all bits in the `BV`.
        /// Resulting `BV` will have bitwidth 1.
        => redand, BITWUZLA_KIND_BV_REDAND
    );
    unop!(
        /// `or` reduction operation: take the Boolean `or` of all bits in the `BV`.
        /// Resulting `BV` will have bitwidth 1.
        => redor, BITWUZLA_KIND_BV_REDOR
    );
    unop!(
        /// `xor` reduction operation: take the Boolean `xor` of all bits in the `BV`.
        /// Resulting `BV` will have bitwidth 1.
        => redxor, BITWUZLA_KIND_BV_REDXOR
    );

    binop_cmp!(
        /// Unsigned greater than. `self` and `other` must have the same bitwidth.
        => ugt, BITWUZLA_KIND_BV_UGT
    );
    binop_cmp!(
        /// Unsigned greater than or equal. `self` and `other` must have the same bitwidth.
        => ugte, BITWUZLA_KIND_BV_UGE
    );
    binop_cmp!(
        /// Signed greater than. `self` and `other` must have the same bitwidth.
        => sgt, BITWUZLA_KIND_BV_SGT
    );
    binop_cmp!(
        /// Signed greater than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => sgte, BITWUZLA_KIND_BV_SGE
    );
    binop_cmp!(
        /// Unsigned less than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ult, BITWUZLA_KIND_BV_ULT
    );
    binop_cmp!(
        /// Unsigned less than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ulte, BITWUZLA_KIND_BV_ULE
    );
    binop_cmp!(
        /// Signed less than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => slt, BITWUZLA_KIND_BV_SLT
    );
    binop_cmp!(
        /// Signed less than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => slte, BITWUZLA_KIND_BV_SLE
    );

    /// Unsigned extension (zero-extension), extending by `n` bits. Resulting
    /// `BV` will have bitwidth equal to the bitwidth of `self` plus `n`.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// let btor = Btor::new();
    ///
    /// // Create an 8-bit `BV` with value `3`
    /// let bv = BV::from_u32(&btor, 3, 8);
    ///
    /// // Zero-extend by 56 bits
    /// let extended = bv.uext(56).simplify();
    ///
    /// // Resulting `BV` is 64 bits and has value `3`
    /// assert_eq!(extended.get_width(), 64);
    /// assert_eq!(extended.as_u64().unwrap(), 3);
    /// ```
    pub fn uext(&self, n: u64) -> Self {
        let tm = self.btor.borrow().tm;
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_BV_ZERO_EXTEND, self.node, n)
            },
        }
    }

    /// Sign-extension operation, extending by `n` bits. Resulting `BV` will have
    /// bitwidth equal to the bitwidth of `self` plus `n`.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // Create an 8-bit `BV` with value `-3`
    /// let bv = BV::from_i32(btor.clone(), -3, 8);
    ///
    /// // Sign-extend by 56 bits
    /// let extended = bv.sext(56).simplify();
    ///
    /// // Resulting `BV` is 64 bits and has value `-3`
    /// assert_eq!(extended.get_width(), 64);
    /// assert_eq!(extended.as_u64().unwrap() as i64, -3);
    /// ```
    pub fn sext(&self, n: u64) -> Self {
        let tm = self.btor.borrow().tm;
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_BV_SIGN_EXTEND, self.node, n)
            },
        }
    }

    /// Slicing operation: obtain bits `high` through `low` (inclusive) of `self`.
    /// Resulting `BV` will have bitwidth `high - low + 1`.
    ///
    /// Requires that `0 <= low <= high < self.get_width()`.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // Create an 8-bit `BV` with this constant value
    /// let bv = BV::from_binary_str(btor.clone(), "01100101");
    ///
    /// // Slice out bits 1 through 4, inclusive
    /// let slice = bv.slice(4, 1).simplify();
    ///
    /// // Resulting slice has width `4` and value `"0010"`
    /// assert_eq!(slice.get_width(), 4);
    /// assert_eq!(slice.as_binary_str().unwrap(), "0010");
    pub fn slice(&self, high: u64, low: u64) -> Self {
        let tm = self.btor.borrow().tm;
        assert!(
            low <= high,
            "slice: low must be <= high; got low = {}, high = {}",
            low,
            high
        );
        assert!(
            high < self.get_width(),
            "slice: high must be < width; got high = {}, width = {}",
            high,
            self.get_width()
        );
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed2(tm, BITWUZLA_KIND_BV_EXTRACT, self.node, high, low)
            },
        }
    }

    binop!(
        /// Concatenate two bitvectors. Resulting `BV` will have bitwidth equal to
        /// the sum of `self` and `other`'s bitwidths.
        /// # Example
        ///
        /// ```
        /// # use bitwuzla::{Btor, BV};
        /// # use std::rc::Rc;
        /// let btor = Rc::new(Btor::new());
        ///
        /// // Create an 8-bit `BV` with value `1`
        /// let one = BV::one(btor.clone(), 8);
        ///
        /// // Create an 8-bit `BV` consisting of all ones
        /// let ones = BV::ones(btor.clone(), 8);
        ///
        /// // The concatenation has length 16 and this value
        /// let result = ones.concat(&one).simplify();
        /// assert_eq!(result.get_width(), 16);
        /// assert_eq!(result.as_binary_str().unwrap(), "1111111100000001");
        ///
        /// // Concatenate in the other order
        /// let result = one.concat(&ones).simplify();
        /// assert_eq!(result.get_width(), 16);
        /// assert_eq!(result.as_binary_str().unwrap(), "0000000111111111");
        /// ```
        => concat, BITWUZLA_KIND_BV_CONCAT
    );

    /// Concatenate the `BV` with itself `n` times
    pub fn repeat(&self, n: u64) -> Self {
        let tm = self.btor.borrow().tm;
        Self {
            btor: self.btor.clone(),
            node: unsafe { bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_BV_REPEAT, self.node, n) },
        }
    }

    pub fn to_bool(&self) -> Bool<R> {
        debug_assert_eq!(self.get_width(), 1);
        let one = Self::from_u32(self.btor.clone(), 1, 1);
        self._eq(&one)
    }

    pub fn to_fp32(&self) -> FP<R> {
        self.to_fp(8, 23 + 1)
    }

    pub fn to_fp64(&self) -> FP<R> {
        self.to_fp(11, 52 + 1)
    }

    pub fn to_fp(&self, exp_width: u64, sig_width: u64) -> FP<R> {
        let tm = self.btor.borrow().tm;
        FP {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed2(
                    tm,
                    BITWUZLA_KIND_FP_TO_FP_FROM_BV,
                    self.node,
                    exp_width,
                    sig_width,
                )
            },
        }
        .simplify()
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Clone for BV<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            node: self.node,
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for BV<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let string = unsafe { CStr::from_ptr(bitwuzla_term_to_string(self.node)) };
        write!(f, "{}", string.to_string_lossy())
    }
}

/// A `BVSolution` represents a possible solution for one `BV` in a given model.
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct BVSolution {
    assignment: String,
}

impl BVSolution {
    /// expects an `assignment` in _binary_ (01x) format
    ///
    /// relevant: https://github.com/boolector/boolector/issues/79
    fn from_raw(assignment: *const c_char) -> Self {
        Self {
            assignment: {
                let cstr = unsafe { CStr::from_ptr(assignment) };
                cstr.to_str().unwrap().to_owned()
            },
        }
    }

    /// Get a string of length equal to the bitwidth, where each character in the
    /// string is either `0`, `1`, or `x`. An `x` indicates that, in this model,
    /// the corresponding bit can be arbitrarily chosen to be `0` or `1` and all
    /// constraints would still be satisfied.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
    /// let btor = Btor::new();
    ///
    /// // `bv` starts as an unconstrained 8-bit value
    /// let bv = BV::new(&btor, 8, Some("foo"));
    ///
    /// // assert that the first two digits of `bv` are 0
    /// let mask = BV::from_u32(&btor, 0b11000000, 8);
    /// let zero = BV::zero(&btor, 8);
    /// bv.and(&mask)._eq(&zero).assert();
    ///
    /// // `as_01x_str()` gives an 8-character string whose first
    /// // two digits are '0'
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// let solution = bv.get_a_solution();
    /// assert_eq!(&solution.as_01x_str()[..2], "00");
    /// ```
    pub fn as_01x_str(&self) -> &str {
        &self.assignment
    }

    /// Turn a string of `0`, `1`, and/or `x` characters into a `BVSolution`.
    /// See [`as_01x_str()`](struct.BVSolution.html#method.as_01x_str).
    pub fn from_01x_str(s: impl Into<String>) -> Self {
        Self {
            assignment: s.into(),
        }
    }

    /// Get a version of this `BVSolution` that is guaranteed to correspond to
    /// exactly one possible value. For instance,
    /// [`as_01x_str()`](struct.BVSolution.html#method.as_01x_str) on the
    /// resulting `BVSolution` will contain no `x`s.
    ///
    /// In the event that the input `BVSolution` did represent multiple possible
    /// values (see [`as_01x_str()`](struct.BVSolution.html#method.as_01x_str)),
    /// this will simply choose one possible value arbitrarily.
    pub fn disambiguate(&self) -> Self {
        Self {
            assignment: self
                .as_01x_str()
                .chars()
                .map(|c| match c {
                    'x' => '0',
                    c => c,
                })
                .collect(),
        }
    }

    /// Get a `u64` value for the `BVSolution`. In the event that this
    /// `BVSolution` represents multiple possible values (see
    /// [`as_01x_str()`](struct.BVSolution.html#method.as_01x_str)), this will
    /// simply choose one possible value arbitrarily.
    ///
    /// Returns `None` if the value does not fit in 64 bits.
    ///
    /// For a code example, see [`BV::new()`](struct.BV.html#method.new).
    pub fn as_u64(&self) -> Option<u64> {
        let disambiguated = self.disambiguate();
        let binary_string = disambiguated.as_01x_str();
        if binary_string.len() > 64 {
            None
        } else {
            Some(u64::from_str_radix(&binary_string, 2).unwrap_or_else(|e| {
                panic!(
                    "Got the following error while trying to parse {:?} as a binary string: {}",
                    binary_string, e
                )
            }))
        }
    }

    /// Get a `bool` value for the `BVSolution`. In the event that this
    /// `BVSolution` represents both `true` and `false` (see
    /// [`as_01x_str()`](struct.BVSolution.html#method.as_01x_str)), this will
    /// return `false`.
    ///
    /// Returns `None` if the `BVSolution` is not a 1-bit value.
    pub fn as_bool(&self) -> Option<bool> {
        let binary_string = self.as_01x_str();
        if binary_string.len() == 1 {
            match binary_string.chars().nth(0).unwrap() {
                '0' => Some(false),
                '1' => Some(true),
                'x' => Some(false),
                c => panic!("Unexpected solution character: {}", c),
            }
        } else {
            None
        }
    }
}
