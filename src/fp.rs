use crate::btor::Bitwuzla;
use crate::sort::Sort;
use crate::Bool;
use crate::RoundingMode;
use crate::BV;
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::CStr;
use std::ffi::CString;
use std::fmt;
use std::os::raw::c_char;

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
macro_rules! unop_cmp {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self) -> Bool<R> {
            let tm = self.btor.borrow().tm;
            Bool {
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

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! ternop {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self, other: &Self, rounding_mode: RoundingMode) -> Self {
            let tm = self.btor.borrow().tm;
            let rm = rounding_mode.to_node(self.btor.clone());
            Self {
                btor: self.btor.clone(),
                node:  unsafe { bitwuzla_mk_term3(tm, $kind, rm.node, self.node, other.node) },
            }
        }
    };
}

/// A floating-point object: that is, a single symbolic value, consisting of a
/// symbolic exponent, significand component, and sign component.
///
/// This is generic in the `Bitwuzla` reference type.
/// For instance, you could use `FP<Rc<Bitwuzla>>` for single-threaded applications,
/// or `FP<Arc<Bitwuzla>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct FP<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: BitwuzlaTerm,
}

impl<R: Borrow<Bitwuzla> + Clone> FP<R> {
    /// Create a new unconstrained `FP` variable of the given `exp_width` and `sig_width`.
    ///
    /// The `symbol`, if present, will be used to identify the `FP` when printing
    /// a model or dumping to file. It must be unique if it is present.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Bitwuzla, FP, SolverResult};
    /// let btor = Bitwuzla::new();
    ///
    /// // An 8-bit unconstrained `BV` with the symbol "foo"
    /// let fp = FP::new(&btor, 8, 24, Some("foo"));
    /// assert_eq!(format!("{:?}", fp), "foo");
    ///
    /// // Assert that it must be greater than `3`
    /// // fp.gt(&BV::from_u32(&btor, 3, 8)).assert();
    ///
    /// // Now any solution must give it a value greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// // let solution = fp.get_a_solution().as_u64().unwrap();
    /// // assert!(solution > 3);
    /// ```
    pub fn new(btor: R, exp_width: u64, sig_width: u64, symbol: Option<&str>) -> Self {
        let tm = btor.borrow().tm;
        let sort = Sort::fp(btor.clone(), exp_width, sig_width);
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

    pub fn new_binary32(btor: R, symbol: Option<&str>) -> Self {
        Self::new(btor, 8, 23 + 1, symbol)
    }

    pub fn new_binary64(btor: R, symbol: Option<&str>) -> Self {
        Self::new(btor, 11, 52 + 1, symbol)
    }

    /// Create a new constant `FP` representing the given floating point value.
    /// The new `FP` represents an IEEE 754 binary32 value.
    pub fn from_f32(btor: R, val: f32) -> Self {
        BV::from_u32(btor, val.to_bits(), 32).to_fp(8, 23 + 1)
    }

    /// Create a new constant `FP` representing the given floating point value.
    /// The new `FP` represents an IEEE 754 binary64 value.
    pub fn from_f64(btor: R, val: f64) -> Self {
        BV::from_u64(btor, val.to_bits(), 64).to_fp(11, 52 + 1)
    }

    /// Simplify the `FP` using the current state of the `Btor`.
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
    /// # use bitwuzla::{Btor, FP};
    /// let btor = Btor::new();
    ///
    /// // This `BV` is constant, so we get a `Some`
    /// let leet = FP::from_f32(&btor, 1337.0);
    /// assert_eq!(leet.as_str().as_deref(), Some("(fp #b0 #b10001001 #b01001110010000000000000)"));
    /// assert_eq!(leet.as_f64(), Some(1337.0));
    ///
    /// // This `BV` is not constant, so we get `None`
    /// let unconstrained = FP::new(&btor, 8, 24, Some("foo"));
    /// assert_eq!(unconstrained.as_str(), None);
    /// ```
    pub fn as_str(&self) -> Option<String> {
        let self_ = self.simplify();
        if self_.is_const() {
            let string = unsafe { CStr::from_ptr(bitwuzla_term_to_string(self_.node)) };
            Some(string.to_string_lossy().into_owned())
        } else {
            None
        }
    }

    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, FP};
    /// let btor = Btor::new();
    ///
    /// // as_f64 should round-trip for every edgecase:
    /// for val in [-0., 0., f64::MIN, f64::MAX, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
    ///     let leet = FP::from_f64(&btor, val);
    ///     assert_eq!(leet.simplify().as_f64(), Some(val));
    /// }
    /// ```
    pub fn as_f64(&self) -> Option<f64> {
        if self.is_const() {
            let s = self.as_str()?;
            assert!(s.starts_with("(fp #b"));
            let bits = s
                .chars()
                .filter(|c| c.is_digit(2))
                .map(|c| c == '1')
                .collect::<Vec<_>>();
            match bits.len() {
                // "(fp #b0 #b10000001 #b01000000000000000000000)"
                32 => {
                    let mut val = 0u32;
                    for i in 0 .. 32 {
                        val |= (bits[i] as u32) << i;
                    }
                    Some(f32::from_bits(val.to_be()) as f64);
                    todo!()
                },
                64 => {
                    let mut val = 0u64;
                    for i in 0 .. 64 {
                        val |= (bits[i] as u64) << i;
                    }
                    Some(f64::from_bits(val.to_be()));
                    todo!()
                },
                _ => unimplemented!(),
            }
        } else {
            None
        }
    }

    /// Does the `FP` have a constant value?
    ///
    /// Note: bitwuzla `is_const` is something entirely different
    ///
    /// # Examples
    ///
    /// ```
    /// # use bitwuzla::{Btor, FP, RoundingMode};
    /// let btor = Btor::new();
    ///
    /// // This `FP` is constant
    /// let pi = FP::from_f32(&btor, 3.1415);
    /// assert!(pi.is_const());
    ///
    /// // This `BV` is not constant
    /// let unconstrained = FP::new_binary32(&btor, Some("foo"));
    /// assert!(!unconstrained.is_const());
    ///
    /// // pi + [unconstrained] is also not constant
    /// let sum = pi.add(&unconstrained, RoundingMode::RTN);
    /// assert!(!sum.is_const());
    ///
    /// // But pi + pi is constant
    /// let tau = pi.add(&pi, RoundingMode::RTN).simplify();
    /// assert!(tau.is_const());
    /// ```
    pub fn is_const(&self) -> bool {
        unsafe { bitwuzla_term_is_value(self.node) }
    }

    unop!(
        /// Floating-point absolute value.
        => abs, BITWUZLA_KIND_FP_ABS
    );

    ternop!(
        /// Floating-point addition. `self` and `other` must have the same layout.
        => add, BITWUZLA_KIND_FP_ADD
    );

    ternop!(
        /// Floating-point division. `self` and `other` must have the same layout.
        => div, BITWUZLA_KIND_FP_DIV
    );

    binop_cmp!(
        /// Floating-point equality. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => _eq, BITWUZLA_KIND_FP_EQUAL
    );

    binop!(
        /// Floating-point fused multiplcation and addition. `self` and `other` must have the same layout.
        => fma, BITWUZLA_KIND_FP_FMA
    );

    binop_cmp!(
        /// Floating-point greater than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => geq, BITWUZLA_KIND_FP_GEQ
    );

    binop_cmp!(
        /// Floating-point greater than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => gt, BITWUZLA_KIND_FP_GT
    );

    unop_cmp!(
        /// Floating-point is Nan tester.
        /// Resulting `BV` will have bitwidth 1.
        => is_nan, BITWUZLA_KIND_FP_IS_NAN
    );

    unop_cmp!(
        /// Floating-point is negative tester.
        /// Resulting `BV` will have bitwidth 1.
        => is_neg, BITWUZLA_KIND_FP_IS_NEG
    );

    unop_cmp!(
        /// Floating-point is subnormal tester.
        /// Resulting `BV` will have bitwidth 1.
        => is_subnormal, BITWUZLA_KIND_FP_IS_SUBNORMAL
    );

    unop_cmp!(
        /// Floating-point is zero tester.
        /// Resulting `BV` will have bitwidth 1.
        => is_zero, BITWUZLA_KIND_FP_IS_ZERO
    );

    binop_cmp!(
        /// Floating-point less than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => lt, BITWUZLA_KIND_FP_LT
    );

    binop_cmp!(
        /// Floating-point greater than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => leq, BITWUZLA_KIND_FP_LEQ
    );

    binop!(
        /// Floating-point max. `self` and `other` must have the same layout.
        => max, BITWUZLA_KIND_FP_MAX
    );

    binop!(
        /// Floating-point min. `self` and `other` must have the same layout.
        => min, BITWUZLA_KIND_FP_MIN
    );

    ternop!(
        /// Floating-point multiplcation. `self` and `other` must have the same layout.
        => mul, BITWUZLA_KIND_FP_MUL
    );

    unop!(
        /// Floating-point negation.
        => neg, BITWUZLA_KIND_FP_NEG
    );

    binop!(
        /// Floating-point remainder. `self` and `other` must have the same layout.
        => rem, BITWUZLA_KIND_FP_REM
    );

    /// Floating-point round to integral.
    pub fn round_to_integral(&self, rounding_mode: RoundingMode) -> Self {
        let tm = self.btor.borrow().tm;
        let rm = rounding_mode.to_node(self.btor.clone());
        Self {
            btor: self.btor.clone(),
            node: unsafe { bitwuzla_mk_term2(tm, BITWUZLA_KIND_FP_RTI, rm.node, self.node) },
        }
    }

    unop!(
        /// Floating-point round to square root. (sic)
        => sqrt, BITWUZLA_KIND_FP_SQRT
    );

    ternop!(
        /// Floating-point round to subtraction. (sic)
        => sub, BITWUZLA_KIND_FP_SUB
    );

    pub fn to_sbv(&self, width: u64) -> BV<R> {
        let tm = self.btor.borrow().tm;
        // TODO: assert width?
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_FP_TO_SBV, self.node, width)
            },
        }
    }

    pub fn to_ubv(&self, width: u64) -> BV<R> {
        let tm = self.btor.borrow().tm;
        // TODO: assert width?
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(tm, BITWUZLA_KIND_FP_TO_UBV, self.node, width)
            },
        }
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
                    BITWUZLA_KIND_FP_TO_FP_FROM_FP,
                    self.node,
                    exp_width,
                    sig_width,
                )
            },
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Clone for FP<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            node: self.node,
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for FP<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let string = unsafe { CStr::from_ptr(bitwuzla_term_to_string(self.node)) };
        write!(f, "{}", string.to_string_lossy())
    }
}
