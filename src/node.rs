use crate::btor::Bitwuzla;
use crate::sort::Sort;
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::{c_char, c_void};

/// A bitvector object: that is, a single symbolic value, consisting of some
/// number of symbolic bits.
///
/// This is generic in the `Btor` reference type.
/// For instance, you could use `BV<Rc<Btor>>` for single-threaded applications,
/// or `BV<Arc<Btor>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct BV<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: *const BitwuzlaTerm,
}

// According to
// https://groups.google.com/forum/#!msg/bitwuzla/itYGgJxU3mY/AC2O0898BAAJ,
// the bitwuzla library is thread-safe, meaning `*const BitwuzlaTerm` can be
// both `Send` and `Sync`.
// So as long as `R` is `Send` and/or `Sync`, we can mark `BV` as `Send` and/or
// `Sync` respectively.
unsafe impl<R: Borrow<Bitwuzla> + Clone + Send> Send for BV<R> {}
unsafe impl<R: Borrow<Bitwuzla> + Clone + Sync> Sync for BV<R> {}

// The attr:meta stuff is so that doc comments work correctly.
// See https://stackoverflow.com/questions/41361897/documenting-a-function-created-with-a-macro-in-rust
macro_rules! unop {
    ( $(#[$attr:meta])* => $f:ident, $kind:ident ) => {
        $(#[$attr])*
        pub fn $f(&self) -> Self {
            Self {
                btor: self.btor.clone(),
                node: unsafe { bitwuzla_mk_term1(self.btor.borrow().as_raw(), $kind, self.node) },
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
                node:  unsafe { bitwuzla_mk_term2(self.btor.borrow().as_raw(), $kind, self.node, other.node) },
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
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Bitwuzla::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // An 8-bit unconstrained `BV` with the symbol "foo"
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // Now any solution must give it a value greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// let solution = bv.get_a_solution().as_u64().unwrap();
    /// assert!(solution > 3);
    /// ```
    pub fn new(btor: R, width: u32, symbol: Option<&str>) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        let node = match symbol {
            None => unsafe {
                bitwuzla_mk_const(btor.borrow().as_raw(), sort.as_raw(), std::ptr::null())
            },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_mk_const(btor.borrow().as_raw(), sort.as_raw(), symbol) }
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
        let node = if b {
            unsafe { bitwuzla_mk_true(btor.borrow().as_raw()) }
        } else {
            unsafe { bitwuzla_mk_false(btor.borrow().as_raw()) }
        };
        Self { btor, node }
    }

    /// Create a new constant `BV` representing the given signed integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_i32(btor: R, i: i32, width: u32) -> Self {
        // TODO: how to handle sign extend?
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value_uint64(btor.borrow().as_raw(), sort.as_raw(), i as u32 as u64)
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` representing the given unsigned integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    ///
    /// For a code example, see [`BV::new()`](struct.BV.html#method.new).
    pub fn from_u32(btor: R, u: u32, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value_uint64(btor.borrow().as_raw(), sort.as_raw(), u as u64)
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` representing the given signed integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_i64(btor: R, i: i64, width: u32) -> Self {
        let low_bits = (i & 0xFFFF_FFFF) as i32;
        let high_bits = (i >> 32) as i32;
        if width <= 32 {
            Self::from_i32(btor, low_bits, width)
        } else {
            let bv64 = Self::from_i32(btor.clone(), high_bits, 32)
                .concat(&Self::from_i32(btor, low_bits, 32));
            if width < 64 {
                bv64.slice(width - 1, 0)
            } else if width == 64 {
                bv64
            } else {
                bv64.sext(width - 64)
            }
        }
    }

    /// Create a new constant `BV` representing the given unsigned integer.
    /// The new `BV` will have the width `width`, which must not be 0.
    pub fn from_u64(btor: R, u: u64, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_value_uint64(btor.borrow().as_raw(), sort.as_raw(), u) },
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
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    /// let zero = BV::zero(btor.clone(), 8);
    /// assert_eq!(zero.as_u64().unwrap(), 0);
    /// ```
    pub fn zero(btor: R, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_zero(btor.borrow().as_raw(), sort.as_raw()) },
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
    pub fn one(btor: R, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_one(btor.borrow().as_raw(), sort.as_raw()) },
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
    pub fn ones(btor: R, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        Self {
            node: unsafe { bitwuzla_mk_bv_ones(btor.borrow().as_raw(), sort.as_raw()) },
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
        let sort = Sort::bitvector(btor.clone(), bits.len() as u32);
        let cstring = CString::new(bits).unwrap();
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value(
                    btor.borrow().as_raw(),
                    sort.as_raw(),
                    cstring.as_ptr(),
                    BITWUZLA_BV_BASE_BIN,
                )
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` from the given string `num` representing a
    /// (signed) decimal number. The new `BV` will have the width `width`, which
    /// must not be 0.
    pub fn from_dec_str(btor: R, num: &str, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        let cstring = CString::new(num).unwrap();
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value(
                    btor.borrow().as_raw(),
                    sort.as_raw(),
                    cstring.as_ptr() as *const c_char,
                    BITWUZLA_BV_BASE_DEC,
                )
            },
            btor, // out of order so it can be used above but moved in here
        }
    }

    /// Create a new constant `BV` from the given string `num` representing a
    /// hexadecimal number. The new `BV` will have the width `width`, which must
    /// not be 0.
    pub fn from_hex_str(btor: R, num: &str, width: u32) -> Self {
        let sort = Sort::bitvector(btor.clone(), width);
        let cstring = CString::new(num).unwrap();
        Self {
            node: unsafe {
                bitwuzla_mk_bv_value(
                    btor.borrow().as_raw(),
                    sort.as_raw(),
                    cstring.as_ptr() as *const c_char,
                    BITWUZLA_BV_BASE_HEX,
                )
            },
            btor, // out of order so it can be used above but moved in here
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
            /*
            #[repr(C)]
            pub struct BzlaBitVector {
                _unused: [u8; 0],
            }
            extern "C" {
                // fn bzla_bv_to_uint64(bv: *const BzlaBitVector) -> u64;
                // fn bzla_bv_get_width(bv: *const BzlaBitVector) -> u32;
                fn print_fmt_bv_model_btor(
                    bzla: *mut bitwuzla_sys::Bitwuzla,
                    base: u32,
                    assignment: *const BzlaBitVector,
                    file: *const libc::FILE,
                );
                fn bzla_model_get_bv(
                    bzla: *mut bitwuzla_sys::Bitwuzla,
                    exp: *const BitwuzlaTerm,
                ) -> *const BzlaBitVector;
            }
            let width = self.get_width();
            */

            // let raw = unsafe { bitwuzla_get_bv_value(self.btor.borrow().as_raw(), self.node) };
            // let cstr = unsafe { CStr::from_ptr(raw) };
            // let string = cstr.to_str().unwrap().to_owned();
            // Some(string)
            unsafe {
                let tmpfile: *mut libc::FILE = libc::tmpfile();
                assert!(!tmpfile.is_null());
                let format = CString::new("smt2").unwrap();
                // Write the data to `tmpfile`
                bitwuzla_term_dump(self.node, format.as_ptr(), tmpfile);
                // Seek to the end of `tmpfile`
                assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
                // Get the length of `tmpfile`
                let length = libc::ftell(tmpfile);
                assert!(length >= 0);
                // Seek back to the beginning of `tmpfile`
                assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
                let mut buffer = Vec::with_capacity(length as usize);
                libc::fread(
                    buffer.as_mut_ptr() as *mut c_void,
                    1,
                    length as usize,
                    tmpfile,
                );
                buffer.set_len(length as usize);
                let string = String::from_utf8_unchecked(buffer);
                libc::fclose(tmpfile);
                assert!(string.starts_with("#b"));
                let string = string[2 ..].to_string();
                Some(string)
            }
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
        let btor = self.btor.borrow();
        use crate::option::{BtorOption, NumberFormat};
        // Workaround for https://github.com/boolector/boolector/issues/79:
        // set OUTPUT_NUMBER_FORMAT to binary just for this call, restore old
        // value on method exit
        let old_output_format =
            unsafe { bitwuzla_get_option(btor.as_raw(), BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT) };
        btor.set_opt(BtorOption::OutputNumberFormat(NumberFormat::Binary));

        btor.timeout_state.restart_timer();

        let solution = BVSolution::from_raw(unsafe {
            bitwuzla_get_bv_value(self.btor.borrow().as_raw(), self.node)
        });

        // restore the old value of the OUTPUT_NUMBER_FORMAT setting
        unsafe {
            bitwuzla_set_option(
                btor.as_raw(),
                BITWUZLA_OPT_OUTPUT_NUMBER_FORMAT,
                old_output_format,
            )
        };

        solution
    }

    /// Get the `Btor` which this `BV` belongs to
    pub fn get_btor(&self) -> R {
        self.btor.clone()
    }

    /// Get the id of the `BV`
    pub fn get_id(&self) -> i32 {
        todo!()
        // unsafe { bitwuzla_get_node_id(self.btor.borrow().as_raw(), self.node) }
    }

    /// Get the bitwidth of the `BV`
    pub fn get_width(&self) -> u32 {
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
    pub fn set_symbol(&mut self, symbol: Option<&str>) {
        match symbol {
            None => unsafe { bitwuzla_term_set_symbol(self.node, std::ptr::null()) },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_term_set_symbol(self.node, symbol) }
            },
        }
    }

    /// Does the `BV` have a constant value?
    ///
    /// # Examples
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // This `BV` is constant
    /// let five = BV::from_u32(btor.clone(), 5, 8);
    /// assert!(five.is_const());
    ///
    /// // This `BV` is not constant
    /// let unconstrained = BV::new(btor.clone(), 8, Some("foo"));
    /// assert!(!unconstrained.is_const());
    ///
    /// // 5 + [unconstrained] is also not constant
    /// let sum = five.add(&unconstrained);
    /// assert!(!sum.is_const());
    ///
    /// // But 5 + 5 is constant
    /// let sum = five.add(&five);
    /// assert!(sum.is_const());
    /// ```
    pub fn is_const(&self) -> bool {
        unsafe { bitwuzla_term_is_value(self.node) }
    }

    /// Does `self` have the same width as `other`?
    pub fn has_same_width(&self, other: &Self) -> bool {
        unsafe { bitwuzla_term_is_equal_sort(self.node, other.node) }
    }

    /// Assert that `self == 1`.
    ///
    /// `self` must have bitwidth 1.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::Incremental(true));
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // Create an unconstrained `BV`
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // (you may prefer this alternate style for assertions)
    /// BV::assert(&bv.ugt(&BV::from_u32(btor.clone(), 3, 8)));
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

    /// Assume that the given node == 1.
    /// Assumptions are identical to assertions except that they are discarded
    /// after each call to `Btor::sat()`.
    ///
    /// Requires incremental usage to be enabled via
    /// [`Btor::set_opt()`](struct.Btor.html#method.set_opt).
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::Incremental(true));
    /// std::thread::sleep(std::time::Duration::from_secs(2));
    ///
    /// // Create an unconstrained `BV`
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // Assert that it must be greater than `3`
    /// bv.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // The state is satisfiable
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    ///
    /// // Temporarily assume that the `BV` is less than `2`
    /// bv.ult(&BV::from_u32(btor.clone(), 2, 8)).assume();
    ///
    /// // The state is now unsatisfiable
    /// assert_eq!(btor.sat(), SolverResult::Unsat);
    ///
    /// // The assumption only lasts until the next `sat()`
    /// // call, so it has been discarded now
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// ```
    pub fn assume(&self) {
        unsafe { bitwuzla_assume(self.btor.borrow().as_raw(), self.node) }
    }

    /// Returns true if this node is an assumption that forced the input formula
    /// to become unsatisfiable.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::Incremental(true));
    ///
    /// // Create an unconstrained `BV` and assert that it is greater
    /// // than `3`; the state is satisfiable
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    /// bv.ugt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    ///
    /// // Temporarily assume that the `BV` is less than `2`
    /// let assumption = bv.ult(&BV::from_u32(btor.clone(), 2, 8));
    /// assumption.assume();
    ///
    /// // The state is now unsatisfiable, and `assumption` is a
    /// // failed assumption
    /// assert_eq!(btor.sat(), SolverResult::Unsat);
    /// assert!(assumption.is_failed_assumption());
    /// ```
    pub fn is_failed_assumption(&self) -> bool {
        unsafe { bitwuzla_is_unsat_assumption(self.btor.borrow().as_raw(), self.node) }
    }

    binop!(
        /// Bitvector equality. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => _eq, BITWUZLA_KIND_EQUAL
    );
    binop!(
        /// Bitvector inequality. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
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

    binop!(
        /// Unsigned greater than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ugt, BITWUZLA_KIND_BV_UGT
    );
    binop!(
        /// Unsigned greater than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ugte, BITWUZLA_KIND_BV_UGE
    );
    binop!(
        /// Signed greater than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => sgt, BITWUZLA_KIND_BV_SGT
    );
    binop!(
        /// Signed greater than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => sgte, BITWUZLA_KIND_BV_SGE
    );
    binop!(
        /// Unsigned less than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ult, BITWUZLA_KIND_BV_ULT
    );
    binop!(
        /// Unsigned less than or equal. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => ulte, BITWUZLA_KIND_BV_ULE
    );
    binop!(
        /// Signed less than. `self` and `other` must have the same bitwidth.
        /// Resulting `BV` will have bitwidth 1.
        => slt, BITWUZLA_KIND_BV_SLT
    );
    binop!(
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
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // Create an 8-bit `BV` with value `3`
    /// let bv = BV::from_u32(btor.clone(), 3, 8);
    ///
    /// // Zero-extend by 56 bits
    /// let extended = bv.uext(56);
    ///
    /// // Resulting `BV` is 64 bits and has value `3`
    /// assert_eq!(extended.get_width(), 64);
    /// assert_eq!(extended.as_u64().unwrap(), 3);
    /// ```
    pub fn uext(&self, n: u32) -> Self {
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_BV_ZERO_EXTEND,
                    self.node,
                    n,
                )
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
    /// let extended = bv.sext(56);
    ///
    /// // Resulting `BV` is 64 bits and has value `-3`
    /// assert_eq!(extended.get_width(), 64);
    /// assert_eq!(extended.as_u64().unwrap() as i64, -3);
    /// ```
    pub fn sext(&self, n: u32) -> Self {
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_BV_SIGN_EXTEND,
                    self.node,
                    n,
                )
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
    /// let slice = bv.slice(4, 1);
    ///
    /// // Resulting slice has width `4` and value `"0010"`
    /// assert_eq!(slice.get_width(), 4);
    /// assert_eq!(slice.as_binary_str().unwrap(), "0010");
    pub fn slice(&self, high: u32, low: u32) -> Self {
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
                bitwuzla_mk_term1_indexed2(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_BV_EXTRACT,
                    self.node,
                    high,
                    low,
                )
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
        /// let result = ones.concat(&one);
        /// assert_eq!(result.get_width(), 16);
        /// assert_eq!(result.as_binary_str().unwrap(), "1111111100000001");
        ///
        /// // Concatenate in the other order
        /// let result = one.concat(&ones);
        /// assert_eq!(result.get_width(), 16);
        /// assert_eq!(result.as_binary_str().unwrap(), "0000000111111111");
        /// ```
        => concat, BITWUZLA_KIND_BV_CONCAT
    );

    /// Concatenate the `BV` with itself `n` times
    pub fn repeat(&self, n: u32) -> Self {
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term1_indexed1(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_BV_REPEAT,
                    self.node,
                    n,
                )
            },
        }
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

    /// Create an if-then-else `BV` node.
    /// If `self` is true, then `truebv` is returned, else `falsebv` is returned.
    ///
    /// `self` must have bitwidth 1.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Btor, BV, SolverResult};
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
    /// let _y = BV::cond_bv(&cond, &five, &one);
    ///
    /// // Now assert that `x < 7`
    /// x.ult(&BV::from_u32(btor.clone(), 7, 8)).assert();
    ///
    /// // As a result, `y` must be `1`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// assert_eq!(y.get_a_solution().as_u64().unwrap(), 1);
    /// ```
    pub fn cond_bv(&self, truebv: &Self, falsebv: &Self) -> Self {
        assert_eq!(
            self.get_width(),
            1,
            "cond_bv: self must have bitwidth 1; got {}",
            self.get_width()
        );
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    self.btor.borrow().as_raw(),
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
        assert_eq!(
            self.get_width(),
            1,
            "cond_array: self must have bitwidth 1; got {}",
            self.get_width()
        );
        Array {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_ITE,
                    self.node,
                    true_array.node,
                    false_array.node,
                )
            },
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Clone for BV<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            /*
            node: unsafe {
                bitwuzla_copy(self.btor.borrow().as_raw(), self.node) // not an actual copy, just incrementing the refcount properly
            },
            */
            node: self.node,
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Drop for BV<R> {
    fn drop(&mut self) {
        // Actually releasing here seems to expose some UAF bugs in boolector
        // Instead, we just rely on release_all when dropping the Btor
        // unsafe { bitwuzla_release(self.btor.borrow().as_raw(), self.node) }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for BV<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const MAX_LENGTH: i64 = 2000; // If the text representation of the `BV` exceeds this length, subsitute a placeholder instead
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            let format = CString::new("smt2").unwrap();
            // Write the data to `tmpfile`
            bitwuzla_term_dump(self.node, format.as_ptr(), tmpfile);
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let retval = if length > MAX_LENGTH {
                write!(f, "<output too large to display>")
            } else {
                let mut buffer = Vec::with_capacity(length as usize);
                libc::fread(
                    buffer.as_mut_ptr() as *mut c_void,
                    1,
                    length as usize,
                    tmpfile,
                );
                buffer.set_len(length as usize);
                let string = String::from_utf8_unchecked(buffer);
                write!(f, "{}", string)
            };
            libc::fclose(tmpfile);
            retval
        }
    }
}

/// An `Array` in bitwuzla is really just a map from `BV`s to `BV`s.
///
/// Like `BV`, `Array` is generic in the `Btor` reference type.
/// For instance, you could use `Array<Rc<Btor>>` for single-threaded applications,
/// or `Array<Arc<Btor>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct Array<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: *const BitwuzlaTerm,
}

// According to
// https://groups.google.com/forum/#!msg/bitwuzla/itYGgJxU3mY/AC2O0898BAAJ,
// the bitwuzla library is thread-safe, meaning `*mut BitwuzlaTerm` can be
// both `Send` and `Sync`.
// So as long as `R` is `Send` and/or `Sync`, we can mark `Array` as `Send`
// and/or `Sync` respectively.
unsafe impl<R: Borrow<Bitwuzla> + Clone + Send> Send for Array<R> {}
unsafe impl<R: Borrow<Bitwuzla> + Clone + Sync> Sync for Array<R> {}

impl<R: Borrow<Bitwuzla> + Clone> Array<R> {
    /// Create a new `Array` which maps `BV`s of width `index_width` to `BV`s of
    /// width `element_width`. All values in the `Array` will be unconstrained.
    ///
    /// The `symbol`, if present, will be used to identify the `Array` when printing
    /// a model or dumping to file. It must be unique if it is present.
    ///
    /// Both `index_width` and `element_width` must not be 0.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Array, Btor, BV};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    ///
    /// // `arr` is an `Array` which maps 8-bit values to 8-bit values
    /// let arr = Array::new(btor.clone(), 8, 8, Some("arr"));
    ///
    /// // Write the value `3` to array index `7`
    /// let three = BV::from_u32(btor.clone(), 3, 8);
    /// let seven = BV::from_u32(btor.clone(), 7, 8);
    /// let arr2 = arr.write(&seven, &three);
    ///
    /// // Read back out the resulting value
    /// let read_bv = arr2.read(&seven);
    ///
    /// // should be the value `3`
    /// assert_eq!(read_bv.as_u64().unwrap(), 3);
    /// ```
    pub fn new(btor: R, index_width: u32, element_width: u32, symbol: Option<&str>) -> Self {
        todo!()
        /*
        let index_sort = Sort::bitvector(btor.clone(), index_width);
        let element_sort = Sort::bitvector(btor.clone(), element_width);
        let array_sort = Sort::array(btor.clone(), &index_sort, &element_sort);
        let node = match symbol {
            None => unsafe {
                bitwuzla_array(
                    btor.borrow().as_raw(),
                    array_sort.as_raw(),
                    std::ptr::null(),
                )
            },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const c_char;
                unsafe { bitwuzla_array(btor.borrow().as_raw(), array_sort.as_raw(), symbol) }
            },
        };
        Self { btor, node }
        */
    }

    /// Create a new `Array` which maps `BV`s of width `index_width` to `BV`s of
    /// width `element_width`. The `Array` will be initialized so that all
    /// indices map to the same constant value `val`.
    ///
    /// Both `index_width` and `element_width` must not be 0.
    ///
    /// # Example
    ///
    /// ```
    /// # use bitwuzla::{Array, Btor, BV, SolverResult};
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    /// btor.set_opt(BtorOption::Incremental(true));
    ///
    /// // `arr` is an `Array` which maps 8-bit values to 8-bit values.
    /// // It is initialized such that all entries are the constant `42`.
    /// let fortytwo = BV::from_u32(btor.clone(), 42, 8);
    /// let arr = Array::new_initialized(btor.clone(), 8, 8, &fortytwo);
    ///
    /// // Reading the value at any index should produce `42`.
    /// let read_bv = arr.read(&BV::from_u32(btor.clone(), 61, 8));
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// assert_eq!(read_bv.get_a_solution().as_u64().unwrap(), 42);
    ///
    /// // Write the value `3` to array index `7`
    /// let three = BV::from_u32(btor.clone(), 3, 8);
    /// let seven = BV::from_u32(btor.clone(), 7, 8);
    /// let arr2 = arr.write(&seven, &three);
    ///
    /// // Read back out the value at index `7`. It should be `3`.
    /// let read_bv = arr2.read(&seven);
    /// assert_eq!(read_bv.as_u64().unwrap(), 3);
    ///
    /// // Reading the value at any other index should still produce `42`.
    /// let read_bv = arr2.read(&BV::from_u32(btor.clone(), 99, 8));
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// //assert_eq!(read_bv.get_a_solution().as_u64().unwrap(), 42);
    /// ```
    pub fn new_initialized(btor: R, index_width: u32, element_width: u32, val: &BV<R>) -> Self {
        let index_sort = Sort::bitvector(btor.clone(), index_width);
        let element_sort = Sort::bitvector(btor.clone(), element_width);
        let array_sort = Sort::array(btor.clone(), &index_sort, &element_sort);
        let node = unsafe {
            bitwuzla_mk_const_array(btor.borrow().as_raw(), array_sort.as_raw(), val.node)
        };
        Self { btor, node }
    }

    /// Get the bitwidth of the index type of the `Array`
    pub fn get_index_width(&self) -> u32 {
        unsafe {
            let sort = bitwuzla_term_array_get_index_sort(self.node);
            // TODO: do we know if the sort is actually a bv?
            bitwuzla_sort_bv_get_size(sort)
        }
    }

    /// Get the bitwidth of the element type of the `Array`
    pub fn get_element_width(&self) -> u32 {
        unsafe {
            let sort = bitwuzla_term_array_get_element_sort(self.node);
            bitwuzla_sort_bv_get_size(sort)
        }
    }

    /// Get the symbol of the `Array`, if one was assigned
    pub fn get_symbol(&self) -> Option<&str> {
        let raw = unsafe { bitwuzla_term_get_symbol(self.node) };
        if raw.is_null() {
            None
        } else {
            let cstr = unsafe { CStr::from_ptr(raw) };
            Some(cstr.to_str().unwrap())
        }
    }

    /// Does the `Array` have a constant value?
    pub fn is_const(&self) -> bool {
        unsafe { bitwuzla_term_is_const(self.node) }
    }

    /// Does `self` have the same index and element widths as `other`?
    pub fn has_same_widths(&self, other: &Self) -> bool {
        unsafe { bitwuzla_term_is_equal_sort(self.node, other.node) }
    }

    binop!(
        /// Array equality. `self` and `other` must have the same index and element widths.
        => _eq, BITWUZLA_KIND_EQUAL
    );
    binop!(
        /// Array inequality. `self` and `other` must have the same index and element widths.
        => _ne, BITWUZLA_KIND_DISTINCT
    );

    /// Array read: get the value in the `Array` at the given `index`
    pub fn read(&self, index: &BV<R>) -> BV<R> {
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term2(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_ARRAY_SELECT,
                    self.node,
                    index.node,
                )
            },
        }
    }

    /// Array write: return a new `Array` which has `value` at position `index`,
    /// and all other elements unchanged.
    pub fn write(&self, index: &BV<R>, value: &BV<R>) -> Self {
        Self {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term3(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_ARRAY_STORE,
                    self.node,
                    index.node,
                    value.node,
                )
            },
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Clone for Array<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            node: self.node,
            // node: unsafe {
            //     bitwuzla_copy(self.btor.borrow().as_raw(), self.node) // not an actual copy, just incrementing the refcount properly
            // },
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Drop for Array<R> {
    fn drop(&mut self) {
        // Actually releasing here seems to expose some UAF bugs in bitwuzla
        // Instead, we just rely on release_all when dropping the Btor
        // unsafe { bitwuzla_release(self.btor.borrow().as_raw(), self.node) }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for Array<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const MAX_LENGTH: i64 = 2000; // If the text representation of the `Array` exceeds this length, subsitute a placeholder instead
        unsafe {
            let tmpfile: *mut libc::FILE = libc::tmpfile();
            if tmpfile.is_null() {
                panic!("Failed to create a temp file");
            }
            let format = CString::new("smt2").unwrap();
            // Write the data to `tmpfile`
            bitwuzla_term_dump(self.node, format.as_ptr(), tmpfile);
            // Seek to the end of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_END), 0);
            // Get the length of `tmpfile`
            let length = libc::ftell(tmpfile);
            if length < 0 {
                panic!("ftell() returned a negative value");
            }
            // Seek back to the beginning of `tmpfile`
            assert_eq!(libc::fseek(tmpfile, 0, libc::SEEK_SET), 0);
            let retval = if length > MAX_LENGTH {
                write!(f, "<output too large to display>")
            } else {
                let mut buffer = Vec::with_capacity(length as usize);
                libc::fread(
                    buffer.as_mut_ptr() as *mut c_void,
                    1,
                    length as usize,
                    tmpfile,
                );
                buffer.set_len(length as usize);
                let string = String::from_utf8_unchecked(buffer);
                write!(f, "{}", string)
            };
            libc::fclose(tmpfile);
            retval
        }
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
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Btor::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // `bv` starts as an unconstrained 8-bit value
    /// let bv = BV::new(btor.clone(), 8, Some("foo"));
    ///
    /// // assert that the first two digits of `bv` are 0
    /// let mask = BV::from_u32(btor.clone(), 0b11000000, 8);
    /// let zero = BV::zero(btor.clone(), 8);
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
