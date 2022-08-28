use crate::btor::Bitwuzla;
use crate::sort::Sort;
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::{c_char, c_void};

/// A floating-point object: that is, a single symbolic value, consisting of a
/// symbolic exponent, significand component, and sign component.
///
/// This is generic in the `Bitwuzla` reference type.
/// For instance, you could use `FP<Rc<Bitwuzla>>` for single-threaded applications,
/// or `FP<Arc<Bitwuzla>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct FP<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: *const BitwuzlaTerm,
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
    /// # use bitwuzla::option::{BtorOption, ModelGen};
    /// # use std::rc::Rc;
    /// let btor = Rc::new(Bitwuzla::new());
    /// btor.set_opt(BtorOption::ModelGen(ModelGen::All));
    ///
    /// // An 8-bit unconstrained `BV` with the symbol "foo"
    /// let fp = FP::new(btor.clone(), 8, 23, Some("foo"));
    /// assert_eq!(format!("{:?}", fp), "(declare-const foo (_ FloatingPoint 8 23))");
    ///
    /// // Assert that it must be greater than `3`
    /// // fp.gt(&BV::from_u32(btor.clone(), 3, 8)).assert();
    ///
    /// // Now any solution must give it a value greater than `3`
    /// assert_eq!(btor.sat(), SolverResult::Sat);
    /// // let solution = fp.get_a_solution().as_u64().unwrap();
    /// // assert!(solution > 3);
    /// ```
    pub fn new(btor: R, exp_width: u32, sig_width: u32, symbol: Option<&str>) -> Self {
        let sort = Sort::fp(btor.clone(), exp_width, sig_width);
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
        let format = CString::new("smt2").unwrap();
        let string = crate::util::tmp_file_to_string(
            |tmpfile| unsafe {
                bitwuzla_term_dump(self.node, format.as_ptr(), tmpfile);
            },
            true,
        )
        .trim()
        .to_owned();
        write!(f, "{}", string)
    }
}
