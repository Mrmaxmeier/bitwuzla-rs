// We have some methods on `Sort` that we don't use, but still make sense to
// have around for the future
#![allow(dead_code)]

use crate::btor::Bitwuzla;
use bitwuzla_sys::*;
use std::borrow::Borrow;

pub struct Sort<R: Borrow<Bitwuzla> + Clone> {
    btor: R,
    sort: BitwuzlaSort,
}

impl<R: Borrow<Bitwuzla> + Clone> Sort<R> {
    pub(crate) fn from_raw(btor: R, sort: BitwuzlaSort) -> Self {
        Self { btor, sort }
    }

    pub(crate) fn as_raw(&self) -> BitwuzlaSort {
        self.sort
    }

    /// Create a bitvector sort for the given bitwidth.
    /// `width` must not be `0`.
    pub fn bitvector(btor: R, width: u64) -> Self {
        let tm = btor.borrow().tm;
        assert!(width > 0, "bitwuzla: cannot create 0-width bitvector sort");
        Self::from_raw(btor, unsafe { bitwuzla_mk_bv_sort(tm, width) })
    }

    /// Create the Boolean sort.
    ///
    /// In bitwuzla, there is no distinction between Booleans and bitvectors of
    /// bitwidth one, so this is equivalent to `Sort::bitvector(btor, 1)`.
    pub fn bool(btor: R) -> Self {
        let tm = btor.borrow().tm;
        Self::from_raw(btor, unsafe { bitwuzla_mk_bool_sort(tm) })
    }

    /// Create a floating-point sort for the given exponent and significand width.
    /// Bitwuzla supports the following floating-point formats:
    /// - FP_FLOAT16: 5-bit exponent, 11-bit significand
    /// - FP_FLOAT32: 8-bit exponent, 24-bit significand
    /// - FP_FLOAT64: 11-bit exponent, 53-bit significand
    /// - FP_FLOAT128: 15-bit exponent, 113-bit significand
    pub fn fp(btor: R, exp_width: u64, sig_width: u64) -> Self {
        let tm = btor.borrow().tm;
        assert!(
            exp_width > 0,
            "bitwuzla: cannot create 0-exp_width bitvector sort"
        );
        assert!(
            sig_width > 0,
            "bitwuzla: cannot create 0-sig_width bitvector sort"
        );
        Self::from_raw(btor, unsafe {
            bitwuzla_mk_fp_sort(tm, exp_width, sig_width)
        })
    }

    /// Create an array sort. An `Array` in bitwuzla is really just a map
    /// which maps items of the `index` sort to the `element` sort.
    ///
    /// Both the `index` and `element` sorts must be bitvector sorts.
    pub fn array(btor: R, index: &Sort<R>, element: &Sort<R>) -> Self {
        let tm = btor.borrow().tm;
        Self::from_raw(btor, unsafe {
            bitwuzla_mk_array_sort(tm, index.as_raw(), element.as_raw())
        })
    }

    pub fn rounding_mode(btor: R) -> Self {
        let tm = btor.borrow().tm;
        Self::from_raw(btor, unsafe { bitwuzla_mk_rm_sort(tm) })
    }

    /// Is `self` an array sort?
    pub fn is_array_sort(&self) -> bool {
        unsafe { bitwuzla_sort_is_array(self.as_raw()) }
    }

    /// Is `self` a bitvector sort?
    pub fn is_bv_sort(&self) -> bool {
        unsafe { bitwuzla_sort_is_bv(self.as_raw()) }
    }

    /// Is `self` a function sort?
    pub fn is_fun_sort(&self) -> bool {
        unsafe { bitwuzla_sort_is_fun(self.as_raw()) }
    }

    /// Is `self` a function sort?
    pub fn is_rounding_mode_sort(&self) -> bool {
        unsafe { bitwuzla_sort_is_rm(self.as_raw()) }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> Drop for Sort<R> {
    fn drop(&mut self) {
        // unsafe { bitwuzla_release_sort(self.btor.borrow().as_raw(), self.as_raw()) }
    }
}
