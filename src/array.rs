use crate::btor::Bitwuzla;
use crate::bv::BV;
use crate::sort::Sort;
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::{CStr, CString};
use std::fmt;

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
        let index_sort = Sort::bitvector(btor.clone(), index_width);
        let element_sort = Sort::bitvector(btor.clone(), element_width);
        let array_sort = Sort::array(btor.clone(), &index_sort, &element_sort);

        let node = match symbol {
            None => unsafe {
                bitwuzla_mk_const(
                    btor.borrow().as_raw(),
                    array_sort.as_raw(),
                    std::ptr::null(),
                )
            },
            Some(symbol) => {
                let cstring = CString::new(symbol).unwrap();
                let symbol = cstring.as_ptr() as *const libc::c_char;
                unsafe { bitwuzla_mk_const(btor.borrow().as_raw(), array_sort.as_raw(), symbol) }
            },
        };
        Self { btor, node }
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

    /// Array equality. `self` and `other` must have the same index and element widths.
    pub fn _eq(&self, other: &Array<R>) -> BV<R> {
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term2(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_EQUAL,
                    self.node,
                    other.node,
                )
            },
        }
    }

    /// Array inequality. `self` and `other` must have the same index and element widths.
    pub fn _ne(&self, other: &Array<R>) -> BV<R> {
        BV {
            btor: self.btor.clone(),
            node: unsafe {
                bitwuzla_mk_term2(
                    self.btor.borrow().as_raw(),
                    BITWUZLA_KIND_DISTINCT,
                    self.node,
                    other.node,
                )
            },
        }
    }

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
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for Array<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let format = CString::new("smt2").unwrap();
        let res = crate::util::tmp_file_to_string(
            |tmpfile| unsafe {
                bitwuzla_term_dump(self.node, format.as_ptr(), tmpfile);
            },
            true,
        );
        write!(f, "{}", res)
    }
}
