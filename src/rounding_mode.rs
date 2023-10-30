use crate::btor::Bitwuzla;
use bitwuzla_sys::*;
use std::borrow::Borrow;
use std::ffi::CString;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub enum RoundingMode {
    Max,
    RNA,
    RNE,
    RTN,
    RTP,
    RTZ,
}

impl RoundingMode {
    pub fn to_node<R: Borrow<Bitwuzla> + Clone>(&self, btor: R) -> RoundingModeNode<R> {
        let rm = match self {
            RoundingMode::Max => BITWUZLA_RM_MAX,
            RoundingMode::RNA => BITWUZLA_RM_RNA,
            RoundingMode::RNE => BITWUZLA_RM_RNE,
            RoundingMode::RTN => BITWUZLA_RM_RTN,
            RoundingMode::RTP => BITWUZLA_RM_RTP,
            RoundingMode::RTZ => BITWUZLA_RM_RTZ,
        };
        let node = unsafe { bitwuzla_mk_rm_value( rm) };
        RoundingModeNode { btor, node }
    }
}

/// A bitvector object: that is, a single symbolic value, consisting of some
/// number of symbolic bits.
///
/// This is generic in the `Bitwuzla` reference type.
/// For instance, you could use `BV<Rc<Bitwuzla>>` for single-threaded applications,
/// or `BV<Arc<Bitwuzla>>` for multi-threaded applications.
#[derive(PartialEq, Eq)]
pub struct RoundingModeNode<R: Borrow<Bitwuzla> + Clone> {
    pub(crate) btor: R,
    pub(crate) node: BitwuzlaTerm,
}

impl<R: Borrow<Bitwuzla> + Clone> RoundingModeNode<R> {}

impl<R: Borrow<Bitwuzla> + Clone> Clone for RoundingModeNode<R> {
    fn clone(&self) -> Self {
        Self {
            btor: self.btor.clone(),
            node: self.node,
        }
    }
}

impl<R: Borrow<Bitwuzla> + Clone> fmt::Debug for RoundingModeNode<R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let format = CString::new("smt2").unwrap();
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
