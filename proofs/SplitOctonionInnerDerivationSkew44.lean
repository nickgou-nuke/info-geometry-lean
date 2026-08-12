import Mathlib
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionInnerDerivation
import proofs.SplitOctonionDerivationSkew44

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionInnerDerivation
open Quaternion

lemma innerDeriv_skew_adjoint (x y u v : SplitOct) :
  splitBilinear (innerDeriv x y u) v + splitBilinear u (innerDeriv x y v) = 0 := by
  exact OctDerivation.derivation_is_skew_adjoint (mkInnerDeriv x y) u v
