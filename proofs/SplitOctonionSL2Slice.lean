import proofs.SplitOctonionQuaternionChart

open Quaternion
open SplitOctonion

namespace SplitOctonionSL2Slice

def sliceToOct (a b c d : ℝ) : SplitOct :=
  a • 1 + b • u + c • ell + d • (u * ell)

theorem sliceToOct_mul (a b c d A B C D : ℝ) :
  sliceToOct a b c d * sliceToOct A B C D =
  sliceToOct
    (a*A - b*B + c*C + d*D)
    (a*B + b*A + d*C - c*D)
    (a*C + c*A + d*B - b*D)
    (a*D + d*A + b*C - c*B) := by
  ext1 <;> ext1 <;> simp [sliceToOct, u, ell, star] <;> ring

end SplitOctonionSL2Slice
