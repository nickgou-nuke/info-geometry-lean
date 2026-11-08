import InfoGeometry.Lie.SplitOctonionAxialCartanFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllCrossChannel

/-!
# Cartan transport of the native Peirce/chiral frame

This owner transports the already-proved idempotent and square-zero channels
through the closed traceless axial Cartan automorphism.  It does not assert a
general exponential flow on the nonassociative carrier.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionPeirceCartanTransport

open InfoGeometry.Lie.SplitOctonionAxialCartanFlow
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev Carrier := InfoGeometry.Canonical.ZornMatrix ℝ

def transported (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0)
    (t : ℝ) (x : Carrier) : Carrier :=
  axialCartanFlow k t x

theorem transported_mul
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ)
    (x y : Carrier) :
    transported k hk t (x * y) =
      transported k hk t x * transported k hk t y := by
  exact axialCartanFlow_map_mul k hk t x y

theorem transported_uPlus_sq
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    transported k hk t uPlus * transported k hk t uPlus =
      transported k hk t uPlus := by
  rw [← transported_mul k hk t uPlus uPlus, uPlus_sq]

theorem transported_uMinus_sq
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    transported k hk t uMinus * transported k hk t uMinus =
      transported k hk t uMinus := by
  rw [← transported_mul k hk t uMinus uMinus, uMinus_sq]

theorem transported_uPlus_mul_uMinus
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    transported k hk t uPlus * transported k hk t uMinus = 0 := by
  rw [← transported_mul k hk t uPlus uMinus, uPlus_mul_uMinus]
  simpa [transported] using (axialCartanFlow k t).map_zero

theorem transported_uMinus_mul_uPlus
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) :
    transported k hk t uMinus * transported k hk t uPlus = 0 := by
  rw [← transported_mul k hk t uMinus uPlus, uMinus_mul_uPlus]
  simpa [transported] using (axialCartanFlow k t).map_zero

theorem transported_rootPlus_sq
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (i : Fin 3) :
    transported k hk t (rootPlus i) * transported k hk t (rootPlus i) = 0 := by
  rw [← transported_mul k hk t (rootPlus i) (rootPlus i), rootPlus_sq]
  simpa [transported] using (axialCartanFlow k t).map_zero

theorem transported_rootMinus_sq
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : ℝ) (i : Fin 3) :
    transported k hk t (rootMinus i) * transported k hk t (rootMinus i) = 0 := by
  rw [← transported_mul k hk t (rootMinus i) (rootMinus i), rootMinus_sq]
  simpa [transported] using (axialCartanFlow k t).map_zero

end InfoGeometry.Lie.SplitOctonionPeirceCartanTransport
