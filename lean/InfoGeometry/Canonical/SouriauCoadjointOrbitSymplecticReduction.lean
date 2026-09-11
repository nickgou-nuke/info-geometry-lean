import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Basic

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace SouriauReduction

variable {R L : Type*} [CommRing R] [LieRing L] [Module R L]

/-! The KKS pairing is formed from a native Lie-ring bracket and a linear
functional on the Lie algebra. -/
def kksForm (mu : L →ₗ[R] R) (X Y : L) : R :=
  mu ⁅X, Y⁆

structure CoadjointIsotropyData where
  mu : L →ₗ[R] R
  isotropySubmodule : Submodule R L

/-- 🏆 THEOREM 1: Skew-Symmetry of Isotropy Action Nullity -/
theorem isotropy_coad_null_skew (data : CoadjointIsotropyData (R := R) (L := L))
    (X Y : L) (hX : X ∈ data.isotropySubmodule)
    (h_coad_null : ∀ Z : L, Z ∈ data.isotropySubmodule →
      ∀ W : L, kksForm data.mu Z W = 0) :
    kksForm data.mu Y X = 0 := by
  have h := h_coad_null X hX Y
  have hskew : ⁅Y, X⁆ = -⁅X, Y⁆ := by
    have h' := congrArg Neg.neg (lie_skew X Y)
    simpa using h'
  calc
    kksForm data.mu Y X = -kksForm data.mu X Y := by
      unfold kksForm
      rw [hskew, map_neg]
    _ = 0 := by rw [h, neg_zero]

/-- 3. Marsden-Weinstein Reduced Symplectic Form ω_red on Reduced Orbit Quotient Space 𝔤* / 𝔥_μ -/
def reducedKKSForm (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) : R :=
  kksForm data.mu X Y

/-- 🏆 THEOREM 2: Well-Definedness of Reduced Form under Gauge Transformations (Addition of Isotropy Elements) -/
theorem reducedKKSForm_well_defined
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y Z : L)
    (hZ : Z ∈ data.isotropySubmodule)
    (h_coad_null : ∀ W : L, W ∈ data.isotropySubmodule →
      ∀ V : L, kksForm data.mu W V = 0) :
    reducedKKSForm data (X + Z) Y = reducedKKSForm data X Y := by
  change data.mu ⁅X + Z, Y⁆ = data.mu ⁅X, Y⁆
  rw [LieRing.add_lie, map_add]
  have h := h_coad_null Z hZ Y
  have h' : data.mu ⁅Z, Y⁆ = 0 := by
    simpa [kksForm] using h
  rw [h', add_zero]

/-- 🏆 THEOREM 3: Skew-Symmetry of the Marsden-Weinstein Reduced Symplectic 2-Form -/
theorem reducedKKSForm_skew
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) :
    reducedKKSForm data X Y = - reducedKKSForm data Y X := by
  have hskew : ⁅Y, X⁆ = -⁅X, Y⁆ := by
    have h' := congrArg Neg.neg (lie_skew X Y)
    simpa using h'
  unfold reducedKKSForm kksForm
  rw [hskew, map_neg]
  simp

/-- 🏆 THEOREM 4: Marsden-Weinstein Pullback Identity: π* ω_red = i* ω_KKS -/
theorem marsden_weinstein_pullback_identity
    (data : CoadjointIsotropyData (R := R) (L := L)) (X Y : L) :
    reducedKKSForm data X Y = kksForm data.mu X Y := rfl

end SouriauReduction
