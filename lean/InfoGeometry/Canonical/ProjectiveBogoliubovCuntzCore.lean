import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CStarCuntzTensorQuotient

/-!
# Projective Bogoliubov data on a finite Cuntz family

This owner records the algebraic part of the projective-to-gauge mechanism.
It deliberately works with the existing `CStarCuntzFamily` interface: no
unconstructed Cuntz completion or automorphism group is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveBogoliubovCuntzCore

open InfoGeometry.Physics.CStarCuntzTensorQuotient

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

/-- Linear mixing of a finite family by a coefficient matrix. -/
def mix (U : Matrix ι ι ℂ) (s : ι → A) (i : ι) : A :=
  ∑ j, U i j • s j

@[simp] theorem mix_apply (U : Matrix ι ι ℂ) (s : ι → A) (i : ι) :
    mix U s i = ∑ j, U i j • s j :=
  rfl

theorem mix_comp (U V : Matrix ι ι ℂ) (s : ι → A) (i : ι) :
    mix U (mix V s) i = mix (U * V) s i := by
  classical
  simp only [mix, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]

theorem mix_projective_defect
    (U V W : Matrix ι ι ℂ) (c : ℂ) (s : ι → A)
    (h : U * V = c • W) (i : ι) :
    mix U (mix V s) i = c • mix W s i := by
  rw [mix_comp, h]
  simp [mix, Finset.smul_sum, smul_smul]

/-- A level-one Cuntz core matrix unit. -/
def coreUnit (F : CStarCuntzFamily A ι) (i j : ι) : A :=
  F.S i * star (F.S j)

theorem gauge_coreUnit_invariant
    (F : CStarCuntzFamily A ι) (z : ℂ) (hz : star z * z = 1) (i j : ι) :
    (z • F.S i) * star (z • F.S j) = coreUnit F i j := by
  simp only [coreUnit, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hz]
  simp

theorem gauge_coreUnit_invariant_of_unitary_scalar
    (F : CStarCuntzFamily A ι) (z : ℂ) (hz : Complex.normSq z = 1)
    (i j : ι) :
    (z • F.S i) * star (z • F.S j) = coreUnit F i j := by
  apply gauge_coreUnit_invariant F z
  have hnorm : star z * z = (Complex.normSq z : ℂ) := by
    simp [Complex.normSq, Complex.ext_iff, pow_two, mul_comm, mul_left_comm,
      mul_assoc]
  rw [hnorm]
  exact_mod_cast hz

/-! ## Observable readout of the finite Bogoliubov lift -/

/-- Column-convention Bogoliubov mixing, matching
`β_U(S_i) = ∑ j, U j i • S_j`. -/
def mixColumn (U : Matrix ι ι ℂ) (s : ι → A) (i : ι) : A :=
  ∑ j, U j i • s j

def mixedCoreUnit (F : CStarCuntzFamily A ι) (U : Matrix ι ι ℂ)
    (i j : ι) : A :=
  mixColumn U F.S i * star (mixColumn U F.S j)

theorem mixedCoreUnit_expand (F : CStarCuntzFamily A ι)
  (U : Matrix ι ι ℂ) (i j : ι) :
    mixedCoreUnit F U i j =
      ∑ l, ∑ k, (U l i * star (U k j)) • coreUnit F l k := by
  classical
  simp only [mixedCoreUnit, mixColumn, star_sum, star_smul,
    Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
    smul_mul_assoc, mul_smul_comm,
    smul_smul, coreUnit]
  rw [Finset.sum_comm]
  simp [mul_comm]

end InfoGeometry.Canonical.ProjectiveBogoliubovCuntzCore

end noncomputable section
