import InfoGeometry.Clifford.ChevalleySpinorBlueprint
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Annihilator isotropy for split exterior spinors

This is the first pure-spinor layer.  It records the algebraic direction that
is needed later for maximal isotropic/pure-spinor comparisons: the annihilator
of a nonzero exterior spinor is isotropic for the split quadratic polar form.
Maximality and the converse correspondence are deliberately separate.
-/

namespace InfoGeometry.Clifford

noncomputable section

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

def annihilator (φ : SpinorSpace L) : Set (SplitSpace L) :=
  {x | spinorAction x φ = 0}

def IsIsotropic (S : Set (SplitSpace L)) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S →
    QuadraticMap.polar (Qsplit L) x y = 0

def IsMaximalIsotropic (S : Set (SplitSpace L)) : Prop :=
  IsIsotropic S ∧
    ∀ T, IsIsotropic T → S ⊆ T → T ⊆ S

def IsPureSpinor (φ : SpinorSpace L) : Prop :=
  φ ≠ 0 ∧ IsMaximalIsotropic (annihilator φ)

theorem spinorAction_add (x y : SplitSpace L) (φ : SpinorSpace L) :
    spinorAction (x + y) φ = spinorAction x φ + spinorAction y φ := by
  simp [spinorAction, extAction, intAction, add_mul]
  abel

theorem annihilator_add {φ : SpinorSpace L} {x y : SplitSpace L}
    (hx : x ∈ annihilator φ) (hy : y ∈ annihilator φ) :
    x + y ∈ annihilator φ := by
  change spinorAction (x + y) φ = 0
  change spinorAction x φ = 0 at hx
  change spinorAction y φ = 0 at hy
  rw [spinorAction_add]
  rw [hx, hy, add_zero]

theorem annihilator_isotropic {φ : SpinorSpace L} (hφ : φ ≠ 0)
    {x y : SplitSpace L} (hx : x ∈ annihilator φ) (hy : y ∈ annihilator φ) :
    QuadraticMap.polar (Qsplit L) x y = 0 := by
  have hsum : x + y ∈ annihilator φ := annihilator_add hx hy
  have hsq := spinorAction_sq (L := L) (x + y) φ
  change spinorAction (x + y) φ = 0 at hsum
  rw [hsum] at hsq
  have hscalar : (Qsplit L (x + y)) • φ = 0 := by
    simpa [Algebra.smul_def] using hsq.symm
  have hq : Qsplit L (x + y) = 0 := by
    exact (smul_eq_zero.mp hscalar).resolve_right hφ
  have hxq := spinorAction_sq (L := L) x φ
  change spinorAction x φ = 0 at hx
  rw [hx] at hxq
  have hxscalar : (Qsplit L x) • φ = 0 := by
    simpa [Algebra.smul_def] using hxq.symm
  have hxzero : Qsplit L x = 0 :=
    (smul_eq_zero.mp hxscalar).resolve_right hφ
  have hyq := spinorAction_sq (L := L) y φ
  change spinorAction y φ = 0 at hy
  rw [hy] at hyq
  have hyscalar : (Qsplit L y) • φ = 0 := by
    simpa [Algebra.smul_def] using hyq.symm
  have hyzero : Qsplit L y = 0 :=
    (smul_eq_zero.mp hyscalar).resolve_right hφ
  simp [QuadraticMap.polar, hq, hxzero, hyzero]

theorem pureSpinor_annihilator_isotropic {φ : SpinorSpace L}
    (hφ : IsPureSpinor φ) :
    IsIsotropic (annihilator φ) :=
  hφ.2.1

end

end InfoGeometry.Clifford
