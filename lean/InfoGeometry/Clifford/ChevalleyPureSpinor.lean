import InfoGeometry.Clifford.ChevalleySpinorBlueprint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Dual.Lemmas

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

/-! ### The canonical pure-spinor point of the neutral Grassmannian -/

/-- The exterior-Fock action on the scalar vacuum sees only the creation
component. Contraction by a covector annihilates the unit. -/
theorem spinorAction_vacuum (u : L) (f : Dual L) :
    spinorAction (u, f) (1 : SpinorSpace L) =
      CliffordAlgebra.ι (0 : QuadraticForm ℝ L) u := by
  simp [spinorAction, extAction, intAction]

/-- The generator of the zero-form Clifford algebra is injective: under
Mathlib's native Clifford-to-exterior equivalence it is the exterior
generator. -/
theorem zeroCliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι (0 : QuadraticForm ℝ L)) := by
  intro u v huv
  have h := congrArg
    (CliffordAlgebra.equivExterior (0 : QuadraticForm ℝ L)) huv
  have h' : ExteriorAlgebra.ι ℝ u = ExteriorAlgebra.ι ℝ v := by
    simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι] using h
  exact (ExteriorAlgebra.ι_inj ℝ u v).mp h'

/-- The annihilator of the scalar vacuum in the neutral Chevalley model is
exactly the covector summand `0 × L*`. This is an arbitrary-rank theorem. -/
theorem vacuum_annihilator_iff (u : L) (f : Dual L) :
    (u, f) ∈ annihilator (1 : SpinorSpace L) ↔ u = 0 := by
  change spinorAction (u, f) (1 : SpinorSpace L) = 0 ↔ u = 0
  rw [spinorAction_vacuum]
  constructor
  · intro h
    exact zeroCliffordIota_injective (by simpa using h)
  · rintro rfl
    simp

/-- Polarization of the evaluation quadratic form on `L × L*` is the
hyperbolic pairing between the two summands. -/
theorem splitPolar_apply (u : L) (f : Dual L) (v : L) (g : Dual L) :
    QuadraticMap.polar (Qsplit L) (u, f) (v, g) = f v + g u := by
  simp [QuadraticMap.polar, Qsplit, Bsplit]
  ring

/-- The vacuum annihilator is a maximal isotropic subspace of the neutral
quadratic space, provided the dual separates vectors (here expressed by
Mathlib's projectivity hypothesis). -/
theorem vacuum_annihilator_isMaximalIsotropic [Module.Projective ℝ L] :
    IsMaximalIsotropic (annihilator (1 : SpinorSpace L)) := by
  constructor
  · intro x hx y hy
    rcases x with ⟨u, f⟩
    rcases y with ⟨v, g⟩
    have hu := (vacuum_annihilator_iff u f).mp hx
    have hv := (vacuum_annihilator_iff v g).mp hy
    rw [splitPolar_apply, hu, hv]
    simp
  · intro T hT hContain x hx
    rcases x with ⟨u, f⟩
    have hvanish : ∀ g : Dual L, g u = 0 := by
      intro g
      have hdual : ((0 : L), g) ∈ annihilator (1 : SpinorSpace L) :=
        (vacuum_annihilator_iff 0 g).2 rfl
      have h := hT hx (hContain hdual)
      simpa [splitPolar_apply] using h
    have hu : u = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℝ u).mp hvanish
    exact (vacuum_annihilator_iff u f).2 hu

/-- The scalar vacuum is a pure spinor in the full neutral Chevalley model:
its annihilator is the maximal isotropic covector summand. -/
theorem scalarVacuum_isPureSpinor [Module.Projective ℝ L] :
    IsPureSpinor (1 : SpinorSpace L) := by
  exact ⟨one_ne_zero, vacuum_annihilator_isMaximalIsotropic (L := L)⟩

end

end InfoGeometry.Clifford
