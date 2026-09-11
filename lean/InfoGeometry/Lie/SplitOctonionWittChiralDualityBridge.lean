import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionChiralWittSolderingDecomposition

/-!
# Explicit finite-dimensional Witt chiral duality

This owner packages the already-proved coordinate projectors as explicit
linear equivalences.  It proves the finite-dimensional statement
`VMinus ≃ₗ[ℝ] Module.Dual ℝ VPlus`; it does not introduce a bundle or a
global `TM ⊕ T*M` identification.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionWittChiralDualityBridge

open InfoGeometry.Lie.SplitOctonionChiralWittSolderingDecomposition
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge

abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R
abbrev Four := InfoGeometry.Algebra.FiniteSpin.Vec4R

def plusSectionMap : Four →ₗ[ℝ] VPlus :=
  { toFun := fun ξ =>
      ⟨symmSection (ξ 0) (ξ 1) (ξ 2) (ξ 3),
        (mem_VPlus_iff _).2 (kappa_fixes_symmSection (ξ 0) (ξ 1) (ξ 2) (ξ 3))⟩
    map_add' := by
      intro ξ η
      apply Subtype.ext
      ext i
      fin_cases i <;> (dsimp [symmSection]; try ring)
    map_smul' := by
      intro c ξ
      apply Subtype.ext
      ext i
      fin_cases i <;> (dsimp [symmSection]; try ring) }

def minusSectionMap : Four →ₗ[ℝ] VMinus :=
  { toFun := fun ξ =>
      ⟨antiSection (ξ 0) (ξ 1) (ξ 2) (ξ 3),
        (mem_VMinus_iff _).2 (kappa_inverts_antiSection (ξ 0) (ξ 1) (ξ 2) (ξ 3))⟩
    map_add' := by
      intro ξ η
      apply Subtype.ext
      ext i
      fin_cases i <;> (dsimp [antiSection]; try ring)
    map_smul' := by
      intro c ξ
      apply Subtype.ext
      ext i
      fin_cases i <;> (dsimp [antiSection]; try ring) }

def plusRead : VPlus →ₗ[ℝ] Four :=
  { toFun := fun X => ![X.1 0, X.1 1, X.1 2, X.1 3]
    map_add' := by
      intro X Y
      ext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c X
      ext i
      fin_cases i <;> rfl }

def minusRead : VMinus →ₗ[ℝ] Four :=
  { toFun := fun X => ![X.1 0, X.1 1, X.1 2, X.1 3]
    map_add' := by
      intro X Y
      ext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c X
      ext i
      fin_cases i <;> rfl }

@[simp] theorem plusRead_plusSection (ξ : Four) :
    plusRead (plusSectionMap ξ) = ξ := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem minusRead_minusSection (ξ : Four) :
    minusRead (minusSectionMap ξ) = ξ := by
  ext i
  fin_cases i <;> rfl

theorem plusSection_plusRead (X : VPlus) :
    plusSectionMap (plusRead X) = X := by
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · have h := congrFun ((mem_VPlus_iff X.1).mp X.2) 0
    exact h.symm
  · have h := congrFun ((mem_VPlus_iff X.1).mp X.2) 1
    exact h.symm
  · have h := congrFun ((mem_VPlus_iff X.1).mp X.2) 2
    exact h.symm
  · have h := congrFun ((mem_VPlus_iff X.1).mp X.2) 3
    exact h.symm

theorem minusSection_minusRead (X : VMinus) :
    minusSectionMap (minusRead X) = X := by
  apply Subtype.ext
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · have h := congrFun ((mem_VMinus_iff X.1).mp X.2) 0
    exact h.symm
  · have h := congrFun ((mem_VMinus_iff X.1).mp X.2) 1
    exact h.symm
  · have h := congrFun ((mem_VMinus_iff X.1).mp X.2) 2
    exact h.symm
  · have h := congrFun ((mem_VMinus_iff X.1).mp X.2) 3
    exact h.symm

theorem plusSectionMap_bijective : Function.Bijective plusSectionMap := by
  constructor
  · intro ξ η h
    have h' := congrArg plusRead h
    simpa using h'
  · intro X
    exact ⟨plusRead X, plusSection_plusRead X⟩

theorem minusSectionMap_bijective : Function.Bijective minusSectionMap := by
  constructor
  · intro ξ η h
    have h' := congrArg minusRead h
    simpa using h'
  · intro X
    exact ⟨minusRead X, minusSection_minusRead X⟩

def plusEquiv : Four ≃ₗ[ℝ] VPlus :=
  LinearEquiv.ofBijective plusSectionMap plusSectionMap_bijective

def minusEquiv : Four ≃ₗ[ℝ] VMinus :=
  LinearEquiv.ofBijective minusSectionMap minusSectionMap_bijective

@[simp] theorem minusEquiv_symm_apply (X : VMinus) :
    minusEquiv.symm X = minusRead X := by
  apply minusSectionMap_bijective.1
  change minusEquiv (minusEquiv.symm X) = minusSectionMap (minusRead X)
  rw [minusEquiv.apply_symm_apply, minusSection_minusRead]

def dualPlusMap : Module.Dual ℝ Four →ₗ[ℝ] Module.Dual ℝ VPlus :=
  LinearMap.dualMap plusRead

theorem dualPlusMap_bijective : Function.Bijective dualPlusMap := by
  constructor
  · intro f g h
    apply LinearMap.ext
    intro ξ
    have h' := congrArg (fun q : Module.Dual ℝ VPlus => q (plusSectionMap ξ)) h
    have hplus : plusRead (plusSectionMap ξ) = ξ := plusRead_plusSection ξ
    dsimp [dualPlusMap, LinearMap.dualMap_apply] at h'
    rwa [hplus] at h'
  · intro f
    refine ⟨LinearMap.dualMap plusSectionMap f, ?_⟩
    apply LinearMap.ext
    intro X
    dsimp [LinearMap.dualMap_apply]
    have h := congrArg f (plusSection_plusRead X)
    exact h

def dualPlusEquiv : Module.Dual ℝ Four ≃ₗ[ℝ] Module.Dual ℝ VPlus :=
  LinearEquiv.ofBijective dualPlusMap dualPlusMap_bijective

/-- The literal finite-dimensional generalized-geometry duality wire. -/
def wittChiralDuality : VMinus ≃ₗ[ℝ] Module.Dual ℝ VPlus :=
  (minusEquiv.symm.trans wittCovectorDuality).trans dualPlusEquiv

theorem wittChiralDuality_apply (X : VMinus) (Y : VPlus) :
    wittChiralDuality X Y =
      wittCovectorDuality (minusRead X) (plusRead Y) := by
  dsimp [wittChiralDuality, dualPlusEquiv, dualPlusMap, LinearMap.dualMap_apply]
  rw [minusEquiv_symm_apply]

def plusPartMap : Coord →ₗ[ℝ] VPlus :=
  { toFun := fun X =>
      ⟨symmetrizeEnd X, by
        rw [symmetrizeEnd_apply]
        exact (mem_VPlus_iff _).2 (kappa_symmetrize X)⟩
    map_add' := by
      intro X Y
      apply Subtype.ext
      exact map_add (symmetrizeEnd : Module.End ℝ Coord) X Y
    map_smul' := by
      intro c X
      apply Subtype.ext
      exact map_smul (symmetrizeEnd : Module.End ℝ Coord) c X }

def minusPartMap : Coord →ₗ[ℝ] VMinus :=
  { toFun := fun X =>
      ⟨antisymmetrizeEnd X, by
        rw [antisymmetrizeEnd_apply]
        exact (mem_VMinus_iff _).2 (kappa_antisymmetrize X)⟩
    map_add' := by
      intro X Y
      apply Subtype.ext
      exact map_add (antisymmetrizeEnd : Module.End ℝ Coord) X Y
    map_smul' := by
      intro c X
      apply Subtype.ext
      exact map_smul (antisymmetrizeEnd : Module.End ℝ Coord) c X }

def chiralDecompositionEquiv : Coord ≃ₗ[ℝ] VPlus × VMinus where
  toFun X := (plusPartMap X, minusPartMap X)
  invFun p := p.1.1 + p.2.1
  left_inv X := by
    change symmetrizeEnd X + antisymmetrizeEnd X = X
    exact congrArg (fun f : Module.End ℝ Coord => f X)
      symmetrizeEnd_add_antisymmetrizeEnd
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change symmetrizeEnd (p.1.1 + p.2.1) = p.1.1
      rw [map_add]
      have hP : symmetrizeEnd p.1.1 = p.1.1 := by
        rw [symmetrizeEnd_apply]
        ext i
        dsimp [symmetrize]
        have hp1 : kappa p.1.1 = p.1.1 := (mem_VPlus_iff _).mp p.1.2
        rw [congrFun hp1 i]
        ring
      have hM : symmetrizeEnd p.2.1 = 0 := by
        rw [symmetrizeEnd_apply]
        ext i
        dsimp [symmetrize]
        have hp2 : kappa p.2.1 = -p.2.1 := (mem_VMinus_iff _).mp p.2.2
        rw [congrFun hp2 i]
        simp
      rw [hP, hM, add_zero]
    · apply Subtype.ext
      change antisymmetrizeEnd (p.1.1 + p.2.1) = p.2.1
      rw [map_add]
      have hP : antisymmetrizeEnd p.1.1 = 0 := by
        rw [antisymmetrizeEnd_apply]
        ext i
        dsimp [antisymmetrize]
        have hp1 : kappa p.1.1 = p.1.1 := (mem_VPlus_iff _).mp p.1.2
        rw [congrFun hp1 i]
        simp
      have hM : antisymmetrizeEnd p.2.1 = p.2.1 := by
        rw [antisymmetrizeEnd_apply]
        ext i
        dsimp [antisymmetrize]
        have hp2 : kappa p.2.1 = -p.2.1 := (mem_VMinus_iff _).mp p.2.2
        rw [congrFun hp2 i]
        dsimp
        ring
      rw [hP, hM, zero_add]
  map_add' := by
    intro X Y
    apply Prod.ext
    · exact map_add plusPartMap X Y
    · exact map_add minusPartMap X Y
  map_smul' := by
    intro c X
    apply Prod.ext
    · exact map_smul plusPartMap c X
    · exact map_smul minusPartMap c X

def generalizedWittCarrierEquiv :
    Coord ≃ₗ[ℝ] VPlus × Module.Dual ℝ VPlus :=
  chiralDecompositionEquiv.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ VPlus) wittChiralDuality)

end InfoGeometry.Lie.SplitOctonionWittChiralDualityBridge
