/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
import InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge

/-!
# A concrete three-cell frame for the algebraic logarithmic connection

The common fiber is the direct product of three copies of the native rank-two
LCFT module.  The braid group acts through its existing permutation quotient
`B₃ → S₃`; each marked cell carries the rank-two Jordan nilpotent.  This gives
a concrete instance of the residue-frame contract and hence a specialization
of the existing connection naturality theorem.  The construction is
permutation-level: it does not claim a faithful braid representation or
analytic braid holonomy.
-/

noncomputable section

namespace InfoGeometry.Projective.HadjiivanovRankTwoBraidFrame

open InfoGeometry.Projective.HadjiivanovLogConnectionRankTwoBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBridge
open InfoGeometry.Projective.HadjiivanovLogConnectionBraidBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

abbrev ThreeCellFiber := Fin 3 → RankTwoFiber

/-- Reindex the three LCFT cells by a permutation. -/
def permuteCells (p : Equiv.Perm (Fin 3)) :
    ThreeCellFiber ≃ₗ[ℂ] ThreeCellFiber where
  toFun v i := v (p.symm i)
  invFun v i := v (p i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    ext i
    rfl
  map_smul' c v := by
    ext i
    rfl

/-- The block permutation representation, before restricting to `B₃`. -/
def cellPermutationRepresentation :
    Equiv.Perm (Fin 3) →* (ThreeCellFiber ≃ₗ[ℂ] ThreeCellFiber) where
  toFun := permuteCells
  map_one' := by
    ext v i
    rfl
  map_mul' p q := by
    ext v i
    rfl

/-- Put the native rank-two nilpotent on one selected cell and zero on the
other two cells. -/
def cellNilpotent (a : Fin 3) : ThreeCellFiber →ₗ[ℂ] ThreeCellFiber where
  toFun v i := if i = a then nativeNilpotentEnd (v i) else 0
  map_add' v w := by
    ext i
    by_cases h : i = a <;> simp [h]
  map_smul' c v := by
    ext i
    by_cases h : i = a <;> simp [h]

theorem cellNilpotent_sq (a : Fin 3) :
    (cellNilpotent a).comp (cellNilpotent a) = 0 := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  funext i
  by_cases h : i = a
  · subst i
    simp only [cellNilpotent]
    have hzero := congrArg
      (fun L : RankTwoFiber →ₗ[ℂ] RankTwoFiber => L (v a))
      nativeNilpotentEnd_sq
    simpa [LinearMap.comp_apply] using hzero
  · simp [cellNilpotent, h]

private theorem permuteCells_nilpotent_intertwining
    (p : Equiv.Perm (Fin 3)) (a : Fin 3) (v : ThreeCellFiber) :
    permuteCells p (cellNilpotent a v) =
      cellNilpotent (p a) (permuteCells p v) := by
  funext i
  have hindex : p.symm i = a ↔ i = p a := by
    constructor
    · intro h
      have := congrArg p h
      simpa using this
    · intro h
      have := congrArg p.symm h
      simpa using this
  by_cases h : p.symm i = a
  · have hi : i = p a := hindex.mp h
    simp [permuteCells, cellNilpotent, hi]
  · have hi : i ≠ p a := fun hi => h (hindex.mpr hi)
    simp [permuteCells, cellNilpotent, h, hi]

/-- The concrete `B₃`-equivariant family of three rank-two residues. -/
def rankTwoBraidFrame (weight : ℂ) :
    LogResidueBraidFrame ThreeCellFiber where
  representation := cellPermutationRepresentation.comp braidPermutation
  weight := weight
  nilpotent := cellNilpotent
  nilpotent_sq := cellNilpotent_sq
  nilpotent_intertwines := by
    intro g a v
    exact permuteCells_nilpotent_intertwining (braidPermutation g) a v

@[simp] theorem rankTwoBraidFrame_representation_apply
    (weight : ℂ) (g : BraidGroup) :
    (rankTwoBraidFrame weight).representation g =
      permuteCells (braidPermutation g) := rfl

theorem rankTwoBraidFrame_representation_factors_through_S3
    (weight : ℂ) {g h : BraidGroup}
    (hp : braidPermutation g = braidPermutation h) :
    (rankTwoBraidFrame weight).representation g =
      (rankTwoBraidFrame weight).representation h := by
  simp [rankTwoBraidFrame, hp]

theorem rankTwoBraidFrame_representation_trivial_on_permutation_kernel
    (weight : ℂ) {g : BraidGroup} (hg : braidPermutation g = 1) :
    (rankTwoBraidFrame weight).representation g = 1 := by
  simp [rankTwoBraidFrame, hg]

/-- Connection naturality for the explicit three-cell LCFT residue frame. -/
theorem rankTwo_logarithmicConnection_braid
    (weight : ℂ) (g : BraidGroup) (a : Fin 3)
    (x : LogSection ThreeCellFiber) :
    logarithmicConnection
        (frameResidue (rankTwoBraidFrame weight)
          (braidPermutation g a))
        (sectionBraidTransport (rankTwoBraidFrame weight) g x) =
      sectionBraidTransport (rankTwoBraidFrame weight) g
        (logarithmicConnection
          (frameResidue (rankTwoBraidFrame weight) a) x) := by
  exact logarithmicConnection_braid (rankTwoBraidFrame weight) g a x

end InfoGeometry.Projective.HadjiivanovRankTwoBraidFrame
