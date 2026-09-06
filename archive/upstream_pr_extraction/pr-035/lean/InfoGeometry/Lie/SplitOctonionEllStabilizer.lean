/-
The Lie-algebra stabilizer of the distinguished split direction `ell`.

This is deliberately an infinitesimal theorem.  It reuses the native
fourteen-dimensional derivation Lie algebra and does not claim a global
automorphism-group identification with `G₂(2)`.
-/

import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Algebra.Zorn.SplitQuaternionCore
import InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllStabilizer

open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Algebra.Zorn.SplitOctonionRindlerBoost
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev EndCZ := InfoGeometry.Lie.CanonicalZornDerivation.EndCZ

noncomputable def leftMul (X : CZ) : EndCZ where
  toFun Y := InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X Y
  map_add' Y Z := by
    exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_add_right X Y Z
  map_smul' r Y := by
    exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_smul_right r X Y

@[simp] theorem leftMul_apply (X Y : CZ) :
    leftMul X Y = InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X Y := rfl

@[simp] theorem leftMul_zero : leftMul (0 : CZ) = 0 := by
  apply LinearMap.ext
  intro Y
  change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 0 Y = 0
  exact InfoGeometry.Algebra.Zorn.SplitQuaternionCore.zMul_zero_left Y

theorem derivation_bracket_leftMul_eq_leftMul_map
    (D : EndCZ)
    (hD : D ∈ canonicalZornDerivations)
    (X : CZ) :
    ⁅D, leftMul X⁆ = leftMul (D X) := by
  apply LinearMap.ext
  intro Y
  rw [LieRing.of_associative_ring_bracket]
  change D (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X Y) -
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X (D Y) =
    InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (D X) Y
  have hXY :
      D (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X Y) =
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (D X) Y +
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul X (D Y) := by
    exact hD X Y
  rw [hXY]
  abel

theorem derivation_map_one
    (D : EndCZ)
    (hD : D ∈ canonicalZornDerivations) :
    D (1 : CZ) = 0 := by
  have h := hD (1 : CZ) (1 : CZ)
  change D (InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 1 1) =
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (D 1) 1 +
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 1 (D 1) at h
  have h1 :
      D (1 : CZ) =
        InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (D 1) 1 +
          InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 1 (D 1) := by
    simpa only [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.one_zMul] using h
  have hleft :
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul (D 1) 1 = D 1 := by
    exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.zMul_one (D 1)
  have hright :
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul 1 (D 1) = D 1 := by
    exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.one_zMul (D 1)
  rw [hleft, hright] at h1
  have hsum : D (1 : CZ) = D 1 + D 1 := by
    exact h1
  have hcancel : D 1 + D 1 = D 1 + 0 := by
    calc
      D 1 + D 1 = D 1 := hsum.symm
      _ = D 1 + 0 := (add_zero _).symm
  have hz : D (1 : CZ) = 0 := add_left_cancel hcancel
  exact hz

def ellStabilizer : LieSubalgebra ℝ EndCZ where
  carrier :=
    {D |
      D ∈ canonicalZornDerivations ∧
        D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = 0}
  zero_mem' := by
    constructor
    · exact canonicalZornDerivations.zero_mem
    · simp
  add_mem' := by
    intro D E hD hE
    constructor
    · exact canonicalZornDerivations.add_mem hD.1 hE.1
    · change D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit +
        E InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = 0
      rw [hD.2, hE.2, add_zero]
  smul_mem' := by
    intro r D hD
    constructor
    · exact canonicalZornDerivations.smul_mem r hD.1
    · change r • D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = 0
      rw [hD.2, smul_zero]
  lie_mem' := by
    intro D E hD hE
    constructor
    · exact canonicalZornDerivations.lie_mem hD.1 hE.1
    · change D (E InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) -
        E (D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) = 0
      have hE' :
          D (E InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) = 0 := by
        simpa only [map_zero] using congrArg D hE.2
      have hD' :
          E (D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) = 0 := by
        simpa only [map_zero] using congrArg E hD.2
      rw [hE', hD']
      simp

@[simp] theorem mem_ellStabilizer (D : EndCZ) :
    D ∈ ellStabilizer ↔
      D ∈ canonicalZornDerivations ∧
        D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit = 0 :=
  Iff.rfl

theorem ellStabilizer_le_derivations :
    ellStabilizer ≤ canonicalZornDerivations := by
  intro D hD
  exact hD.1

theorem ellStabilizer_closed_under_lie
    {D E : EndCZ}
    (hD : D ∈ ellStabilizer) (hE : E ∈ ellStabilizer) :
    ⁅D, E⁆ ∈ ellStabilizer := by
  exact ellStabilizer.lie_mem hD hE

theorem mem_ellStabilizer_iff_leftMul_centralizer
    (D : EndCZ)
    (hD : D ∈ canonicalZornDerivations) :
    D ∈ ellStabilizer ↔ ⁅D, leftMul InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit⁆ = 0 := by
  constructor
  · intro h
    rw [derivation_bracket_leftMul_eq_leftMul_map D hD
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit, h.2]
    exact leftMul_zero
  · intro h
    refine ⟨hD, ?_⟩
    have hmap := derivation_bracket_leftMul_eq_leftMul_map D hD
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit
    have hleft :
        leftMul (D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) = 0 := by
      rw [← hmap]
      exact h
    have hone := congrArg (fun T : EndCZ => T (1 : CZ)) hleft
    change InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul
      (D InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) (1 : CZ) = 0 at hone
    rw [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.zMul_one] at hone
    exact hone

/-! ## Explicit target surfaces: ell, ordered chiral pair, and quaternionic slice -/

/-- The two scalar Witt/chiral directions associated with the distinguished
split generator `lUnit`.  These are named locally to avoid conflating the
matrix/operator `uPlus/uMinus` APIs with elements of the split-octonion
carrier. -/
noncomputable def ellChiralPlus : CZ :=
  chiralNull ⟨0, by decide⟩ 1

noncomputable def ellChiralMinus : CZ :=
  chiralNull ⟨0, by decide⟩ (-1)

theorem ellChiralPlus_add_ellChiralMinus :
    ellChiralPlus + ellChiralMinus = (1 : CZ) := by
  simpa [ellChiralPlus, ellChiralMinus] using one_eq_chiral_sum.symm

theorem ellChiralPlus_sub_ellChiralMinus :
    ellChiralPlus - ellChiralMinus =
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit := by
  simpa [ellChiralPlus, ellChiralMinus] using lUnit_eq_chiral_difference.symm

/-- Infinitesimal stabilizer of the ordered pair of scalar chiral directions.
This is deliberately distinct from the stabilizer of the unordered pair. -/
def orderedEllChiralPairStabilizer : LieSubalgebra ℝ EndCZ where
  carrier :=
    {D |
      D ∈ canonicalZornDerivations ∧
        D ellChiralPlus = 0 ∧ D ellChiralMinus = 0}
  zero_mem' := by
    refine ⟨canonicalZornDerivations.zero_mem, ?_, ?_⟩ <;> simp
  add_mem' := by
    intro D E hD hE
    refine ⟨canonicalZornDerivations.add_mem hD.1 hE.1, ?_, ?_⟩
    · change D ellChiralPlus + E ellChiralPlus = 0
      rw [hD.2.1, hE.2.1, add_zero]
    · change D ellChiralMinus + E ellChiralMinus = 0
      rw [hD.2.2, hE.2.2, add_zero]
  smul_mem' := by
    intro r D hD
    refine ⟨canonicalZornDerivations.smul_mem r hD.1, ?_, ?_⟩
    · change r • D ellChiralPlus = 0
      rw [hD.2.1, smul_zero]
    · change r • D ellChiralMinus = 0
      rw [hD.2.2, smul_zero]
  lie_mem' := by
    intro D E hD hE
    refine ⟨canonicalZornDerivations.lie_mem hD.1 hE.1, ?_, ?_⟩
    · change D (E ellChiralPlus) - E (D ellChiralPlus) = 0
      rw [hE.2.1, hD.2.1, map_zero, map_zero, sub_zero]
    · change D (E ellChiralMinus) - E (D ellChiralMinus) = 0
      rw [hE.2.2, hD.2.2, map_zero, map_zero, sub_zero]

@[simp] theorem mem_orderedEllChiralPairStabilizer (D : EndCZ) :
    D ∈ orderedEllChiralPairStabilizer ↔
      D ∈ canonicalZornDerivations ∧
        D ellChiralPlus = 0 ∧ D ellChiralMinus = 0 := Iff.rfl

theorem mem_ellStabilizer_iff_mem_orderedEllChiralPairStabilizer
    (D : EndCZ)
    (hD : D ∈ canonicalZornDerivations) :
    D ∈ ellStabilizer ↔ D ∈ orderedEllChiralPairStabilizer := by
  constructor
  · intro h
    refine ⟨hD, ?_, ?_⟩
    · rw [ellChiralPlus, scalar_chiralNull_plus_idempotent]
      rw [map_smul, map_add, derivation_map_one D hD, h.2, add_zero, smul_zero]
    · rw [ellChiralMinus, scalar_chiralNull_minus_idempotent]
      rw [map_smul, map_sub, derivation_map_one D hD, h.2, sub_zero, smul_zero]
  · intro h
    refine ⟨hD, ?_⟩
    rw [← ellChiralPlus_sub_ellChiralMinus]
    rw [map_sub, h.2.1, h.2.2, sub_zero]

/-- Infinitesimal stabilizer of the quaternionic split slice.  “Stabilize”
means preserve the four-dimensional submodule setwise; it does not mean fix
every element of the slice pointwise. -/
def quaternionicSlicePreserver : LieSubalgebra ℝ EndCZ where
  carrier :=
    {D |
      D ∈ canonicalZornDerivations ∧
        ∀ X, X ∈ coreSubmodule → D X ∈ coreSubmodule}
  zero_mem' := by
    refine ⟨canonicalZornDerivations.zero_mem, ?_⟩
    intro X hX
    exact Submodule.zero_mem _
  add_mem' := by
    intro D E hD hE
    refine ⟨canonicalZornDerivations.add_mem hD.1 hE.1, ?_⟩
    intro X hX
    change D X + E X ∈ coreSubmodule
    exact Submodule.add_mem _ (hD.2 X hX) (hE.2 X hX)
  smul_mem' := by
    intro r D hD
    refine ⟨canonicalZornDerivations.smul_mem r hD.1, ?_⟩
    intro X hX
    change r • D X ∈ coreSubmodule
    exact Submodule.smul_mem _ r (hD.2 X hX)
  lie_mem' := by
    intro D E hD hE
    refine ⟨canonicalZornDerivations.lie_mem hD.1 hE.1, ?_⟩
    intro X hX
    change D (E X) - E (D X) ∈ coreSubmodule
    exact Submodule.sub_mem _ (hD.2 (E X) (hE.2 X hX))
      (hE.2 (D X) (hD.2 X hX))

@[simp] theorem mem_quaternionicSlicePreserver (D : EndCZ) :
    D ∈ quaternionicSlicePreserver ↔
      D ∈ canonicalZornDerivations ∧
        ∀ X, X ∈ coreSubmodule → D X ∈ coreSubmodule := Iff.rfl

/-! ## Group-level candidates, without asserting a global G₂ classification -/

def realZornEllStabilizer : Subgroup realZornCompositionAut where
  carrier :=
    {φ |
      (φ : CanonicalLinearAut)
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit}
  one_mem' := by simp
  mul_mem' := by
    intro φ ψ hφ hψ
    change (φ : CanonicalLinearAut)
        ((ψ : CanonicalLinearAut)
          InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) = _
    rw [hψ, hφ]
  inv_mem' := by
    intro φ hφ
    apply (φ : CanonicalLinearAut).injective
    change (φ : CanonicalLinearAut)
        ((φ : CanonicalLinearAut).symm
          InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) =
      (φ : CanonicalLinearAut) InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit
    rw [LinearEquiv.apply_symm_apply, hφ]

def realZornOrderedChiralPairStabilizer : Subgroup realZornCompositionAut where
  carrier :=
    {φ |
      (φ : CanonicalLinearAut) ellChiralPlus = ellChiralPlus ∧
      (φ : CanonicalLinearAut) ellChiralMinus = ellChiralMinus}
  one_mem' := by simp
  mul_mem' := by
    intro φ ψ hφ hψ
    constructor
    · change (φ : CanonicalLinearAut)
        ((ψ : CanonicalLinearAut) ellChiralPlus) = ellChiralPlus
      rw [hψ.1, hφ.1]
    · change (φ : CanonicalLinearAut)
        ((ψ : CanonicalLinearAut) ellChiralMinus) = ellChiralMinus
      rw [hψ.2, hφ.2]
  inv_mem' := by
    intro φ hφ
    constructor
    · apply (φ : CanonicalLinearAut).injective
      change (φ : CanonicalLinearAut)
          ((φ : CanonicalLinearAut).symm ellChiralPlus) =
        (φ : CanonicalLinearAut) ellChiralPlus
      rw [LinearEquiv.apply_symm_apply, hφ.1]
    · apply (φ : CanonicalLinearAut).injective
      change (φ : CanonicalLinearAut)
          ((φ : CanonicalLinearAut).symm ellChiralMinus) =
        (φ : CanonicalLinearAut) ellChiralMinus
      rw [LinearEquiv.apply_symm_apply, hφ.2]

/-- Group-level stabilizer of the quaternionic split slice.  The iff form is
used deliberately: it records genuine setwise preservation and makes inverse
closure explicit, rather than silently assuming that one-sided containment
has an inverse. -/
def realZornQuaternionicSliceStabilizer : Subgroup realZornCompositionAut where
  carrier :=
    {φ |
      ∀ X : CZ, X ∈ coreSubmodule ↔
        (φ : CanonicalLinearAut) X ∈ coreSubmodule}
  one_mem' := by
    intro X
    simp
  mul_mem' := by
    intro φ ψ hφ hψ X
    change X ∈ coreSubmodule ↔
      (φ : CanonicalLinearAut) ((ψ : CanonicalLinearAut) X) ∈ coreSubmodule
    rw [hψ X, hφ ((ψ : CanonicalLinearAut) X)]
  inv_mem' := by
    intro φ hφ X
    constructor
    · intro hX
      exact (hφ ((φ : CanonicalLinearAut).symm X)).mpr (by
        simpa using hX)
    · intro hX
      have h' := (hφ ((φ : CanonicalLinearAut).symm X)).mp hX
      simpa using h'

theorem realZornEllStabilizer_eq_orderedChiralPairStabilizer :
    realZornEllStabilizer = realZornOrderedChiralPairStabilizer := by
  ext φ
  change ((φ : CanonicalLinearAut)
      InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit =
        InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit) ↔
    ((φ : CanonicalLinearAut) ellChiralPlus = ellChiralPlus ∧
      (φ : CanonicalLinearAut) ellChiralMinus = ellChiralMinus)
  constructor
  · intro h
    have hone := realZornCompositionAut_fix_one φ
    constructor
    · rw [ellChiralPlus, scalar_chiralNull_plus_idempotent]
      rw [map_smul, map_add, hone, h]
    · rw [ellChiralMinus, scalar_chiralNull_minus_idempotent]
      rw [map_smul, map_sub, hone, h]
  · intro h
    rw [← ellChiralPlus_sub_ellChiralMinus]
    rw [map_sub, h.1, h.2]

end InfoGeometry.Lie.SplitOctonionEllStabilizer
