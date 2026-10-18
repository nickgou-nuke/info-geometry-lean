/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Synthesis.SedenionG2ParameterBracket
import InfoGeometry.Synthesis.SplitSedenionDerivationClassification
import InfoGeometry.Synthesis.SplitSedenionParameterEndomorphism

/-!
# Endomorphism representation of the split-sedenion parameter bracket

This proves that the concrete fourteen-parameter family represents the bracket
pulled back from the native Zorn derivations as an ordinary commutator in
`Module.End`. The final range theorem repackages the existing function-level
classification as an exact characterization among linear endomorphisms. This
does not claim a 17-dimensional decomposition of a different derivation algebra.
-/

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Synthesis.SedenionG2EndomorphismLieRepresentation

open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Cl44IdempotentIdeal
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Synthesis.Cl44LeftIdealSplitSedenionSynthesis
open InfoGeometry.Synthesis.Cl44MinimalIdealSplitSedenionEquivBridge
open InfoGeometry.Synthesis.Cl44MinimalIdealInducedSedenionProductBridge
open InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge
open InfoGeometry.Synthesis.SedenionG2ParameterBracket
open InfoGeometry.Synthesis.SplitSedenionDerivationClassification
open InfoGeometry.Synthesis.SplitSedenionParameterEndomorphism
open InfoGeometry.Synthesis.SplitSedenionDerivationRepresentationSynthesis

local instance : LieRing (Module.End ℝ (SplitSedenion ℝ)) :=
  LieRing.ofAssociativeRing

local instance : LieAlgebra ℝ (Module.End ℝ (SplitSedenion ℝ)) :=
  LieAlgebra.ofAssociativeAlgebra

local instance : LieRing (Module.End ℝ (Fin 16 → ℝ)) :=
  LieRing.ofAssociativeRing

local instance : LieAlgebra ℝ (Module.End ℝ (Fin 16 → ℝ)) :=
  LieAlgebra.ofAssociativeAlgebra

local instance : LieRing (Module.End ℝ (LeftIdeal primIdem)) :=
  LieRing.ofAssociativeRing

local instance : LieAlgebra ℝ (Module.End ℝ (LeftIdeal primIdem)) :=
  LieAlgebra.ofAssociativeAlgebra

private theorem sedenionSub_eq_sub (x y : SplitSedenion ℝ) :
    sedenionSub x y = x - y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply Prod.ext
  · ext <;> simp [sedenionSub, sedenionAdd, sedenionNeg,
      zornAdd, zornSmul] <;> ring
  · ext <;> simp [sedenionSub, sedenionAdd, sedenionNeg,
      zornAdd, zornSmul] <;> ring

/-- The endomorphism family represents the pulled-back parameter bracket by
the commutator in `Module.End`, with composition ordered as `D ∘ E - E ∘ D`.
This concerns only the specified fourteen-parameter family. -/
theorem sedenionG2EndomorphismFamily_parameterBracket (p q : Params) :
    sedenionG2EndomorphismFamily (parameterBracket p q) =
      sedenionG2EndomorphismFamily p * sedenionG2EndomorphismFamily q -
        sedenionG2EndomorphismFamily q * sedenionG2EndomorphismFamily p := by
  apply LinearMap.ext
  intro X
  have h := sedenionG2Derivation_parameterBracket p q X
  simpa [sedenionG2EndomorphismFamily, sedenionG2DerivationLinear,
    sedenionDerivationCommutator, sedenionSub_eq_sub] using h

/-- The native Zorn derivation Lie algebra acts on the actual split-sedenion carrier by the
specified fourteen-parameter endomorphisms. -/
noncomputable def sedenionG2DerivationLieHom :
    VDer →ₗ⁅ℝ⁆ Module.End ℝ (SplitSedenion ℝ) where
  toLinearMap :=
    sedenionG2EndomorphismFamily.comp parameterLinearEquiv.symm.toLinearMap
  map_lie' := by
    intro D E
    change sedenionG2EndomorphismFamily
        (parameterLinearEquiv.symm
          (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E)) =
      ⁅sedenionG2EndomorphismFamily (parameterLinearEquiv.symm D),
        sedenionG2EndomorphismFamily (parameterLinearEquiv.symm E)⁆
    have hpar :
        parameterBracket (parameterLinearEquiv.symm D) (parameterLinearEquiv.symm E) =
          parameterLinearEquiv.symm
            (InfoGeometry.Algebra.ZornVectorMatrix.Derivation.bracket D E) := by
      simp [parameterBracket]
    rw [← hpar, sedenionG2EndomorphismFamily_parameterBracket,
      LieRing.of_associative_ring_bracket]

/-- Evaluation of the native Lie representation is the parameterized
split-sedenion derivation selected by `parameterLinearEquiv`. -/
@[simp] theorem sedenionG2DerivationLieHom_apply
    (D : VDer) (X : SplitSedenion ℝ) :
    sedenionG2DerivationLieHom D X =
      sedenionG2Derivation (parameterLinearEquiv.symm D) X := rfl

/-- The Lie representation is faithful on the native fourteen-dimensional derivation algebra. -/
theorem sedenionG2DerivationLieHom_injective :
    Function.Injective sedenionG2DerivationLieHom := by
  intro D E h
  apply parameterLinearEquiv.symm.injective
  apply sedenionG2EndomorphismFamily_injective
  change sedenionG2EndomorphismFamily (parameterLinearEquiv.symm D) =
    sedenionG2EndomorphismFamily (parameterLinearEquiv.symm E)
  exact h

/-- The native derivation algebra is Lie-isomorphic to the endomorphism representation's range. -/
noncomputable def sedenionG2DerivationLieEquiv :
    VDer ≃ₗ⁅ℝ⁆ sedenionG2DerivationLieHom.range :=
  LieEquiv.ofInjective sedenionG2DerivationLieHom sedenionG2DerivationLieHom_injective

/-- The represented Lie subalgebra of endomorphisms has real dimension fourteen. -/
theorem sedenionG2DerivationLieHom_range_finrank :
    Module.finrank ℝ sedenionG2DerivationLieHom.range = 14 := by
  rw [← sedenionG2DerivationLieEquiv.toLinearEquiv.finrank_eq]
  exact finrank_vectorDerivations

/-- The concrete parameter family has as its linear range exactly the real-linear
endomorphisms whose underlying functions satisfy the split-sedenion derivation
predicate. This packages the existing function-level classification as a range
characterization in `Module.End`. -/
theorem sedenionG2EndomorphismFamily_range_eq_sedenionDerivations :
    LinearMap.range sedenionG2EndomorphismFamily =
      {T : Module.End ℝ (SplitSedenion ℝ) |
        IsSedenionDerivation
          (T : SplitSedenion ℝ → SplitSedenion ℝ)} := by
  ext T
  change (∃ p, sedenionG2EndomorphismFamily p = T) ↔
    IsSedenionDerivation (T : SplitSedenion ℝ → SplitSedenion ℝ)
  constructor
  · rintro ⟨p, hp⟩
    have hpFun : sedenionG2Derivation p =
        (T : SplitSedenion ℝ → SplitSedenion ℝ) := by
      have h := congrArg
        (fun E : Module.End ℝ (SplitSedenion ℝ) =>
          (E : SplitSedenion ℝ → SplitSedenion ℝ)) hp
      simpa [sedenionG2EndomorphismFamily, sedenionG2DerivationLinear] using h
    rw [← hpFun]
    exact (sedenionG2Derivation_isStarDerivation p).1
  · intro hT
    obtain ⟨p, hp, _hUnique⟩ :=
      sedenionDerivation_existsUnique_g2Params
        (D := (T : SplitSedenion ℝ → SplitSedenion ℝ)) hT
    refine ⟨p, ?_⟩
    apply LinearMap.ext
    intro X
    have hX := congrFun hp X
    change T X = sedenionG2Derivation p X at hX
    change sedenionG2Derivation p X = T X
    exact hX.symm

/-- The carrier set of the native-derivation LieHom range is exactly the
real-linear endomorphisms whose underlying maps satisfy the concrete
split-sedenion Leibniz predicate. This is the family range theorem transported
through `parameterLinearEquiv`; it adds no further classification claim. -/
theorem sedenionG2DerivationLieHom_range_eq_sedenionDerivations :
    (sedenionG2DerivationLieHom.range : Set (Module.End ℝ (SplitSedenion ℝ))) =
      {T : Module.End ℝ (SplitSedenion ℝ) |
        IsSedenionDerivation (T : SplitSedenion ℝ → SplitSedenion ℝ)} := by
  ext T
  change (∃ D, sedenionG2DerivationLieHom D = T) ↔
    IsSedenionDerivation (T : SplitSedenion ℝ → SplitSedenion ℝ)
  have hFamilyRange :
      (T ∈ LinearMap.range sedenionG2EndomorphismFamily) ↔
        IsSedenionDerivation (T : SplitSedenion ℝ → SplitSedenion ℝ) :=
    Iff.of_eq <| congrArg
      (fun S : Set (Module.End ℝ (SplitSedenion ℝ)) => T ∈ S)
      sedenionG2EndomorphismFamily_range_eq_sedenionDerivations
  constructor
  · rintro ⟨D, hD⟩
    have hFamily :
        sedenionG2EndomorphismFamily (parameterLinearEquiv.symm D) = T := by
      change sedenionG2DerivationLieHom D = T at hD
      exact hD
    have hMem : T ∈ LinearMap.range sedenionG2EndomorphismFamily :=
      ⟨parameterLinearEquiv.symm D, hFamily⟩
    exact hFamilyRange.mp hMem
  · intro hT
    have hMem : T ∈ LinearMap.range sedenionG2EndomorphismFamily :=
      hFamilyRange.mpr hT
    obtain ⟨p, hp⟩ := LinearMap.mem_range.mp hMem
    refine ⟨parameterLinearEquiv p, ?_⟩
    change sedenionG2EndomorphismFamily
      (parameterLinearEquiv.symm (parameterLinearEquiv p)) = T
    rw [parameterLinearEquiv.symm_apply_apply]
    exact hp

/-- Transport the native split-sedenion derivation representation to the
spinor-coordinate carrier. The induced product is the product transported
from split sedenions, not ordinary matrix multiplication. -/
noncomputable def spinor16G2DerivationLieHom :
    VDer →ₗ⁅ℝ⁆ Module.End ℝ (Fin 16 → ℝ) :=
  (spinor16SplitSedenionLinearEquiv.symm.lieConj).toLieHom.comp
    sedenionG2DerivationLieHom

/-- Transport the native split-sedenion derivation representation to the
minimal left ideal carrier, using the product transported from split
sedenions. -/
noncomputable def cl44LeftIdealG2DerivationLieHom :
    VDer →ₗ⁅ℝ⁆ Module.End ℝ (LeftIdeal primIdem) :=
  (leftIdealEquiv.symm.lieConj).toLieHom.comp
    spinor16G2DerivationLieHom

/-- The transported spinor Lie action agrees pointwise with the existing
parameter action under the native derivation parameter equivalence. -/
@[simp] theorem spinor16G2DerivationLieHom_apply
    (D : VDer) (v : Fin 16 → ℝ) :
    spinor16G2DerivationLieHom D v =
      spinor16G2Derivation (parameterLinearEquiv.symm D) v := by
  apply spinor16SplitSedenionEquiv.injective
  change spinor16SplitSedenionEquiv
      (spinor16SplitSedenionLinearEquiv.symm.conj
        (sedenionG2DerivationLieHom D) v) =
    spinor16SplitSedenionEquiv
      (spinor16SplitSedenionEquiv.symm
        (sedenionG2Derivation (parameterLinearEquiv.symm D)
          (spinor16SplitSedenionEquiv v)))
  rw [LinearEquiv.conj_apply_apply]
  simp [spinor16SplitSedenionLinearEquiv,
    spinor16SplitSedenionEquiv, sedenionG2EndomorphismFamily,
    sedenionG2DerivationLinear]

/-- The transported left-ideal Lie action agrees pointwise with the existing
parameter action under the native derivation parameter equivalence. -/
@[simp] theorem cl44LeftIdealG2DerivationLieHom_apply
    (D : VDer) (A : LeftIdeal primIdem) :
    cl44LeftIdealG2DerivationLieHom D A =
      cl44LeftIdealG2Derivation (parameterLinearEquiv.symm D) A := by
  apply leftIdealEquiv.injective
  change leftIdealEquiv
      (leftIdealEquiv.symm.conj (spinor16G2DerivationLieHom D) A) =
    leftIdealEquiv (cl44LeftIdealG2Derivation (parameterLinearEquiv.symm D) A)
  rw [LinearEquiv.conj_apply_apply]
  rw [spinor16G2DerivationLieHom_apply]
  exact leftIdealEquiv_intertwines_g2Derivation
    (parameterLinearEquiv.symm D) A

/-- The transported spinor and left-ideal actions intertwine through the
existing carrier equivalence. -/
theorem leftIdealEquiv_intertwines_G2LieActions
    (D : VDer) (A : LeftIdeal primIdem) :
    leftIdealEquiv (cl44LeftIdealG2DerivationLieHom D A) =
      spinor16G2DerivationLieHom D (leftIdealEquiv A) := by
  rw [cl44LeftIdealG2DerivationLieHom_apply,
    spinor16G2DerivationLieHom_apply]
  exact leftIdealEquiv_intertwines_g2Derivation
    (parameterLinearEquiv.symm D) A

end InfoGeometry.Synthesis.SedenionG2EndomorphismLieRepresentation
