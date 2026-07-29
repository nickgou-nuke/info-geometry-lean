import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Core.CartanPhaseAxisForcing
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie

Concrete Cartan symmetric-pair owner for the doubled-carrier phase-axis split.

The phase axis `K = Jε` satisfies `K² = -1`, so ordinary conjugation
`A ↦ KAK` is sign-shifted.  The Cartan involution used here is
`θ(A) = -KAK`, matching the existing source-owned split:

- phase-linear/gauge operators are even,
- phase-antilinear/scale-source operators are odd,
- the clock axis is even.

This packages the algebra already used by `BogoliubovTransport` without
identifying the scale source with zero.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Krein.clockAxis (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/-- The phase-axis Cartan involution on endomorphisms: `θ(A) = -KAK`. -/
@[rep_depth transport]
noncomputable def phaseAxisCartanMap (A : EndH) : EndH :=
  -phaseConjugate (E := E) A

lemma phaseConjugate_phaseConjugate (A : EndH) :
    phaseConjugate (E := E) (phaseConjugate (E := E) A) = A := by
  have hK2 : ∀ x : H₂, Kop (Kop x) = -x := by
    intro x
    exact congrArg (fun T : EndH => T x) (InfoGeometry.Krein.clockAxis_sq (E := E))
  apply ContinuousLinearMap.ext
  intro x
  exact
    calc
      (phaseConjugate (E := E) (phaseConjugate (E := E) A)) x
          = Kop (Kop (A (Kop (Kop x)))) := by
              simp [phaseConjugate]
      _ = Kop (Kop (A (-x))) := by rw [hK2 x]
      _ = -(A (-x)) := hK2 (A (-x))
      _ = A x := by simp

lemma phaseAxisCartanMap_involutive :
    Function.Involutive (phaseAxisCartanMap (E := E)) := by
  intro A
  calc
    phaseAxisCartanMap (E := E) (phaseAxisCartanMap (E := E) A)
        = phaseConjugate (E := E) (phaseConjugate (E := E) A) := by
            apply ContinuousLinearMap.ext
            intro x
            simp [phaseAxisCartanMap, phaseConjugate]
    _ = A := phaseConjugate_phaseConjugate (E := E) A

omit [CompleteSpace E] in
lemma phaseConjugate_sub
    (A B : EndH) :
    phaseConjugate (E := E) (A - B)
      = phaseConjugate (E := E) A - phaseConjugate (E := E) B := by
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;> simp [phaseConjugate, sub_eq_add_neg]

lemma phaseConjugate_comp_phaseConjugate
    (A B : EndH) :
    (phaseConjugate (E := E) A) * (phaseConjugate (E := E) B)
      = -(phaseConjugate (E := E) (A * B)) := by
  have hK2 : ∀ x : H₂, Kop (Kop x) = -x := by
    intro x
    exact congrArg (fun T : EndH => T x) (InfoGeometry.Krein.clockAxis_sq (E := E))
  apply ContinuousLinearMap.ext
  intro x
  exact
    calc
      ((phaseConjugate (E := E) A) * (phaseConjugate (E := E) B)) x
          = Kop (A (Kop (Kop (B (Kop x))))) := by
              simp [phaseConjugate]
      _ = Kop (A (-(B (Kop x)))) := by rw [hK2 (B (Kop x))]
      _ = Kop (-(A (B (Kop x)))) := by rw [ContinuousLinearMap.map_neg]
      _ = -(Kop (A (B (Kop x)))) := by rw [ContinuousLinearMap.map_neg]
      _ = (-(phaseConjugate (E := E) (A * B))) x := by
            apply DoubledSpace.ext <;> simp [phaseConjugate]

lemma phaseAxisCartanMap_lie
    (A B : EndH) :
    phaseAxisCartanMap (E := E) ⁅A, B⁆ =
      ⁅phaseAxisCartanMap (E := E) A, phaseAxisCartanMap (E := E) B⁆ := by
  have hAB := phaseConjugate_comp_phaseConjugate (E := E) A B
  have hBA := phaseConjugate_comp_phaseConjugate (E := E) B A
  calc
    phaseAxisCartanMap (E := E) ⁅A, B⁆
        = -(phaseConjugate (E := E) (A * B - B * A)) := by
            simp [phaseAxisCartanMap, LieRing.of_associative_ring_bracket,
              sub_eq_add_neg]
    _ = -(phaseConjugate (E := E) (A * B) -
            phaseConjugate (E := E) (B * A)) := by
          rw [phaseConjugate_sub (E := E)]
    _ = -(phaseConjugate (E := E) (A * B)) +
          phaseConjugate (E := E) (B * A) := by
          abel
    _ = (phaseConjugate (E := E) A) * (phaseConjugate (E := E) B)
          - (phaseConjugate (E := E) B) * (phaseConjugate (E := E) A) := by
          rw [hAB, hBA]
          abel
    _ = ⁅phaseAxisCartanMap (E := E) A, phaseAxisCartanMap (E := E) B⁆ := by
          simp [phaseAxisCartanMap, LieRing.of_associative_ring_bracket,
            sub_eq_add_neg]

/-- The phase-axis Cartan involution as a bare involutive automorphism. -/
@[rep_depth transport]
noncomputable def phaseAxisCartanInvolution :
    InfoGeometry.Core.InvolutiveAutomorphism EndH where
  toFun := phaseAxisCartanMap (E := E)
  involutive := phaseAxisCartanMap_involutive (E := E)

instance phaseAxisCartanInvolution_preservesLinear :
    InfoGeometry.Core.PreservesLinear EndH (phaseAxisCartanInvolution (E := E)) where
  map_add := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    apply DoubledSpace.ext <;>
      simp [phaseAxisCartanInvolution, phaseAxisCartanMap, phaseConjugate] <;> abel
  map_smul := by
    intro a A
    apply ContinuousLinearMap.ext
    intro x
    apply DoubledSpace.ext <;>
      simp [phaseAxisCartanInvolution, phaseAxisCartanMap, phaseConjugate]

instance phaseAxisCartanInvolution_preservesLieBracket :
    InfoGeometry.Core.PreservesLieBracket EndH (phaseAxisCartanInvolution (E := E)) where
  map_lie := by
    intro A B
    exact phaseAxisCartanMap_lie (E := E) A B

/-- Concrete symmetric Lie algebra induced by the doubled-carrier phase axis. -/
@[rep_depth transport]
noncomputable def phaseAxisSymmetricLieAlgebra :
    InfoGeometry.Core.SymmetricLieAlgebra EndH where
  θ := phaseAxisCartanInvolution (E := E)

lemma phaseLinear_mem_phaseAxis_even
    {A : EndH}
    (hA : IsPhaseLinear (E := E) A) :
    A ∈ (phaseAxisSymmetricLieAlgebra (E := E)).evenLieSubalgebra := by
  exact ((phaseAxisSymmetricLieAlgebra (E := E)).mem_even_iff).2 (by
    simp [phaseAxisSymmetricLieAlgebra, phaseAxisCartanInvolution, phaseAxisCartanMap,
      phaseConjugate_eq_neg_of_IsPhaseLinear (E := E) A hA])

lemma phaseAntilinear_mem_phaseAxis_odd
    {A : EndH}
    (hA : IsPhaseAntilinear (E := E) A) :
    A ∈ (phaseAxisSymmetricLieAlgebra (E := E)).oddSubmodule := by
  exact ((phaseAxisSymmetricLieAlgebra (E := E)).mem_oddSubmodule_iff).2 (by
    simp [phaseAxisSymmetricLieAlgebra, phaseAxisCartanInvolution, phaseAxisCartanMap,
      phaseConjugate_eq_self_of_IsPhaseAntilinear (E := E) A hA])

lemma clockAxis_mem_phaseAxis_even :
    Kop ∈ (phaseAxisSymmetricLieAlgebra (E := E)).evenLieSubalgebra := by
  have hK2 : ∀ x : H₂, Kop (Kop x) = -x := by
    intro x
    exact congrArg (fun T : EndH => T x) (InfoGeometry.Krein.clockAxis_sq (E := E))
  exact ((phaseAxisSymmetricLieAlgebra (E := E)).mem_even_iff).2 (by
    apply ContinuousLinearMap.ext
    intro x
    exact
      calc
        ((phaseAxisSymmetricLieAlgebra (E := E)).θ Kop) x
            = -(Kop (Kop (Kop x))) := by
                simp [phaseAxisSymmetricLieAlgebra, phaseAxisCartanInvolution,
                  phaseAxisCartanMap, phaseConjugate]
        _ = -(-(Kop x)) := by rw [hK2 (Kop x)]
        _ = Kop x := by simp
  )

/-- The modular gauge sector is even for the phase-axis Cartan structure. -/
@[rep_depth transport]
theorem modularGeneratorGaugePart_mem_phaseAxis_even
    (hMod : EndH) :
    modularGeneratorGaugePart (E := E) hMod
      ∈ (phaseAxisSymmetricLieAlgebra (E := E)).evenLieSubalgebra :=
  phaseLinear_mem_phaseAxis_even
    (E := E)
    (modularGeneratorGaugePart_isPhaseLinear (E := E) hMod)

/-- The modular scale/source sector is odd for the phase-axis Cartan structure. -/
@[rep_depth transport]
theorem modularGeneratorScalePart_mem_phaseAxis_odd
    (hMod : EndH) :
    modularGeneratorScalePart (E := E) hMod
      ∈ (phaseAxisSymmetricLieAlgebra (E := E)).oddSubmodule :=
  phaseAntilinear_mem_phaseAxis_odd
    (E := E)
    (modularGeneratorScalePart_isPhaseAntilinear (E := E) hMod)

/--
The scale-clock commutator lies in the odd sector by the phase-axis Cartan
grading.
-/
@[rep_depth transport]
theorem scaleClock_commutator_mem_phaseAxis_odd
    (hMod : EndH) :
    ⁅modularGeneratorScalePart (E := E) hMod, Kop⁆
      ∈ (phaseAxisSymmetricLieAlgebra (E := E)).oddSubmodule := by
  exact
    InfoGeometry.Core.SymmetricLieAlgebra.commutator_KI_mem_odd
      (phaseAxisSymmetricLieAlgebra (E := E))
      (modularGeneratorScalePart (E := E) hMod)
      Kop
      (modularGeneratorScalePart_mem_phaseAxis_odd (E := E) hMod)
      (clockAxis_mem_phaseAxis_even (E := E))

/--
The gauge-clock commutator stays in the even sector.  This is the concrete
`[𝔨,𝔨] ⊆ 𝔨` half of the phase-axis Cartan split.
-/
@[rep_depth transport]
theorem gaugeClock_commutator_mem_phaseAxis_even
    (hMod : EndH) :
    ⁅modularGeneratorGaugePart (E := E) hMod, Kop⁆
      ∈ (phaseAxisSymmetricLieAlgebra (E := E)).evenLieSubalgebra := by
  have hg :
      modularGeneratorGaugePart (E := E) hMod
        ∈ (phaseAxisSymmetricLieAlgebra (E := E)).𝔨 := by
    simpa [InfoGeometry.Core.SymmetricLieAlgebra.𝔨] using
      modularGeneratorGaugePart_mem_phaseAxis_even (E := E) hMod
  have hk :
      Kop ∈ (phaseAxisSymmetricLieAlgebra (E := E)).𝔨 := by
    simpa [InfoGeometry.Core.SymmetricLieAlgebra.𝔨] using
      clockAxis_mem_phaseAxis_even (E := E)
  simpa [InfoGeometry.Core.SymmetricLieAlgebra.𝔨] using
    InfoGeometry.Core.SymmetricLieAlgebra.bracket_k_k
      (S := phaseAxisSymmetricLieAlgebra (E := E)) hg hk

omit [CompleteSpace E] in
/--
The gauge-clock commutator is actually zero because the gauge sector is
phase-linear and therefore commutes with the phase axis.
-/
@[rep_depth transport]
theorem gaugeClock_commutator_eq_zero
    (hMod : EndH) :
    ⁅modularGeneratorGaugePart (E := E) hMod, Kop⁆ = 0 := by
  have hZero :
      phaseAxisForce (E := E) (modularGeneratorGaugePart (E := E) hMod) = 0 :=
    phaseAxisForce_eq_zero_of_IsPhaseLinear
      (E := E)
      (modularGeneratorGaugePart (E := E) hMod)
      (modularGeneratorGaugePart_isPhaseLinear (E := E) hMod)
  simpa [lieBracket_eq_transportCommutator, phaseAxisForce] using hZero

/--
Concrete dual-grade closure for the scale-clock channel: the scale-clock
commutator is already odd; if a source theorem also places it in the even
sector, the Cartan intersection rule kills it.
-/
@[rep_depth transport]
theorem scaleClock_commutator_eq_zero_of_mem_phaseAxis_even
    (hMod : EndH)
    (hEven :
      ⁅modularGeneratorScalePart (E := E) hMod, Kop⁆
        ∈ (phaseAxisSymmetricLieAlgebra (E := E)).evenLieSubalgebra) :
    ⁅modularGeneratorScalePart (E := E) hMod, Kop⁆ = 0 := by
  exact
    InfoGeometry.Core.SymmetricLieAlgebra.eq_zero_of_mem_even_and_odd
      (phaseAxisSymmetricLieAlgebra (E := E))
      hEven
      (scaleClock_commutator_mem_phaseAxis_odd (E := E) hMod)

end Core

end InfoGeometry.Canonical.PhaseAxisCartanSymmetricLie
