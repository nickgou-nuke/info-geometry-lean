import Mathlib
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
import InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge
import InfoGeometry.Canonical.SplitOctonionSymplecticLieAlgebra

namespace InfoGeometry.Canonical.CanonicalZornPhaseBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionDerivationWittOrthogonalBridge
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace
open InfoGeometry.Canonical.SplitOctonionGogberashviliCanonicalBridge

noncomputable section

abbrev Derivation := canonicalZornDerivations
abbrev PaperZorn := InfoGeometry.Algebra.ZornMatrix ℝ
abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev Phase := InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace.Phase
abbrev PhaseEnd := Module.End ℝ Phase

def phaseToPaper : Phase →ₗ[ℝ] PaperZorn where
  toFun X := { a := 0, v := X.1, w := X.2, b := 0 }
  map_add' X Y := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · change (0 : ℝ) = 0 + 0
      simp
    · change X.1 + Y.1 = X.1 + Y.1
      rfl
    · change X.2 + Y.2 = X.2 + Y.2
      rfl
    · change (0 : ℝ) = 0 + 0
      simp
  map_smul' r X := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · change (0 : ℝ) = r • 0
      simp
    · change r • X.1 = r • X.1
      rfl
    · change r • X.2 = r • X.2
      rfl
    · change (0 : ℝ) = r • 0
      simp

def paperToPhase : PaperZorn →ₗ[ℝ] Phase where
  toFun X := (X.v, X.w)
  map_add' X Y := by ext i <;> rfl
  map_smul' r X := by ext i <;> rfl

@[simp] theorem paperToPhase_phaseToPaper (X : Phase) :
    paperToPhase (phaseToPaper X) = X := rfl

theorem phaseToPaper_injective : Function.Injective phaseToPaper := by
  intro X Y h
  exact congrArg paperToPhase h

def phaseToCanonical : Phase →ₗ[ℝ] CZ :=
  paperCanonicalLinearEquiv.toLinearMap.comp phaseToPaper

def canonicalToPhase : CZ →ₗ[ℝ] Phase :=
  paperToPhase.comp paperCanonicalLinearEquiv.symm.toLinearMap

@[simp] theorem canonicalToPhase_phaseToCanonical (X : Phase) :
    canonicalToPhase (phaseToCanonical X) = X := by
  simp [phaseToCanonical, canonicalToPhase]

theorem phaseToCanonical_injective : Function.Injective phaseToCanonical := by
  intro X Y h
  simpa using congrArg canonicalToPhase h

def IsPhaseElement (X : CZ) : Prop := X.a = 0 ∧ X.b = 0

theorem phaseToCanonical_mem (X : Phase) :
    IsPhaseElement (phaseToCanonical X) := by
  exact ⟨rfl, rfl⟩

theorem phaseToCanonical_canonicalToPhase_of_mem
    {X : CZ} (hX : IsPhaseElement X) :
    phaseToCanonical (canonicalToPhase X) = X := by
  rcases hX with ⟨ha, hb⟩
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [phaseToCanonical, canonicalToPhase, phaseToPaper, paperToPhase,
      paperCanonicalLinearEquiv, ha]
  · simp [phaseToCanonical, canonicalToPhase, phaseToPaper, paperToPhase,
      paperCanonicalLinearEquiv, hb]
  · simp [phaseToCanonical, canonicalToPhase, phaseToPaper, paperToPhase,
      paperCanonicalLinearEquiv]
  · simp [phaseToCanonical, canonicalToPhase, phaseToPaper, paperToPhase,
      paperCanonicalLinearEquiv]

def PreservesPhase (D : Derivation) : Prop :=
  ∀ X : Phase, IsPhaseElement (D.1 (phaseToCanonical X))

def phaseAction (D : Derivation) : PhaseEnd :=
  canonicalToPhase.comp (D.1.comp phaseToCanonical)

@[simp] theorem phaseAction_apply (D : Derivation) (X : Phase) :
    phaseAction D X = canonicalToPhase (D.1 (phaseToCanonical X)) := rfl

theorem phaseToCanonical_phaseAction
    {D : Derivation} (hD : PreservesPhase D) (X : Phase) :
    phaseToCanonical (phaseAction D X) = D.1 (phaseToCanonical X) := by
  rw [phaseAction_apply]
  exact phaseToCanonical_canonicalToPhase_of_mem (hD X)

theorem preservesPhase_zero : PreservesPhase (0 : Derivation) := by
  intro X
  exact ⟨rfl, rfl⟩

theorem preservesPhase_add
    {D E : Derivation}
    (hD : PreservesPhase D) (hE : PreservesPhase E) :
    PreservesPhase (D + E) := by
  intro X
  rcases hD X with ⟨hDa, hDb⟩
  rcases hE X with ⟨hEa, hEb⟩
  constructor
  · change (D.1 (phaseToCanonical X) + E.1 (phaseToCanonical X)).a = 0
    simp [hDa, hEa]
  · change (D.1 (phaseToCanonical X) + E.1 (phaseToCanonical X)).b = 0
    simp [hDb, hEb]

theorem preservesPhase_smul
    (r : ℝ) {D : Derivation} (hD : PreservesPhase D) :
    PreservesPhase (⟨r • D.1,
      canonicalZornDerivations.smul_mem r D.2⟩ : Derivation) := by
  intro X
  rcases hD X with ⟨ha, hb⟩
  constructor
  · change (r • D.1 (phaseToCanonical X)).a = 0
    simp [ha]
  · change (r • D.1 (phaseToCanonical X)).b = 0
    simp [hb]

theorem preservesPhase_neg
    {D : Derivation} (hD : PreservesPhase D) :
    PreservesPhase (⟨-D.1,
      canonicalZornDerivations.neg_mem D.2⟩ : Derivation) := by
  intro X
  rcases hD X with ⟨ha, hb⟩
  constructor
  · change (-D.1 (phaseToCanonical X)).a = 0
    simp [ha]
  · change (-D.1 (phaseToCanonical X)).b = 0
    simp [hb]

theorem preservesPhase_lie
    {D E : Derivation}
    (hD : PreservesPhase D) (hE : PreservesPhase E) :
    PreservesPhase ⁅D, E⁆ := by
  intro X
  let EX : Phase := phaseAction E X
  let DX : Phase := phaseAction D X
  have hEX : phaseToCanonical EX = E.1 (phaseToCanonical X) :=
    phaseToCanonical_phaseAction hE X
  have hDX : phaseToCanonical DX = D.1 (phaseToCanonical X) :=
    phaseToCanonical_phaseAction hD X
  have hDEX := hD EX
  have hEDX := hE DX
  rw [hEX] at hDEX
  rw [hDX] at hEDX
  rcases hDEX with ⟨hDEXa, hDEXb⟩
  rcases hEDX with ⟨hEDXa, hEDXb⟩
  constructor
  · change (D.1 (E.1 (phaseToCanonical X)) -
      E.1 (D.1 (phaseToCanonical X))).a = 0
    simp [hDEXa, hEDXa]
  · change (D.1 (E.1 (phaseToCanonical X)) -
      E.1 (D.1 (phaseToCanonical X))).b = 0
    simp [hDEXb, hEDXb]

def PhasePreservingDerivation := {D : Derivation // PreservesPhase D}

noncomputable def phasePreservingDerivations :
    LieSubalgebra ℝ Derivation where
  carrier := {D | PreservesPhase D}
  zero_mem' := preservesPhase_zero
  add_mem' := by
    intro D E hD hE
    exact preservesPhase_add hD hE
  smul_mem' := by
    intro r D hD
    exact preservesPhase_smul r hD
  lie_mem' := by
    intro D E hD hE
    exact preservesPhase_lie hD hE

theorem phaseAction_zero : phaseAction (0 : Derivation) = 0 := by
  apply LinearMap.ext
  intro X
  rfl

theorem phaseAction_add (D E : Derivation) :
    phaseAction (D + E) = phaseAction D + phaseAction E := by
  apply LinearMap.ext
  intro X
  rfl

theorem phaseAction_smul (r : ℝ) (D : Derivation) :
    phaseAction (⟨r • D.1,
      canonicalZornDerivations.smul_mem r D.2⟩ : Derivation) =
      r • phaseAction D := by
  apply LinearMap.ext
  intro X
  rfl

theorem phaseAction_lie
    {D E : Derivation}
    (hD : PreservesPhase D) (hE : PreservesPhase E) :
    phaseAction ⁅D, E⁆ = symplecticCommutator (phaseAction D) (phaseAction E) := by
  apply LinearMap.ext
  intro X
  apply phaseToCanonical_injective
  rw [phaseToCanonical_phaseAction (preservesPhase_lie hD hE)]
  change D.1 (E.1 (phaseToCanonical X)) -
      E.1 (D.1 (phaseToCanonical X)) =
      phaseToCanonical (phaseAction D (phaseAction E X) -
        phaseAction E (phaseAction D X))
  rw [map_sub]
  rw [phaseToCanonical_phaseAction hD]
  rw [phaseToCanonical_phaseAction hE]
  rw [phaseToCanonical_phaseAction hE]
  rw [phaseToCanonical_phaseAction hD]

noncomputable def phasePreservingLieHom :
    phasePreservingDerivations →ₗ⁅ℝ⁆ PhaseEnd where
  toFun D := phaseAction D.1
  map_add' := by
    intro D E
    exact phaseAction_add D.1 E.1
  map_smul' := by
    intro r D
    exact phaseAction_smul r D.1
  map_lie' := by
    intro D E
    exact phaseAction_lie D.2 E.2

@[simp] theorem phasePreservingLieHom_apply
    (D : phasePreservingDerivations) :
    phasePreservingLieHom D = phaseAction D.1 := rfl

/-! The full canonical derivation algebra preserves the native Witt form.
    Restricting that theorem to the phase chart identifies the symmetric
    neutral pairing with the existing para-metric. -/

theorem nativeCanonicalWittPairing_phase
    (X Y : Phase) :
    nativeCanonicalWittPairing (phaseToCanonical X) (phaseToCanonical Y) =
      paraMetric X Y := by
  rcases X with ⟨q, p⟩
  rcases Y with ⟨r, s⟩
  simp [nativeCanonicalWittPairing, phaseToCanonical, phaseToPaper,
    paperCanonicalLinearEquiv, paraMetric, paraJ, omega,
    chiralPairing, InfoGeometry.Algebra.Vec3.dot,
    InfoGeometry.Algebra.ZornVectorMatrix.trace,
    InfoGeometry.Algebra.ZornVectorMatrix.mul,
    InfoGeometry.Algebra.ZornVectorMatrix.conj,
    InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem phaseAction_paraMetric_skew
    (D : phasePreservingDerivations) (X Y : Phase) :
    paraMetric (phaseAction D.1 X) Y +
        paraMetric X (phaseAction D.1 Y) = 0 := by
  have h := derivation_native_witt_skew D.1
      (phaseToCanonical X) (phaseToCanonical Y)
  rw [← phaseToCanonical_phaseAction D.2 X,
    ← phaseToCanonical_phaseAction D.2 Y] at h
  simpa [nativeCanonicalWittPairing_phase] using h

 def PreservesPolarization (D : phasePreservingDerivations) : Prop :=
  ∀ X : Phase, phaseAction D.1 (paraJ X) = paraJ (phaseAction D.1 X)

def polarizedPhaseDerivations :
    LieSubalgebra ℝ phasePreservingDerivations where
  carrier := {D | PreservesPolarization D}
  zero_mem' := by
    intro X
    change phaseAction (0 : Derivation) (paraJ X) =
      paraJ (phaseAction (0 : Derivation) X)
    change (0 : Phase) = paraJ 0
    ext i <;> norm_num [paraJ]
  add_mem' := by
    intro D E hD hE X
    change phaseAction (D.1 + E.1) (paraJ X) =
      paraJ (phaseAction (D.1 + E.1) X)
    rw [phaseAction_add]
    simp only [LinearMap.add_apply]
    rw [hD X, hE X]
    ext i <;> simp [paraJ] <;> ring
  smul_mem' := by
    intro r D hD X
    change (r • phaseAction D.1) (paraJ X) =
      paraJ ((r • phaseAction D.1) X)
    simp only [LinearMap.smul_apply]
    rw [hD X]
    rcases phaseAction D.1 X with ⟨q, p⟩
    ext i <;> simp [paraJ]
  lie_mem' := by
    intro D E hD hE X
    let d : Derivation := D.val
    let e : Derivation := E.val
    have hDphase : PreservesPhase d := D.property
    have hEphase : PreservesPhase e := E.property
    change phaseAction ⁅d, e⁆ (paraJ X) =
      paraJ (phaseAction ⁅d, e⁆ X)
    rw [phaseAction_lie hDphase hEphase]
    change phaseAction d (phaseAction e (paraJ X)) -
      phaseAction e (phaseAction d (paraJ X)) = _
    simp only [symplecticCommutator, LinearMap.sub_apply,
      LinearMap.comp_apply]
    rw [hD X, hE X, hD (phaseAction e X),
      hE (phaseAction d X)]
    ext i <;> simp [paraJ] <;> ring

theorem polarized_phaseAction_isOmegaSymplectic
    (D : polarizedPhaseDerivations) :
    IsOmegaSymplectic (phaseAction D.1.1) := by
  intro X Y
  have h := phaseAction_paraMetric_skew D.1 X (paraJ Y)
  rw [D.2 Y] at h
  simpa [paraMetric, paraJ] using h

noncomputable def canonicalDerivationPhaseLieHom :
    polarizedPhaseDerivations →ₗ⁅ℝ⁆ omegaSymplecticLieSubalgebra where
  toFun D := ⟨phaseAction D.1.1, polarized_phaseAction_isOmegaSymplectic D⟩
  map_add' := by
    intro D E
    apply Subtype.ext
    exact phaseAction_add D.1.1 E.1.1
  map_smul' := by
    intro r D
    apply Subtype.ext
    exact phaseAction_smul r D.1.1
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact phaseAction_lie D.1.2 E.1.2

@[simp] theorem canonicalDerivationPhaseLieHom_apply
    (D : polarizedPhaseDerivations) :
    (canonicalDerivationPhaseLieHom D : PhaseEnd) = phaseAction D.1.1 := rfl

end
end InfoGeometry.Canonical.CanonicalZornPhaseBridge
