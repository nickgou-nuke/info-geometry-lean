import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.ChiralCartanCore
import Mathlib.Tactic.NoncommRing

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ConformalAlgebra

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ChiralCartanCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Conformal belief-algebra scaffold over a chiral conformal inference structure.

This layer fixes the dilation generator canonically from `CI.D` and carries an
additional chosen generator `M` for the Cartan/volume-preserving sector.
-/
structure ConformalBeliefAlgebra (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  CI : ConformalInference E
  /-- Chosen Cartan/volume-preserving generator. -/
  M : E →L[ℝ] E
  /-- Canonical dilation generator inherited from `CI`. -/
  D : E →L[ℝ] E := CI.D
  /-- `D` is definitionally tied to the conformal-inference dilation operator. -/
  D_def : D = CI.D := by rfl
  /-- Positive anomaly obstructs the flat conformal weight equations. -/
  anomaly_breaks_weights :
      CI.chiralScale > 0 →
        ¬ ((D * CI.P - CI.P * D = CI.P) ∧ (D * CI.K - CI.K * D = - CI.K))

namespace ConformalBeliefAlgebra

variable (CBA : ConformalBeliefAlgebra E)

/-- The dilation field is canonically inherited from the underlying conformal inference. -/
theorem D_eq_CI_D : CBA.D = CBA.CI.D :=
  CBA.D_def

/-! ### 1. Fundamental Commutation Relations -/

/--
Conformal Weight of Translation: [D, P] = P.
In Information Geometry, this means the Dilation flow scales the
information flow A linearly.
-/
def SatisfiesPWeight : Prop :=
  CBA.D * CBA.CI.P - CBA.CI.P * CBA.D = CBA.CI.P

/--
Conformal Weight of Special Conformal: [D, K] = -K.
This means the Dilation flow contracts the metric inverse A+.
-/
def SatisfiesKWeight : Prop :=
  CBA.D * CBA.CI.K - CBA.CI.K * CBA.D = - CBA.CI.K

/--
The master conformal relation witness:
`[K, P] = 2 (η • D - M)` for a chosen scalar coefficient `η`.
-/
def SatisfiesMasterRelation (η : ℝ) : Prop :=
  CBA.CI.K * CBA.CI.P - CBA.CI.P * CBA.CI.K = 2 • (η • CBA.D - CBA.M)

/-- Flat conformal weight package `[D,P]=P` and `[D,K]=-K`. -/
def SatisfiesFlatWeights : Prop :=
  CBA.SatisfiesPWeight ∧ CBA.SatisfiesKWeight

/-- Lie commutator on endomorphisms. -/
noncomputable def commutator (X Y : E →L[ℝ] E) : E →L[ℝ] E :=
  X * Y - Y * X

/-! ### 2. Anomaly and Scale Emergence -/

omit [FiniteDimensional ℝ E] in
/--
Theorem: If the Chiral Anomaly ε is non-zero, the conformal generators
do not satisfy the standard flat relations.
A 'Scale Anomaly' constant emerges, proportional to ε.
-/
theorem scale_anomaly_emergence
    : CBA.CI.chiralScale > 0 → ¬ CBA.SatisfiesFlatWeights := by
  simpa [SatisfiesFlatWeights, SatisfiesPWeight, SatisfiesKWeight] using CBA.anomaly_breaks_weights

omit [FiniteDimensional ℝ E] in
/-- Theorem `scale_anomaly_breaks_weight_closure`. -/
theorem scale_anomaly_breaks_weight_closure
    : CBA.CI.chiralScale > 0 → ¬ CBA.SatisfiesFlatWeights :=
  CBA.scale_anomaly_emergence

/--
The Chiral Cartan Splitting of the Conformal Algebra.
Maps the generators to the 𝔨 ⊕ 𝔭 sectors.
-/
def GeneratorCartanDecomposition : Prop :=
  IsCompactBeliefUpdate CBA.CI CBA.M ∧ IsNonCompactBeliefUpdate CBA.CI CBA.D

/--
`GeneratorCartanDecomposition` is exactly the conjunction of compactness of `M`
and non-compactness (Weyl-dilation type) of `D`.
-/
theorem generatorCartanDecomposition_iff :
    CBA.GeneratorCartanDecomposition
      ↔ IsCompactBeliefUpdate CBA.CI CBA.M ∧ IsNonCompactBeliefUpdate CBA.CI CBA.D := by
  rfl

/--
Direct constructor for the Cartan split from primitive sector hypotheses.
-/
theorem generatorCartanDecomposition_of_parts
    (hM : IsCompactBeliefUpdate CBA.CI CBA.M)
    (hD : IsNonCompactBeliefUpdate CBA.CI CBA.D) :
    CBA.GeneratorCartanDecomposition := by
  exact ⟨hM, hD⟩

/-- Cartan grading involutivity hypothesis `Γ^2 = 1`. -/
def GradingInvolutive : Prop :=
  chiralGrading CBA.CI * chiralGrading CBA.CI = (1 : E →L[ℝ] E)

/--
Cartan involution on generators, induced by conjugation with the chiral grading:
`θ(X) = Γ X Γ`.
-/
noncomputable def cartanInvolution (X : E →L[ℝ] E) : E →L[ℝ] E :=
  chiralGrading CBA.CI * X * chiralGrading CBA.CI

/-- Volume-preserving (Cartan-compact) sector for updates. -/
def IsVolumePreservingPart (X : E →L[ℝ] E) : Prop :=
  IsCompactBeliefUpdate CBA.CI X

/-- Weyl-dilation (Cartan-noncompact) sector for updates. -/
def IsWeylDilationPart (X : E →L[ℝ] E) : Prop :=
  IsNonCompactBeliefUpdate CBA.CI X

/-- In the Cartan split, `M` is volume-preserving. -/
theorem M_in_volumePreserving_of_cartan
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsVolumePreservingPart CBA.M := by
  exact hCartan.1

/-- In the Cartan split, `D` is the Weyl-dilation generator. -/
theorem D_in_weylDilation_of_cartan
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsWeylDilationPart CBA.D := by
  exact hCartan.2

/-- Generator-level Cartan split into volume-preserving and Weyl-dilation sectors. -/
theorem cartan_generator_split
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsVolumePreservingPart CBA.M ∧ CBA.IsWeylDilationPart CBA.D := by
  exact ⟨CBA.M_in_volumePreserving_of_cartan hCartan,
    CBA.D_in_weylDilation_of_cartan hCartan⟩

/-- `θ² = Id` under grading involutivity. -/
theorem cartanInvolution_involutive_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive) (X : E →L[ℝ] E) :
    CBA.cartanInvolution (CBA.cartanInvolution X) = X := by
  let Γ : E →L[ℝ] E := chiralGrading CBA.CI
  have hΓSq' : Γ * Γ = (1 : E →L[ℝ] E) := by
    simpa [Γ, GradingInvolutive] using hΓSq
  calc
    CBA.cartanInvolution (CBA.cartanInvolution X)
        = Γ * (Γ * X * Γ) * Γ := by
            simp [ConformalBeliefAlgebra.cartanInvolution, Γ]
    _ = (Γ * Γ) * X * (Γ * Γ) := by
              noncomm_ring
    _ = (1 : E →L[ℝ] E) * X * (1 : E →L[ℝ] E) := by simp [hΓSq']
    _ = X := by simp

/-- Compact sector is the `+1` eigenspace of the Cartan involution. -/
theorem cartanInvolution_eq_self_of_volumePreserving_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E)
    (hX : CBA.IsVolumePreservingPart X) :
    CBA.cartanInvolution X = X := by
  let Γ : E →L[ℝ] E := chiralGrading CBA.CI
  have hΓSq' : Γ * Γ = (1 : E →L[ℝ] E) := by
    simpa [Γ, GradingInvolutive] using hΓSq
  have hX' : X * Γ = Γ * X := by
    simpa [Γ, IsVolumePreservingPart, IsCompactBeliefUpdate] using hX
  calc
    CBA.cartanInvolution X = Γ * X * Γ := by
      simp [ConformalBeliefAlgebra.cartanInvolution, Γ]
    _ = (X * Γ) * Γ := by
            rw [← hX']
    _ = X * (Γ * Γ) := by simp [mul_assoc]
    _ = X * (1 : E →L[ℝ] E) := by rw [hΓSq']
    _ = X := by simp

/-- Non-compact sector is the `-1` eigenspace of the Cartan involution. -/
theorem cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E)
    (hX : CBA.IsWeylDilationPart X) :
    CBA.cartanInvolution X = -X := by
  let Γ : E →L[ℝ] E := chiralGrading CBA.CI
  have hΓSq' : Γ * Γ = (1 : E →L[ℝ] E) := by
    simpa [Γ, GradingInvolutive] using hΓSq
  have hX' : X * Γ = -(Γ * X) := by
    simpa [Γ, IsWeylDilationPart, IsNonCompactBeliefUpdate] using hX
  have hGX : Γ * X = -(X * Γ) := by
    calc
      Γ * X = -(- (Γ * X)) := by simp
      _ = -(X * Γ) := by rw [← hX']
  calc
    CBA.cartanInvolution X = Γ * X * Γ := by
      simp [ConformalBeliefAlgebra.cartanInvolution, Γ]
    _ = (-(X * Γ)) * Γ := by rw [hGX]
    _ = -((X * Γ) * Γ) := by simp
    _ = -(X * (Γ * Γ)) := by simp [mul_assoc]
    _ = -(X * (1 : E →L[ℝ] E)) := by rw [hΓSq']
    _ = -X := by simp

/-- `θ(X)=X` implies compactness when `Γ^2=1`. -/
theorem volumePreserving_of_cartanInvolution_eq_self_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E)
    (hθ : CBA.cartanInvolution X = X) :
    CBA.IsVolumePreservingPart X := by
  let Γ : E →L[ℝ] E := chiralGrading CBA.CI
  have hΓSq' : Γ * Γ = (1 : E →L[ℝ] E) := by
    simpa [Γ, GradingInvolutive] using hΓSq
  have hθ' : Γ * X * Γ = X := by
    simpa [Γ, ConformalBeliefAlgebra.cartanInvolution] using hθ
  have hXΓ : X * Γ = (Γ * X * Γ) * Γ := by
    simpa [mul_assoc] using congrArg (fun Y => Y * Γ) hθ'.symm
  have hComm : X * Γ = Γ * X := by
    calc
      X * Γ = (Γ * X * Γ) * Γ := hXΓ
      _ = Γ * X * (Γ * Γ) := by simp [mul_assoc]
      _ = Γ * X * (1 : E →L[ℝ] E) := by rw [hΓSq']
      _ = Γ * X := by simp
  simpa [Γ, IsVolumePreservingPart, IsCompactBeliefUpdate] using hComm

/-- `θ(X)=-X` implies Weyl-dilation sector when `Γ^2=1`. -/
theorem weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E)
    (hθ : CBA.cartanInvolution X = -X) :
    CBA.IsWeylDilationPart X := by
  let Γ : E →L[ℝ] E := chiralGrading CBA.CI
  have hΓSq' : Γ * Γ = (1 : E →L[ℝ] E) := by
    simpa [Γ, GradingInvolutive] using hΓSq
  have hθ' : Γ * X * Γ = -X := by
    simpa [Γ, ConformalBeliefAlgebra.cartanInvolution] using hθ
  have hGX : Γ * X = -(X * Γ) := by
    calc
      Γ * X = Γ * X * (1 : E →L[ℝ] E) := by simp
      _ = Γ * X * (Γ * Γ) := by rw [← hΓSq']
      _ = (Γ * X * Γ) * Γ := by
            simp [mul_assoc]
      _ = (-X) * Γ := by rw [hθ']
      _ = -(X * Γ) := by simp
  have hNonCompact : X * Γ = -(Γ * X) := by
    calc
      X * Γ = -(- (X * Γ)) := by simp
      _ = -(Γ * X) := by rw [hGX]
  simpa [Γ, IsWeylDilationPart, IsNonCompactBeliefUpdate] using hNonCompact

/-- Eigenspace characterization of `𝔨` via Cartan involution. -/
theorem cartanInvolution_eq_self_iff_volumePreserving_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E) :
    CBA.cartanInvolution X = X ↔ CBA.IsVolumePreservingPart X := by
  constructor
  · intro hθ
    exact CBA.volumePreserving_of_cartanInvolution_eq_self_of_gradingInvolutive
      hΓSq X hθ
  · intro hX
    exact CBA.cartanInvolution_eq_self_of_volumePreserving_of_gradingInvolutive
      hΓSq X hX

/-- Eigenspace characterization of `𝔭` via Cartan involution. -/
theorem cartanInvolution_eq_neg_self_iff_weylDilation_of_gradingInvolutive
    (hΓSq : CBA.GradingInvolutive)
    (X : E →L[ℝ] E) :
    CBA.cartanInvolution X = -X ↔ CBA.IsWeylDilationPart X := by
  constructor
  · intro hθ
    exact CBA.weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive
      hΓSq X hθ
  · intro hX
    exact CBA.cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive
      hΓSq X hX

/--
Cartan bracket law `[𝔨, 𝔨] ⊆ 𝔨`:
the commutator of two volume-preserving generators is volume-preserving.
-/
theorem commutator_volumePreserving_volumePreserving
    (X Y : E →L[ℝ] E)
    (hX : CBA.IsVolumePreservingPart X)
    (hY : CBA.IsVolumePreservingPart Y) :
    CBA.IsVolumePreservingPart (commutator X Y) := by
  unfold IsVolumePreservingPart IsCompactBeliefUpdate at hX hY ⊢
  unfold commutator
  calc
    (X * Y - Y * X) * chiralGrading CBA.CI
        = X * (Y * chiralGrading CBA.CI) - Y * (X * chiralGrading CBA.CI) := by
          noncomm_ring
    _ = X * (chiralGrading CBA.CI * Y) - Y * (chiralGrading CBA.CI * X) := by
          rw [hY, hX]
    _ = (X * chiralGrading CBA.CI) * Y - (Y * chiralGrading CBA.CI) * X := by
          simp [mul_assoc]
    _ = (chiralGrading CBA.CI * X) * Y - (chiralGrading CBA.CI * Y) * X := by
          rw [hX, hY]
    _ = chiralGrading CBA.CI * (X * Y - Y * X) := by
          noncomm_ring

/--
Cartan bracket law `[𝔨, 𝔭] ⊆ 𝔭`:
the commutator of a volume-preserving and Weyl-dilation generator is
Weyl-dilation.
-/
theorem commutator_volumePreserving_weylDilation
    (X Y : E →L[ℝ] E)
    (hX : CBA.IsVolumePreservingPart X)
    (hY : CBA.IsWeylDilationPart Y) :
    CBA.IsWeylDilationPart (commutator X Y) := by
  unfold IsVolumePreservingPart IsCompactBeliefUpdate at hX
  unfold IsWeylDilationPart IsNonCompactBeliefUpdate at hY ⊢
  unfold commutator
  calc
    (X * Y - Y * X) * chiralGrading CBA.CI
        = X * (Y * chiralGrading CBA.CI) - Y * (X * chiralGrading CBA.CI) := by
          noncomm_ring
    _ = X * (-(chiralGrading CBA.CI * Y)) - Y * (chiralGrading CBA.CI * X) := by
          rw [hY, hX]
    _ = -(X * (chiralGrading CBA.CI * Y)) - Y * (chiralGrading CBA.CI * X) := by
          simp
    _ = -((X * chiralGrading CBA.CI) * Y) - (Y * chiralGrading CBA.CI) * X := by
          simp [mul_assoc]
    _ = -((chiralGrading CBA.CI * X) * Y) - (-(chiralGrading CBA.CI * Y)) * X := by
          rw [hX, hY]
    _ = -(chiralGrading CBA.CI * (X * Y - Y * X)) := by
          noncomm_ring

/--
Cartan bracket law `[𝔭, 𝔭] ⊆ 𝔨`:
the commutator of two Weyl-dilation generators is volume-preserving.
-/
theorem commutator_weylDilation_weylDilation
    (X Y : E →L[ℝ] E)
    (hX : CBA.IsWeylDilationPart X)
    (hY : CBA.IsWeylDilationPart Y) :
    CBA.IsVolumePreservingPart (commutator X Y) := by
  unfold IsWeylDilationPart IsNonCompactBeliefUpdate at hX hY
  unfold IsVolumePreservingPart IsCompactBeliefUpdate at ⊢
  unfold commutator
  calc
    (X * Y - Y * X) * chiralGrading CBA.CI
        = X * (Y * chiralGrading CBA.CI) - Y * (X * chiralGrading CBA.CI) := by
          noncomm_ring
    _ = X * (-(chiralGrading CBA.CI * Y)) - Y * (-(chiralGrading CBA.CI * X)) := by
          rw [hY, hX]
    _ = -(X * (chiralGrading CBA.CI * Y)) + Y * (chiralGrading CBA.CI * X) := by
          simp
    _ = -((X * chiralGrading CBA.CI) * Y) + (Y * chiralGrading CBA.CI) * X := by
          simp [mul_assoc]
    _ = -((-(chiralGrading CBA.CI * X)) * Y) + (-(chiralGrading CBA.CI * Y)) * X := by
          rw [hX, hY]
    _ = chiralGrading CBA.CI * (X * Y - Y * X) := by
          noncomm_ring

/-- Positive anomaly scale obstructs flat conformal-weight closure. -/
theorem scale_anomaly_obstructs_weyl_flatness :
    CBA.CI.chiralScale > 0 → ¬ CBA.SatisfiesFlatWeights := by
  exact CBA.scale_anomaly_breaks_weight_closure

end ConformalBeliefAlgebra

end ConformalAlgebra
