import InfoGeometry.Canonical.PerelmanW

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.SpectralInference

section MongeAmpereRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Constant Monge-Ampere density scaffold:
there exists a global scalar density value `ρ₀`.
-/
def HasConstantMongeAmpereDensity (H : HessianGeometry E) : Prop :=
  ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0

/-- Ricci-flatness condition in this finite-dimensional scaffold. -/
def IsRicciFlat (R : RicciTensor E) : Prop :=
  ∀ u v : E, R u v = 0

/-- Constructive Calabi-Yau geometric state (non-bridge form). -/
abbrev CalabiYauRicciState (R : RicciTensor E) : Prop :=
  IsRicciFlat R

/--
Constructive closure state for the Monge-Ampere-to-Ricci layer:
constant Monge-Ampere density together with an explicit Ricci-flat witness.
-/
def MongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) : Prop :=
  HasConstantMongeAmpereDensity K.H ∧ IsRicciFlat R

/-- Lemma `hasConstantMongeAmpereDensity_iff`. -/
lemma hasConstantMongeAmpereDensity_iff
    (H : HessianGeometry E) :
    HasConstantMongeAmpereDensity H
      ↔ ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0 := Iff.rfl

/-- Lemma `hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const`. -/
lemma hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const
    (H : HessianGeometry E) (ρ0 : ℝ)
    (hMA : SatisfiesMongeAmpere H (fun _ => ρ0)) :
    HasConstantMongeAmpereDensity H := by
  exact ⟨ρ0, hMA⟩

/-- Lemma `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity`. -/
lemma satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity
    (H : HessianGeometry E)
    (hConst : HasConstantMongeAmpereDensity H) :
    ∃ ρ0 : ℝ, SatisfiesMongeAmpere H (fun _ => ρ0) := by
  rcases hConst with ⟨ρ0, hρ0⟩
  exact ⟨ρ0, hρ0⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Lemma `ricciTensor_eq_of_isRicciFlat`. -/
lemma ricciTensor_eq_of_isRicciFlat
    {R₁ R₂ : RicciTensor E}
    (h₁ : IsRicciFlat R₁) (h₂ : IsRicciFlat R₂) :
    R₁ = R₂ := by
  funext u v
  rw [h₁ u v, h₂ u v]

/-- Lemma `isEinsteinKaehlerAtWith_zero_of_isRicciFlat`. -/
lemma isEinsteinKaehlerAtWith_zero_of_isRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hFlat : IsRicciFlat R) :
    IsEinsteinKaehlerAtWith 0 R K x := by
  intro u v
  rw [hFlat u v]
  ring

/-- Projection: a `MongeAmpereRicciState` carries the constant-density witness. -/
theorem hasConstantMongeAmpereDensity_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    HasConstantMongeAmpereDensity K.H :=
  hState.1

/-- Projection: a `MongeAmpereRicciState` carries Ricci-flatness. -/
theorem isRicciFlat_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState : MongeAmpereRicciState R K) :
    IsRicciFlat R :=
  hState.2

/--
Constructive state packaging:
constant Monge-Ampere density and explicit Ricci-flatness form the closure state.
-/
theorem mongeAmpereRicciState_mk
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hConst : HasConstantMongeAmpereDensity K.H)
    (hFlat : IsRicciFlat R) :
    MongeAmpereRicciState R K := by
  exact ⟨hConst, hFlat⟩

/--
Uniqueness under constructive closure states:
if two Ricci tensors are both Ricci-flat under the same geometry scaffold, they coincide.
-/
theorem ricciTensor_unique_of_mongeAmpereRicciState
    (R₁ R₂ : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hState₁ : MongeAmpereRicciState R₁ K)
    (hState₂ : MongeAmpereRicciState R₂ K) :
    R₁ = R₂ := by
  exact ricciTensor_eq_of_isRicciFlat hState₁.2 hState₂.2

/--
Constructive vacuum Einstein closure from an explicit Ricci-flat witness
(non-bridge form).
-/
theorem vacuumEinsteinEquation_of_isRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hFlat : IsRicciFlat R) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  have hEin0 : IsEinsteinKaehlerAtWith 0 R K x :=
    isEinsteinKaehlerAtWith_zero_of_isRicciFlat (R := R) (K := K) (x := x) hFlat
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := 0) (R := R) (K := K) (x := x) (scalar := 2 * Λ) (Λ := Λ)
    hEin0 (by ring)

/--
Constructive closure theorem in state form:
from `MongeAmpereRicciState` we obtain the vacuum Einstein equation.
-/
theorem vacuumEinsteinEquation_of_mongeAmpereRicciState
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hState : MongeAmpereRicciState R K) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_isRicciFlat
    (R := R) (K := K) (x := x) (Λ := Λ) hState.2

end MongeAmpereRicci

section WBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Constructive Calabi-Yau spectral closure state:
constant Monge-Ampere density together with vanishing spinorial scalar curvature.
-/
def MongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E) : Prop :=
  HasConstantMongeAmpereDensity IST.H ∧ spinorialScalarCurvature IST = 0

/-- Constructive spectral Calabi-Yau state (non-bridge form). -/
def CalabiYauSpinorialState (IST : InfoSpectralTriple E) : Prop :=
  spinorialScalarCurvature IST = 0

/-- Constructor for the spinorial closure state. -/
theorem mongeAmpereSpinorialClosure_mk
    (IST : InfoSpectralTriple E)
    (hConst : HasConstantMongeAmpereDensity IST.H)
    (hSpin0 : CalabiYauSpinorialState IST) :
    MongeAmpereSpinorialClosure IST := by
  exact ⟨hConst, hSpin0⟩

/-- Extract spinorial vanishing from the constructive spinorial closure state. -/
theorem spinorialScalarCurvature_eq_zero_of_mongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E)
    (hCY : MongeAmpereSpinorialClosure IST) :
    CalabiYauSpinorialState IST :=
  hCY.2

/--
Connection to the `W`-flow layer:
under normalized spinorial tracking, Calabi-Yau closure makes `W` constant.
-/
theorem W_constant_of_mongeAmpereSpinorialClosure
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hCY : MongeAmpereSpinorialClosure IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  exact W_constant_of_spinorial_zero
    (E := E) (flow := flow) (IST := IST) (W := W)
    hDiff hW hNorm hTrack hCY.2

/--
Constructive `W`-constancy closure from an explicit zero-spinorial witness
(non-bridge form).
-/
theorem W_constant_of_spinorialState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin0 : CalabiYauSpinorialState IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  exact W_constant_of_spinorial_zero
    (E := E) (flow := flow) (IST := IST) (W := W)
    hDiff hW hNorm hTrack hSpin0

end WBridge

end InfoGeometry.Canonical.CalabiYauBridge
