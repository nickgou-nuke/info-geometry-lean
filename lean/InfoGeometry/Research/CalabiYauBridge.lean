import InfoGeometry.Research.PerelmanW

namespace InfoGeometry.Research.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Research.KaehlerGeometry
open InfoGeometry.Research.RicciMongeAmpere
open InfoGeometry.Research.PerelmanW
open InfoGeometry.Research.SpectralInference

section MongeAmpereRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Constant Monge-Ampere density scaffold:
there exists a global scalar density value `ρ₀`.
-/
def HasConstantMongeAmpereDensity (H : HessianGeometry E) : Prop :=
  ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0

/-- Ricci-flatness surrogate in this finite-dimensional scaffold. -/
def IsRicciFlat (R : RicciTensor E) : Prop :=
  ∀ u v : E, R u v = 0

lemma hasConstantMongeAmpereDensity_iff
    (H : HessianGeometry E) :
    HasConstantMongeAmpereDensity H
      ↔ ∃ ρ0 : ℝ, ∀ x : E, mongeAmpereDensity H x = ρ0 := Iff.rfl

lemma hasConstantMongeAmpereDensity_of_satisfiesMongeAmpere_const
    (H : HessianGeometry E) (ρ0 : ℝ)
    (hMA : SatisfiesMongeAmpere H (fun _ => ρ0)) :
    HasConstantMongeAmpereDensity H := by
  exact ⟨ρ0, hMA⟩

lemma satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity
    (H : HessianGeometry E)
    (hConst : HasConstantMongeAmpereDensity H) :
    ∃ ρ0 : ℝ, SatisfiesMongeAmpere H (fun _ => ρ0) := by
  rcases hConst with ⟨ρ0, hρ0⟩
  exact ⟨ρ0, hρ0⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma ricciTensor_eq_of_isRicciFlat
    {R₁ R₂ : RicciTensor E}
    (h₁ : IsRicciFlat R₁) (h₂ : IsRicciFlat R₂) :
    R₁ = R₂ := by
  funext u v
  rw [h₁ u v, h₂ u v]

lemma isEinsteinKaehlerAtWith_zero_of_isRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (hFlat : IsRicciFlat R) :
    IsEinsteinKaehlerAtWith 0 R K x := by
  intro u v
  rw [hFlat u v]
  ring

/--
Calabi-Yau bridge hypothesis:
constant Monge-Ampere density closes to Ricci-flatness.
-/
def ConstantMongeAmpereImpliesRicciFlat
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) : Prop :=
  HasConstantMongeAmpereDensity K.H → IsRicciFlat R

theorem isRicciFlat_of_constantMongeAmpere
    (R : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hBridge : ConstantMongeAmpereImpliesRicciFlat R K)
    (hConst : HasConstantMongeAmpereDensity K.H) :
    IsRicciFlat R :=
  hBridge hConst

/--
Uniqueness scaffold:
if two Ricci tensors are both obtained from the same constant Monge-Ampere
bridge closure, they coincide.
-/
theorem ricciTensor_unique_of_constantMongeAmpere
    (R₁ R₂ : RicciTensor E) (K : KaehlerInformationGeometry E)
    (hBridge₁ : ConstantMongeAmpereImpliesRicciFlat R₁ K)
    (hBridge₂ : ConstantMongeAmpereImpliesRicciFlat R₂ K)
    (hConst : HasConstantMongeAmpereDensity K.H) :
    R₁ = R₂ := by
  apply ricciTensor_eq_of_isRicciFlat
  · exact hBridge₁ hConst
  · exact hBridge₂ hConst

/--
Constant Monge-Ampere + bridge closure yields the vacuum Einstein equation
at scalar closure `R = 2Λ` (the `c = 0` Einstein-Kaehler branch).
-/
theorem vacuumEinsteinEquation_of_constantMongeAmpere
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (Λ : ℝ)
    (hBridge : ConstantMongeAmpereImpliesRicciFlat R K)
    (hConst : HasConstantMongeAmpereDensity K.H) :
    VacuumEinsteinEquationAt R K x (2 * Λ) Λ := by
  have hFlat : IsRicciFlat R := hBridge hConst
  have hEin0 : IsEinsteinKaehlerAtWith 0 R K x :=
    isEinsteinKaehlerAtWith_zero_of_isRicciFlat (R := R) (K := K) (x := x) hFlat
  exact vacuumEinsteinEquation_of_scalar_relation
    (c := 0) (R := R) (K := K) (x := x) (scalar := 2 * Λ) (Λ := Λ)
    hEin0 (by ring)

end MongeAmpereRicci

section WBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/--
Calabi-Yau spectral closure hypothesis:
constant Monge-Ampere density forces vanishing spinorial scalar curvature.
-/
def ConstantMongeAmpereImpliesZeroSpinorial
    (IST : InfoSpectralTriple E) : Prop :=
  HasConstantMongeAmpereDensity IST.H → spinorialScalarCurvature IST = 0

theorem spinorialScalarCurvature_eq_zero_of_constantMongeAmpere
    (IST : InfoSpectralTriple E)
    (hCY : ConstantMongeAmpereImpliesZeroSpinorial IST)
    (hConst : HasConstantMongeAmpereDensity IST.H) :
    spinorialScalarCurvature IST = 0 :=
  hCY hConst

/--
Connection to the `W`-flow layer:
under normalized spinorial tracking, Calabi-Yau closure makes `W` constant.
-/
theorem W_constant_of_constantMongeAmpere
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = spinorialWDissipation flow IST s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hCY : ConstantMongeAmpereImpliesZeroSpinorial IST)
    (hConst : HasConstantMongeAmpereDensity IST.H) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  exact W_constant_of_spinorial_zero
    (E := E) (flow := flow) (IST := IST) (W := W)
    hDiff hW hNorm hTrack (hCY hConst)

end WBridge

end InfoGeometry.Research.CalabiYauBridge
