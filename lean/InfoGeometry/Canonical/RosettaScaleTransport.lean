import InfoGeometry.Canonical.AnalyticalIndex
import InfoGeometry.Canonical.GrandUnification
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.KK.KasparovCycle

/-!
# Research.RosettaScaleTransport

Lower Rosetta ownership for the Weyl scale-transport lanes:

- endomorphism-valued shadows feeding the KK analytical-index interface
- scalar shadows feeding the Jordan/KKT divergence interface
-/

namespace InfoGeometry.Canonical.Rosetta

section WeylScaleKkRosetta

open InfoGeometry.Canonical.AnalyticalIndex
open InfoGeometry.Krein

variable {I F A P : Type*}
variable [Group P]
variable {H A₀ B₀ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]

/--
Endomorphism-valued shadow of a Weyl scale-transport observable along a chosen
real parameterization.
-/
noncomputable def weylScaleTransportShadow
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I) :
    ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H :=
  fun s => realize <|
    InfoGeometry.Canonical.ScaleEquivariantFlow.transportObservable Ξ phaseOf (path 0) (path s)

/-- Pointwise expansion of `weylScaleTransportShadow`. -/
@[simp] theorem weylScaleTransportShadow_apply
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (s : ℝ) :
    weylScaleTransportShadow (H := H) Ξ phaseOf realize path s =
      realize (InfoGeometry.Canonical.ScaleEquivariantFlow.transportObservable Ξ phaseOf (path 0) (path s)) := by
  rfl

/--
If a Weyl scale-transport shadow acts injectively on the carrier and transports
both chiral slices to the baseline through the Clifford label action, then it
instantiates the modular/Clifford transport hypothesis used by the analytical
index layer.
-/
private theorem weylScaleTransportShadow_to_modularCliffordTransport
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    ChiralSliceModularCliffordTransportAlong
      (D := D) (Γ := Γ)
      (weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
      clAct unit := by
  exact ⟨hUnit, hShadowInj, hPlusMap, hMinusMap⟩

/--
Weyl scale transport yields analytical-index invariance once its endomorphism
shadow satisfies the modular/Clifford slice-transport requirements.
-/
private theorem indexInvariantAlong_of_weylScaleTransport
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_modularCliffordTransport
    (D := D) (Γ := Γ)
    (σ := weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
    (clAct := clAct)
    (unit := unit)
    (weylScaleTransportShadow_to_modularCliffordTransport
      (H := H)
      (Ξ := Ξ) (phaseOf := phaseOf) (realize := realize) (path := path)
      (D := D) (Γ := Γ)
      (clAct := clAct) (unit := unit)
      hUnit hShadowInj hPlusMap hMinusMap)

/--
KK analytical-index bridge specialized to a Weyl scale-transport shadow.
This is the missing Rosetta step from the Weyl/scale lane into the modular /
Clifford / KK invariance theorem surface.
-/
theorem kk_analyticalIndex_eq_of_weylScaleTransport
    [NormedRing A₀] [NormedRing B₀]
    [NormedAlgebra ℝ A₀] [NormedAlgebra ℝ B₀]
    [KreinSpace H] [KreinGradedModule H]
    (Xk : InfoGeometry.KK.KasparovCycle A₀ B₀ H)
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (realize : P → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (path : ℝ → I)
    (D Γ : ℝ → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    {ι : Type*}
    (clAct : ι → InfoGeometry.Canonical.BottDirac.Endomorphism H)
    (unit : ι)
    (hD0 : D 0 = Xk.F.toLinearMap)
    (hΓ0 : Γ 0 = (KreinGradedModule.gradeCLM (H := H)).toLinearMap)
    (hUnit : clAct unit = LinearMap.id)
    (hShadowInj : ∀ s : ℝ,
      Function.Injective (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
    (hPlusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSlicePlus (D 0) (Γ 0))
    (hMinusMap : ∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map
          ((clAct ℓ).comp (weylScaleTransportShadow (H := H) Ξ phaseOf realize path s))
        = chiralKernelSliceMinus (D 0) (Γ 0)) :
    ∀ s : ℝ,
      InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex (D s) (Γ s) =
        Xk.analyticalIndex := by
  exact InfoGeometry.KK.analyticalIndex_eq_of_modularCliffordTransport
    (X := Xk)
    (D := D)
    (Γ := Γ)
    (σ := weylScaleTransportShadow (H := H) Ξ phaseOf realize path)
    (clAct := clAct)
    (unit := unit)
    hD0
    hΓ0
    (weylScaleTransportShadow_to_modularCliffordTransport
      (H := H)
      (Ξ := Ξ) (phaseOf := phaseOf) (realize := realize) (path := path)
      (D := D) (Γ := Γ)
      (clAct := clAct) (unit := unit)
      hUnit hShadowInj hPlusMap hMinusMap)

end WeylScaleKkRosetta

section WeylScaleJordanRosetta

variable {I F A P E : Type*}
variable [Group P]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Scalar readout of a Weyl scale-transport observable. -/
noncomputable def weylScaleTransportScalarShadow
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ) :
    I → I → ℝ :=
  fun i j => scalarOf (InfoGeometry.Canonical.ScaleEquivariantFlow.transportObservable Ξ phaseOf i j)

/-- Pointwise expansion of `weylScaleTransportScalarShadow`. -/
@[simp] theorem weylScaleTransportScalarShadow_apply
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (i j : I) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf i j =
      scalarOf (InfoGeometry.Canonical.ScaleEquivariantFlow.transportObservable Ξ phaseOf i j) := by
  rfl

/--
If a Weyl scale-transport scalar shadow agrees with the dual-flat divergence,
then any Jordan/KKT realization of that divergence reads the same shadow as the
Jordan Bregman divergence.
-/
theorem weylScaleTransportScalarShadow_eq_jordanBregman_of_isJordanKKTGeometry
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (S : InfoGeometry.Geometry.DualFlat.DualFlatStructure E)
    (hJG : InfoGeometry.Canonical.GrandUnification.IsJordanKKTGeometry J S)
    (hShadowDiv : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        InfoGeometry.Geometry.DualFlat.divergence S x y) :
    ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y := by
  intro x y
  rw [hShadowDiv x y]
  exact InfoGeometry.Canonical.GrandUnification.geometry_divergence_eq_jordan_bregman
    (J := J) (S := S) hJG x y

/--
Conversely, if the same Weyl scale-transport shadow reads both the dual-flat
Divergence and the Jordan Bregman divergence, it furnishes the full
Jordan/KKT geometry witness.
-/
theorem isJordanKKTGeometry_of_weylScaleTransportShadow
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (S : InfoGeometry.Geometry.DualFlat.DualFlatStructure E)
    (hShadowDiv : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        InfoGeometry.Geometry.DualFlat.divergence S x y)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y) :
    InfoGeometry.Canonical.GrandUnification.IsJordanKKTGeometry J S := by
  intro x y
  rw [← hShadowDiv x y, hShadowJ x y]

/-- Transported scalar shadow vanishes on the diagonal in the Jordan/KKT lane. -/
@[simp] theorem weylScaleTransportScalarShadow_self_eq_zero_of_jordanBregman
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x : E) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf x) = 0 := by
  rw [hShadowJ x x]
  exact J.DBregman_self x

/-- Transported scalar shadow is nonnegative in the Jordan/KKT lane. -/
theorem weylScaleTransportScalarShadow_nonneg_of_jordanBregman
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y : E) :
    0 ≤ weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) := by
  rw [hShadowJ x y]
  exact J.DBregman_nonneg x y

/-- Transported scalar shadow detects equality in the Jordan/KKT lane. -/
theorem weylScaleTransportScalarShadow_eq_zero_iff_of_jordanBregman
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y : E) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) = 0 ↔ x = y := by
  rw [hShadowJ x y]
  exact J.DBregman_eq_zero_iff x y

/--
The generalized Pythagorean law transports from Jordan/KKT geometry to the
Weyl scale shadow once the shadow reads the Jordan Bregman divergence.
-/
theorem weylScaleTransportScalarShadow_generalized_pythagorean_of_jordanBregman
    (Ξ : InfoGeometry.Canonical.ScaleEquivariantFlow I F A)
    (phaseOf : A → P)
    (scalarOf : P → ℝ)
    (indexOf : E → I)
    (J : InfoGeometry.Canonical.GrandUnification.JordanKKTData E)
    (hShadowJ : ∀ x y : E,
      weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y) =
        J.DBregman x y)
    (x y z : E)
    (hOrth : J.IsBregmanOrthogonal x y z) :
    weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf y)
      + weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf y) (indexOf z)
      = weylScaleTransportScalarShadow Ξ phaseOf scalarOf (indexOf x) (indexOf z) := by
  rw [hShadowJ x y, hShadowJ y z, hShadowJ x z]
  exact J.generalized_pythagorean_theorem x y z hOrth

end WeylScaleJordanRosetta

end InfoGeometry.Canonical.Rosetta
