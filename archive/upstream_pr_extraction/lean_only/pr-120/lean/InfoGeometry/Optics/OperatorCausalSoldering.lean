import InfoGeometry.Clifford.OperatorValuedJonesProduct
import InfoGeometry.Optics.OperatorValuedCliffordJones
import InfoGeometry.Optics.OperatorLiftCarrier
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Operator-valued causal soldering

This file joins three existing owner layers:

* four causal components with coefficients in `End(W)`;
* their reconstruction as `M₂(End(W))`;
* the faithful action of that matrix on the doubled carrier `Fin 2 → W`.

It also transports the genuine algebraic curvature `dΩ + Ω ∧ Ω` through the
matrix reconstruction.  No scalar-coordinate replacement is made.
-/

noncomputable section

namespace InfoGeometry.Optics.OperatorCausalSoldering

open InfoGeometry.Clifford
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.OperatorLiftCarrier
open InfoGeometry.Optics.OperatorValuedCliffordJones

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Internal operator coefficients. -/
abbrev EndW (W : Type*) [AddCommGroup W] [Module ℂ W] := Module.End ℂ W

/-- A genuine four-vector whose entries are operators on `W`, not scalars. -/
abbrev OperatorFourVector (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Fin 4 → EndW W

/-- Causal ordering `(scalar, chiral, exchange, circular) = (0,3,1,2)`. -/
def causalCoordinatesOfFourVector (v : OperatorFourVector W) :
    CausalOperatorCoordinates (EndW W) :=
  ⟨v 0, v 3, v 1, v 2⟩

/-- Operator-valued Pauli/Dirac soldering into `M₂(End(W))`. -/
def operatorSoldering (v : OperatorFourVector W) :
    OperatorMatrix (R := ℂ) (W := W) :=
  reconstruct_causal (causalCoordinatesOfFourVector v)

/-- The soldered operator matrix acting on the doubled sheet carrier. -/
def operatorSolderingAction (v : OperatorFourVector W) :
    Module.End ℂ (Fin 2 → W) :=
  matrixAction (operatorSoldering v)

/-! ## The represented `Cl(1,1)` packet on the doubled carrier -/

abbrev CarrierEnd (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  Module.End ℂ (Fin 2 → W)

/-- The sheet grading acting on the doubled carrier. -/
def carrierGamma : CarrierEnd W :=
  matrixAction (sheetGamma (B := EndW W))

/-- The sheet exchange acting on the doubled carrier. -/
def carrierJ : CarrierEnd W :=
  matrixAction (sheetJ (B := EndW W))

/-- The product `ΓJ`, which is the real phase-axis square-minus-one element. -/
def carrierGammaJ : CarrierEnd W :=
  matrixAction (sheetGammaJ (B := EndW W))

theorem carrierGammaJ_eq :
    carrierGammaJ (W := W) =
      carrierGamma (W := W) * carrierJ (W := W) := by
  calc
    carrierGammaJ (W := W) =
        matrixAction (sheetGammaJ (B := EndW W)) := rfl
    _ = matrixAction
        (sheetGamma (B := EndW W) * sheetJ (B := EndW W)) := by
      rw [sheetGammaJ_eq]
    _ = carrierGamma (W := W) * carrierJ (W := W) := by
      exact matrixAction_mul_end _ _

private theorem matrixAction_one_end :
    matrixAction (1 : OperatorMatrix (R := ℂ) (W := W)) =
      (1 : CarrierEnd W) := by
  apply LinearMap.ext
  intro ψ
  exact matrixAction_one ψ

@[simp] theorem carrierGamma_sq :
    carrierGamma (W := W) * carrierGamma (W := W) = 1 := by
  change matrixAction (sheetGamma (B := EndW W)) *
      matrixAction (sheetGamma (B := EndW W)) = 1
  calc
    carrierGamma (W := W) * carrierGamma (W := W) =
        matrixAction
          (sheetGamma (B := EndW W) * sheetGamma (B := EndW W)) := by
      exact (matrixAction_mul_end _ _).symm
    _ = matrixAction (1 : OperatorMatrix (R := ℂ) (W := W)) := by
      rw [sheetGamma_sq, sheetIdentity_eq_one]
    _ = 1 := matrixAction_one_end (W := W)

@[simp] theorem carrierJ_sq :
    carrierJ (W := W) * carrierJ (W := W) = 1 := by
  change matrixAction (sheetJ (B := EndW W)) *
      matrixAction (sheetJ (B := EndW W)) = 1
  calc
    carrierJ (W := W) * carrierJ (W := W) =
        matrixAction
          (sheetJ (B := EndW W) * sheetJ (B := EndW W)) := by
      exact (matrixAction_mul_end _ _).symm
    _ = matrixAction (1 : OperatorMatrix (R := ℂ) (W := W)) := by
      rw [sheetJ_sq, sheetIdentity_eq_one]
    _ = 1 := matrixAction_one_end (W := W)

theorem carrierJ_mul_carrierGamma :
    carrierJ (W := W) * carrierGamma (W := W) =
      -(carrierGamma (W := W) * carrierJ (W := W)) := by
  change matrixAction (sheetJ (B := EndW W)) *
      matrixAction (sheetGamma (B := EndW W)) =
        -(matrixAction (sheetGamma (B := EndW W)) *
          matrixAction (sheetJ (B := EndW W)))
  calc
    carrierJ (W := W) * carrierGamma (W := W) =
        matrixAction
          (sheetJ (B := EndW W) * sheetGamma (B := EndW W)) := by
      exact (matrixAction_mul_end _ _).symm
    _ = matrixAction
          (-(sheetGamma (B := EndW W) * sheetJ (B := EndW W))) := by
      rw [sheetJ_mul_sheetGamma]
    _ = -(matrixAction
          (sheetGamma (B := EndW W) * sheetJ (B := EndW W))) := by
      exact matrixAction_neg _
    _ = -(carrierGamma (W := W) * carrierJ (W := W)) := by
      congr 1
      exact matrixAction_mul_end _ _

theorem carrierGamma_mul_carrierJ :
    carrierGamma (W := W) * carrierJ (W := W) =
      -(carrierJ (W := W) * carrierGamma (W := W)) := by
  rw [carrierJ_mul_carrierGamma]
  simp only [neg_neg]

@[simp] theorem carrierGammaJ_sq :
    carrierGammaJ (W := W) * carrierGammaJ (W := W) = -1 := by
  change matrixAction (sheetGammaJ (B := EndW W)) *
      matrixAction (sheetGammaJ (B := EndW W)) = -1
  calc
    carrierGammaJ (W := W) * carrierGammaJ (W := W) =
        matrixAction
          (sheetGammaJ (B := EndW W) * sheetGammaJ (B := EndW W)) := by
      exact (matrixAction_mul_end _ _).symm
    _ = matrixAction (-1 : OperatorMatrix (R := ℂ) (W := W)) := by
      rw [sheetGammaJ_sq, sheetIdentity_eq_one]
    _ = -matrixAction (1 : OperatorMatrix (R := ℂ) (W := W)) := by
      exact matrixAction_neg _
    _ = -1 := by rw [matrixAction_one_end]

@[simp] theorem operatorSoldering_apply
    (v : OperatorFourVector W) :
    operatorSoldering v =
      !![v 0 + v 3, v 1 - Complex.I • v 2;
         v 1 + Complex.I • v 2, v 0 - v 3] :=
  rfl

@[simp] theorem operatorSolderingAction_apply
    (v : OperatorFourVector W) (ψ : Fin 2 → W) (i : Fin 2) :
    operatorSolderingAction v ψ i =
      ∑ j : Fin 2, operatorSoldering v i j (ψ j) :=
  matrixAction_apply (operatorSoldering v) ψ i

theorem operatorSolderingAction_injective :
    Function.Injective (operatorSolderingAction (W := W)) := by
  intro v w h
  have hm : operatorSoldering v = operatorSoldering w :=
    matrixAction_injective h
  have hc : causalCoordinatesOfFourVector v =
      causalCoordinatesOfFourVector w := by
    exact (causalOperatorCoordinatesRingEquiv (B := EndW W)).injective hm
  funext i
  fin_cases i
  · simpa [causalCoordinatesOfFourVector] using
      congrArg CausalOperatorCoordinates.scalar hc
  · simpa [causalCoordinatesOfFourVector] using
      congrArg CausalOperatorCoordinates.exchange hc
  · simpa [causalCoordinatesOfFourVector] using
      congrArg CausalOperatorCoordinates.circular hc
  · simpa [causalCoordinatesOfFourVector] using
      congrArg CausalOperatorCoordinates.chiral hc

@[simp] theorem operatorSoldering_zero :
    operatorSoldering (W := W) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorSoldering, causalCoordinatesOfFourVector, reconstruct_causal]
@[simp] theorem operatorSolderingAction_zero :
    operatorSolderingAction (W := W) 0 = 0 := by
  change matrixAction (operatorSoldering (W := W) 0) = 0
  rw [operatorSoldering_zero]
  apply LinearMap.ext
  intro ψ
  exact matrixAction_zero (R := ℂ) (W := W) ψ

theorem operatorSoldering_eq_zero_iff (v : OperatorFourVector W) :
    operatorSoldering v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply operatorSolderingAction_injective (W := W)
    change matrixAction (operatorSoldering v) =
      matrixAction (operatorSoldering (W := W) 0)
    rw [h, operatorSoldering_zero]
  · intro h
    rw [h, operatorSoldering_zero]

theorem operatorSolderingAction_eq_zero_iff (v : OperatorFourVector W) :
    operatorSolderingAction v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply operatorSolderingAction_injective (W := W)
    exact h.trans (operatorSolderingAction_zero (W := W)).symm
  · intro h
    rw [h, operatorSolderingAction_zero]

/-- Multiplication of causal operator coordinates is composition on the doubled carrier. -/
theorem causal_mul_action
    (A C : CausalOperatorCoordinates (EndW W)) :
    matrixAction (reconstruct_causal (A * C)) =
      matrixAction (reconstruct_causal A) *
        matrixAction (reconstruct_causal C) := by
  rw [reconstruct_causal_mul, matrixAction_mul_end]

/-- The causal operator coordinates transport the noncommutative commutator
to the doubled carrier. -/
theorem causal_commutator_action
    (A C : CausalOperatorCoordinates (EndW W)) :
    matrixAction (reconstruct_causal (A * C - C * A)) =
      matrixAction (reconstruct_causal A) * matrixAction (reconstruct_causal C) -
        matrixAction (reconstruct_causal C) * matrixAction (reconstruct_causal A) := by
  rw [reconstruct_causal_sub, reconstruct_causal_mul, reconstruct_causal_mul,
    matrixAction_commutator]

/-- The causal operator coordinates transport the CAR anticommutator to the
doubled carrier without commuting the internal operator coefficients. -/
theorem causal_anticommutator_action
    (A C : CausalOperatorCoordinates (EndW W)) :
    matrixAction (reconstruct_causal (A * C + C * A)) =
      matrixAction (reconstruct_causal A) * matrixAction (reconstruct_causal C) +
        matrixAction (reconstruct_causal C) * matrixAction (reconstruct_causal A) := by
  rw [reconstruct_causal_add, reconstruct_causal_mul, reconstruct_causal_mul,
    matrixAction_anticommutator]

section Connection

variable {Point Tangent : Type*}

/-- A causal connection whose four coefficients are endomorphisms of `W`. -/
abbrev CausalOperatorConnection
    (W Point Tangent : Type*) [AddCommGroup W] [Module ℂ W] :=
  Connection
    (Point := Point) (Tangent := Tangent)
    (Value := CausalOperatorCoordinates (EndW W))

/-- Reconstruct every coefficient and exterior derivative as an operator matrix. -/
def matrixConnection (C : CausalOperatorConnection W Point Tangent) :
    Connection
      (Point := Point) (Tangent := Tangent)
      (Value := OperatorMatrix (R := ℂ) (W := W)) where
  form p X := reconstruct_causal (C.form p X)
  derivative p X Y := reconstruct_causal (C.derivative p X Y)
  derivative_swap p X Y := by
    rw [C.derivative_swap, reconstruct_causal_neg]
  derivative_same p X := by
    rw [C.derivative_same, reconstruct_causal_zero]

/-- Matrix reconstruction preserves the full curvature `dΩ + Ω ∧ Ω`. -/
theorem matrixConnection_curvature
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    curvature (matrixConnection C) p X Y =
      reconstruct_causal (curvature C p X Y) := by
  simp [curvature, wedgeSquare, matrixConnection]

/-- Curvature acts faithfully on the doubled internal carrier. -/
theorem matrixAction_curvature
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    matrixAction (curvature (matrixConnection C) p X Y) =
      matrixAction (reconstruct_causal (curvature C p X Y)) := by
  rw [matrixConnection_curvature]

/-- The doubled carrier sees the curvature as derivative plus a commutator of
the two transported connection operators. -/
theorem matrixAction_curvature_explicit
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    matrixAction (curvature (matrixConnection C) p X Y) =
      matrixAction (reconstruct_causal (C.derivative p X Y)) +
        (matrixAction (reconstruct_causal (C.form p X)) *
            matrixAction (reconstruct_causal (C.form p Y)) -
          matrixAction (reconstruct_causal (C.form p Y)) *
            matrixAction (reconstruct_causal (C.form p X))) := by
  rw [matrixConnection_curvature]
  unfold curvature wedgeSquare
  rw [reconstruct_causal_add, reconstruct_causal_sub,
    reconstruct_causal_mul, reconstruct_causal_mul,
    matrixAction_add, matrixAction_sub, matrixAction_mul_end,
    matrixAction_mul_end]

/-- Vanishing after doubled-carrier action is equivalent to vanishing causal curvature. -/
theorem matrixAction_curvature_eq_zero_iff
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    matrixAction (curvature (matrixConnection C) p X Y) = 0 ↔
      curvature C p X Y = 0 := by
  rw [matrixConnection_curvature]
  constructor
  · intro h
    have hz :
        matrixAction (0 : OperatorMatrix (R := ℂ) (W := W)) = 0 := by
      apply LinearMap.ext
      intro ψ
      exact matrixAction_zero ψ
    have h' :
        matrixAction (reconstruct_causal (curvature C p X Y)) =
          matrixAction (0 : OperatorMatrix (R := ℂ) (W := W)) := by
      rw [hz]
      exact h
    have hm : reconstruct_causal (curvature C p X Y) = 0 :=
      matrixAction_injective h'
    apply (causalOperatorCoordinatesRingEquiv (B := EndW W)).injective
    change reconstruct_causal (curvature C p X Y) = reconstruct_causal 0
    rw [hm, reconstruct_causal_zero]
  · intro h
    rw [h, reconstruct_causal_zero]
    apply LinearMap.ext
    intro ψ
    exact matrixAction_zero ψ

end Connection

end InfoGeometry.Optics.OperatorCausalSoldering
