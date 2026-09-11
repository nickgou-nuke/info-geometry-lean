import InfoGeometry.Krein.HestenesAffineO55ClosureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.TKKConformalClosure

open scoped InnerProductSpace BigOperators

noncomputable section

namespace InfoGeometry.Canonical.O55TKKAnomalyAnnihilation

open InfoGeometry.OperatorAlgebra.TKKConformalClosure

/-!
# Finite `O(5,5)` / TKK anomaly-annihilation ledger

This file records the kernel-checked finite theorem surface mirrored by
`tools/sympy/o55_tkk_anomaly_annihilation.py`.

Honest scope:

* same-arrow TKK bracket anomalies vanish in the supplied short grading;
* mixed TKK brackets land in grade zero;
* an anomaly residual built from an invariant finite `O(5,5)` readout is zero;
* the existing Hestenes affine `O(5,5)` bridge supplies concrete Ω-volume and
  D4/Hurwitz-root residual-zero readbacks.

No continuum anomaly-cancellation theorem, global index theorem, or full
`Pin(5,5)` double-cover construction is asserted here.
-/

/-! ## Abstract finite `O(5,5)` residual ledger -/

/--
A finite anomaly ledger whose transformed readout is invariant under the
supplied `O(5,5)` action.

`residual_eq_transformed_sub_anomaly` makes the residual an equation-level law,
not a certificate/prose socket.  The annihilation theorem below is just the
algebraic consequence of this law and `o55_invariant`.
-/
@[rep_depth transport]
structure FiniteO55AnomalyLedger (State Anomaly : Type*) [AddGroup Anomaly] where
  /-- Finite representative of the `O(5,5)` action on the state carrier. -/
  o55Action : State ≃ State
  /-- Original anomaly readout. -/
  anomaly : State → Anomaly
  /-- Transformed anomaly readout after the supplied `O(5,5)` action. -/
  transformed : State → Anomaly
  /-- Difference between transformed and original anomaly readouts. -/
  residual : State → Anomaly
  /-- Residual is exactly transformed minus original. -/
  residual_eq_transformed_sub_anomaly :
    ∀ s : State, residual s = transformed s - anomaly s
  /-- `O(5,5)` invariance of the finite readout. -/
  o55_invariant :
    ∀ s : State, transformed s = anomaly s

namespace FiniteO55AnomalyLedger

variable {State Anomaly : Type*} [AddGroup Anomaly]
variable (L : FiniteO55AnomalyLedger State Anomaly)

/-- Any residual defined from an `O(5,5)`-invariant finite readout vanishes. -/
@[rep_depth transport]
theorem residual_eq_zero (s : State) :
    L.residual s = 0 := by
  rw [L.residual_eq_transformed_sub_anomaly s, L.o55_invariant s]
  simp

end FiniteO55AnomalyLedger

/-! ## TKK finite same-arrow anomaly annihilation -/

namespace TKKFinite



variable {L : Type*}
variable [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (G : TKKThreeGrading L)

/-- Same-arrow anomaly in the negative TKK grade vanishes. -/
@[rep_depth transport]
theorem minus_same_arrow_anomaly_eq_zero
    {X Y : L}
    (hX : X ∈ G.gMinus)
    (hY : Y ∈ G.gMinus) :
    ⁅X, Y⁆ = 0 :=
  G.minus_minus_eq_zero hX hY

/-- Same-arrow anomaly in the positive TKK grade vanishes. -/
@[rep_depth transport]
theorem plus_same_arrow_anomaly_eq_zero
    {X Y : L}
    (hX : X ∈ G.gPlus)
    (hY : Y ∈ G.gPlus) :
    ⁅X, Y⁆ = 0 :=
  G.plus_plus_eq_zero hX hY

/-- Mixed outer TKK anomaly is absorbed into the structure/zero grade. -/
@[rep_depth transport]
theorem mixed_outer_anomaly_mem_zero
    {X Y : L}
    (hX : X ∈ G.gMinus)
    (hY : Y ∈ G.gPlus) :
    ⁅X, Y⁆ ∈ G.gZero :=
  G.minus_plus_mem_zero hX hY

end TKKFinite

/-! ## Owner-backed Hestenes affine `O(5,5)` residual-zero readbacks -/

namespace HestenesFinite

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesAffineO55ClosureBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

variable (B : _root_.InfoGeometry.Krein.HestenesAffineO55ClosureBridge.Bridge (E := E))

/-- Ω-volume anomaly residual vanishes under the supplied `O(5,5)` operator action. -/
@[rep_depth operator]
theorem volume_o55_residual_eq_zero (A : EndH) :
    B.duality.arithmetic.moebius.wilson.volume.volumeState (B.o55OperatorAction A) -
        B.duality.arithmetic.moebius.wilson.volume.volumeState A = 0 := by
  rw [B.volumeState_o55_invariant A]
  simp

/-- D4/Hurwitz root Ω-weight residual vanishes under the supplied `O(5,5)` root action. -/
@[rep_depth operator]
theorem hurwitzRoot_o55_residual_eq_zero (i : Fin 24) :
    B.duality.arithmetic.moebius.wilson.volume.volumeState
          (B.duality.arithmetic.hurwitzRoot (B.o55RootAction i)) -
        B.duality.arithmetic.moebius.wilson.volume.volumeState
          (B.duality.arithmetic.hurwitzRoot i) = 0 := by
  rw [B.hurwitzRoot_expectation_o55_invariant i]
  simp

/-- Positive affine same-arrow anomaly is nilpotently annihilated in the owner bridge. -/
@[rep_depth operator]
theorem affine_plus_same_arrow_anomaly_eq_zero (A C : EndH) :
    B.duality.arithmetic.affineNullRootPlus A *
        B.duality.arithmetic.affineNullRootPlus C = 0 :=
  B.affineNullRootPlus_same_arrow_nilpotent A C

/-- Negative affine same-arrow anomaly is nilpotently annihilated in the owner bridge. -/
@[rep_depth operator]
theorem affine_minus_same_arrow_anomaly_eq_zero (A C : EndH) :
    B.duality.arithmetic.affineNullRootMinus A *
        B.duality.arithmetic.affineNullRootMinus C = 0 :=
  B.affineNullRootMinus_same_arrow_nilpotent A C

end Core

end HestenesFinite

end InfoGeometry.Canonical.O55TKKAnomalyAnnihilation

end
