/-
InfoGeometry/Canonical/DrazinDilationGap.lean

Drazin Dilation Gap:
  Drazin support      P_D = A Aᴰ
  Drazin defect       Q₀  = 1 - P_D
  MP range support    P_R = A A†
  MP domain support   P_I = A† A
  Dilation gap        G   = 1/2 (P_R - P_I)
  Drazin supercharge  Q   = 2 [P_D, G]    -- algebraic odd generator
                    or 2 i [P_D, G]       -- Hilbert self-adjoint version
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics

noncomputable section

namespace DrazinDilationGap

/--
Drazin data for an operator A.
-/
structure DrazinData
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  A : Op
  AD : Op
  P_D : Op
  Q₀ : Op

  P_D_def :
    P_D = A * AD

  commute :
    A * AD = AD * A

  P_D_idempotent :
    P_D * P_D = P_D

  P_D_self_adjoint :
    star P_D = P_D

  Q₀_def :
    Q₀ = 1 - P_D

/--
Moore--Penrose support data.
-/
structure MoorePenroseSupportData
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  A : Op
  A_MP : Op

  P_range : Op
  P_domain : Op

  P_range_def :
    P_range = A * A_MP

  P_domain_def :
    P_domain = A_MP * A

  P_range_idempotent :
    P_range * P_range = P_range

  P_domain_idempotent :
    P_domain * P_domain = P_domain

  P_range_self_adjoint :
    star P_range = P_range

  P_domain_self_adjoint :
    star P_domain = P_domain

/--
Dilation gap:

  G = c • (P_range - P_domain)

Usually c = 1/2.  We keep `halfScalar` as a field because
abstract rings may not have a literal inverse of 2.
-/
structure DilationGapData
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where

  mp :
    MoorePenroseSupportData Op

  halfScalar :
    ℝ

  G :
    Op

  G_def :
    G = halfScalar • (mp.P_range - mp.P_domain)

def commutator
    {Op : Type*}
    [Mul Op] [Sub Op]
    (X Y : Op) : Op :=
  X * Y - Y * X

/--
Algebraic Drazin supercharge:

  Q_alg = 2 [P_D, G].
-/
structure DrazinSuperchargeData
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where

  drazin :
    DrazinData Op

  gap :
    DilationGapData Op

  Q_alg :
    Op

  Q_alg_def :
    Q_alg = (2 : ℝ) • commutator drazin.P_D gap.G

/--
Kinetic/defect split of the squared Drazin supercharge.

The theorem-safe repo closure is the odd-odd bracket:
  {Q, Q} = 2 T_D + Z_D
  Q^2 = T_D + 1/2 Z_D
-/
structure DrazinKineticDefectSplit
    (Op : Type*)
    [Ring Op]
    [Star Op]
    [SMul ℝ Op] where

  supercharge :
    DrazinSuperchargeData Op

  T_D :
    Op

  Z_D :
    Op

  square_split :
    supercharge.Q_alg * supercharge.Q_alg = T_D + (0.5 : ℝ) • Z_D

  T_D_regular :
    supercharge.drazin.P_D * T_D * supercharge.drazin.P_D = T_D

  Z_D_supported :
    supercharge.drazin.Q₀ * Z_D * supercharge.drazin.Q₀ = Z_D

/--
Modular persistence of the Drazin support.

The regular support P_D is the modularly invariant kinetic lane.
-/
structure ModularPersistenceData
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  drazin :
    DrazinData Op

  flow :
    InfoGeometry.OperatorAlgebra.OperatorThermodynamics.OperatorFlow Op

  /--
  The regular support P_D is modularly invariant.
  -/
  regular_invariant :
    ∀ t : ℝ, flow.flow t drazin.P_D = drazin.P_D

/--
Abstract modular-flow packet for a regular support.

This records the theorem-safe nuance: if a unital, subtraction-preserving flow
fixes the regular support, then it also fixes the complementary noise support.
The complement can be invariant as a projector while still being excluded from
the regular kinetic readout.
-/
structure ModularRegularSupport
    (Op : Type*)
    [Ring Op] where

  modularFlow :
    ℝ → Op → Op

  regularSupport :
    Op

  flow_one :
    ∀ t : ℝ, modularFlow t 1 = 1

  flow_sub :
    ∀ (t : ℝ) (X Y : Op),
      modularFlow t (X - Y) = modularFlow t X - modularFlow t Y

  regular_invariant :
    ∀ t : ℝ, modularFlow t regularSupport = regularSupport

namespace ModularRegularSupport

variable {Op : Type*} [Ring Op] (M : ModularRegularSupport Op)

/-- The complementary noise/defect support associated to the regular support. -/
def noiseSupport : Op :=
  1 - M.regularSupport

/--
If the modular flow is unital/sub-preserving and fixes the regular support, it
also fixes the complementary noise support.
-/
theorem noiseSupport_invariant :
    ∀ t : ℝ, M.modularFlow t M.noiseSupport = M.noiseSupport := by
  intro t
  calc
    M.modularFlow t M.noiseSupport
        = M.modularFlow t (1 - M.regularSupport) := rfl
    _ = M.modularFlow t 1 - M.modularFlow t M.regularSupport := by
          rw [M.flow_sub]
    _ = 1 - M.regularSupport := by
          rw [M.flow_one, M.regular_invariant]
    _ = M.noiseSupport := rfl

end ModularRegularSupport

/--
Drazin–Hodge envelope of an observable x.

This represents the physical observable after projection onto the Drazin support
and the singular defect/harmonic-zero block.
-/
structure DrazinHodgeEnvelope
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  drazin :
    DrazinData Op

  /-- Harmonic/Hodge Drazin data for the background flow L. -/
  hodge :
    DrazinData Op

  x :
    Op

  /-- The physical envelope: x_phys = (1 - LLᴰ)(AAᴰ) x (AAᴰ)(1 - LLᴰ). -/
  x_phys :
    Op

  x_phys_def :
    x_phys = hodge.Q₀ * drazin.P_D * x * drazin.P_D * hodge.Q₀

/--
Fierz–Klein invariants of the Drazin–Hodge envelope.
-/
structure FierzKleinInvariants
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  envelope :
    DrazinHodgeEnvelope Op

  /-- The state used to measure the invariants. -/
  phi :
    InfoGeometry.OperatorAlgebra.OperatorThermodynamics.AlgebraicState Op

  /-- The Fierz channel coefficients C_alpha. -/
  channels :
    ℕ → Op → Op

  /-- The measured coordinates F_alpha. -/
  coords :
    ℕ → ℂ

  coords_def :
    ∀ n : ℕ, coords n = phi.eval (channels n envelope.x_phys)

/--
If the Moore--Penrose range and domain supports agree, the dilation gap
vanishes.
-/
theorem dilation_gap_zero_of_supports_equal
    {Op : Type*}
    [Ring Op]
    [Star Op]
    [SMul ℝ Op]
    (G : DilationGapData Op)
    (h : G.mp.P_range = G.mp.P_domain)
    (hzero : G.halfScalar • (0 : Op) = 0) :
    G.G = 0 := by
  rw [G.G_def, h]
  simp only [sub_self]
  exact hzero

/--
If two self-adjoint operators generate a commutator, that commutator is
skew-adjoint.
-/
theorem star_commutator_eq_neg_of_self_adjoint
    {Op : Type*} [Ring Op] [StarRing Op] {P G : Op}
    (hP : star P = P) (hG : star G = G) :
    star (commutator P G) = -commutator P G := by
  simp [commutator, hP, hG]

end DrazinDilationGap
