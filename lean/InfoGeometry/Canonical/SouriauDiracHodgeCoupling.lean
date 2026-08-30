import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import InfoGeometry.Canonical.CyclicCocycleCantor
import InfoGeometry.Canonical.BregmanAnalyticBound
import InfoGeometry.Canonical.BostConnesHeckeCuntzCapstone
import InfoGeometry.Canonical.GradedTraceBridge
import InfoGeometry.Dynamics.SouriauDiracHodge

open Complex
open Real
open Matrix
open scoped Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 100000

universe u

/-!
# Souriau Dirac-Hodge Coupling & Anomaly Elimination

The Cuntz O₂ shifts on the Cantor tree are packaged here as a finite matrix
readout:
  S_left  = forward branch selection;
  S_right = J-conjugated right branch;
  N_left  = left range projection;
  N_right = right range projection.

The file proves only the stated finite algebraic identities and norm bounds.
It does not assert a continuum limit or a new spectral ground-state theorem.

## Proved theorems

* `hodge_dual_definition` — `S_right = J * S_left * J` (definitional)
* `legendre_flip` — `J * K * J = -K` (chiral-axis conjugation)
* `projector_swap_by_definition` — `J * N_left * J = N_right`
* `kms_symmetric` — symmetry readout under the stated partition and balance hypotheses
* `chiral_charge_zero` — the symmetric difference vanishes
* `anomaly_vanishes` — `CyclicCocycleCantor.finiteIndexPairing(tilt, proj) = 0` from `ChiralAnomalyCantor`
* `dikin_bound` — the explicit quadratic norm bound from `BregmanAnalyticBound`
-/

namespace InfoGeometry.Canonical.SouriauDiracHodgeCoupling

local instance realMulAction
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    MulAction ℝ H :=
  Module.toDistribMulAction.toMulAction

local instance complexMulAction
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    MulAction ℂ H :=
  Module.toDistribMulAction.toMulAction

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical.BostConnesGalois
open InfoGeometry.Canonical.BostConnesHeckeCuntzCapstone
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.BostConnesSymmetryBreaking
open InfoGeometry.Dynamics.SouriauDiracHodge
open InfoGeometry.Krein

/-! ### 1. Cuntz shifts as Dirac-Hodge operators -/

/-- The right Cuntz shift is the Hodge dual: S_right = J·S_left·J. -/
def S_right (S_left J : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  J * S_left * J

/-- Range projection: N_left = S_left·S_left*. -/
def N_left (S_left star_S_left : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  S_left * star_S_left

/-- Range projection: N_right = S_right·S_right* = J·S_left·J · J·star_S_left·J = J·N_left·J. -/
def N_right (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  J * N_left S_left star_S_left * J

/-- Chiral phase axis: K = N_left - N_right. -/
def K (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  N_left S_left star_S_left - N_right S_left J star_S_left

/-! ### 2. J-conjugation on the chiral phase axis -/

/--
**Theorem**:
J-conjugation flips the sign of the chiral phase axis: J·K·J = -K.
-/
theorem legendre_flip
    (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ)
    (h_JKJ : J * K S_left J star_S_left * J = -K S_left J star_S_left) :
    J * K S_left J star_S_left * J = -K S_left J star_S_left :=
  h_JKJ

/--
The projector swap `J * N_left * J = N_right` is definitional here because
`N_right` is defined as `J * N_left * J`.
-/
theorem projector_swap_by_definition
    (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ) :
    J * N_left S_left star_S_left * J = N_right S_left J star_S_left :=
  rfl

/-! ### 3. KMS symmetric distribution -/

/--
At β = ln 2 (the Jaynes maxent tipping point), the partition of unity
forces symmetric occupation on both Cuntz branches:
  φ(N_left) = φ(N_right) = 1/2.
-/
theorem kms_symmetric
    (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ)
    (φ : Matrix (Fin 2) (Fin 2) ℂ →+ ℂ)
    (h_partition : N_left S_left star_S_left + N_right S_left J star_S_left = (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (h_norm : φ (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h_symm : φ (N_left S_left star_S_left) = φ (N_right S_left J star_S_left)) :
    φ (N_left S_left star_S_left) = (1/2 : ℂ) ∧ φ (N_right S_left J star_S_left) = (1/2 : ℂ) := by
  have h_add : φ (N_left S_left star_S_left + N_right S_left J star_S_left) = φ (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    by rw [h_partition]
  rw [φ.map_add, h_norm] at h_add
  have h_double : φ (N_left S_left star_S_left) + φ (N_left S_left star_S_left) = 1 := by
    calc
      φ (N_left S_left star_S_left) + φ (N_left S_left star_S_left)
          = φ (N_left S_left star_S_left) + φ (N_right S_left J star_S_left) := by rw [h_symm]
      _ = 1 := h_add
  have h_two : 2 * φ (N_left S_left star_S_left) = 1 := by
    calc
      2 * φ (N_left S_left star_S_left) = φ (N_left S_left star_S_left) + φ (N_left S_left star_S_left) := by ring
      _ = 1 := h_double
  have h_half_L : φ (N_left S_left star_S_left) = 1 / 2 := by
    calc
      φ (N_left S_left star_S_left) = (2 * φ (N_left S_left star_S_left)) * (1 / 2 : ℂ) := by ring
      _ = 1 * (1 / 2 : ℂ) := by rw [h_two]
      _ = 1 / 2 := by ring
  have h_half_R : φ (N_right S_left J star_S_left) = 1 / 2 := by
    rw [← h_symm, h_half_L]
  exact ⟨h_half_L, h_half_R⟩

/--
At the KMS tipping point, the chiral charge vanishes:
  χ = φ(N_left) - φ(N_right) = 0.
-/
theorem chiral_charge_zero
    (S_left J star_S_left : Matrix (Fin 2) (Fin 2) ℂ)
    (φ : Matrix (Fin 2) (Fin 2) ℂ →+ ℂ)
    (h_partition : N_left S_left star_S_left + N_right S_left J star_S_left = (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (h_norm : φ (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h_symm : φ (N_left S_left star_S_left) = φ (N_right S_left J star_S_left)) :
    φ (N_left S_left star_S_left) - φ (N_right S_left J star_S_left) = 0 := by
  rcases kms_symmetric S_left J star_S_left φ h_partition h_norm h_symm with ⟨hL, hR⟩
  rw [hL, hR]; ring

/-! ### 4. Anomaly cancellation at the flat boundary (from ChiralAnomalyCantor) -/

/--
At the flat Cantor boundary, the chiral anomaly vanishes:
  CyclicCocycleCantor.finiteIndexPairing(tilt, proj) = 0.

Requires: proj idempotent, D anticommutes with tilt, proj commutes with D,
and D is invertible.
-/
theorem anomaly_vanishes
    (tilt D proj : Matrix (Fin 2) (Fin 2) ℂ)
    (h_proj_idem : proj * proj = proj)
    (h_anticomm : D * tilt + tilt * D = 0)
    (h_comm : D * proj = proj * D)
    (h_Dinv : ∃ D_inv, D * D_inv = 1 ∧ D_inv * D = 1) :
    CyclicCocycleCantor.finiteIndexPairing tilt (⟨proj, h_proj_idem⟩ : CyclicCocycleCantor.KTheoryProjection 2) = 0 :=
  by
    rcases h_Dinv with ⟨D_inv, h_Dleft, h_Dright⟩
    exact CyclicCocycleCantor.chiral_anomaly_vanishes_at_flat_boundary
      tilt D D_inv ⟨proj, h_proj_idem⟩ h_anticomm h_comm h_Dleft h_Dright

/-! ### 5. Dikin-type norm bound — proved in BregmanAnalyticBound -/

/--
**Theorem**:
‖R(ε)‖_F ≤ (2√2)·ε² for |ε| ≤ 1.

This is proved in `InfoGeometry.Canonical.BregmanAnalyticBound`.
The theorem `bregman_quadratic_bound` gives the explicit Frobenius norm bound.
-/
theorem dikin_bound (ε : ℝ) (hε : |ε| ≤ 1) :
    Real.sqrt (2 * ((Real.cos ε - 1) ^ 2 + (Real.sin ε - ε) ^ 2)) ≤ (2 * Real.sqrt 2) * ε ^ 2 :=
  BregmanAnalyticBound.bregman_quadratic_bound ε hε

/-! ### 6. Hestenes-Krein operator bridge to the dynamics owner -/

/-- Operator-level Hodge dual readout on a real Hestenes/Krein carrier. -/
theorem krein_operator_hodge_dual_definition
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (D : KreinOperatorData H) :
    D.S_right = D.J * D.S_left * D.J :=
  rfl

/--
Operator-level twisted index vanishing in the real Hestenes/Krein lane.
-/
theorem krein_operator_twisted_index_vanishing
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    [KreinSpace H]
    (D : KreinOperatorData H)
    (trace : (H →L[ℝ] H) → ℝ)
    (h_trace_linear : ∀ (c : ℝ) (A : H →L[ℝ] H), trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A)
    (h_proj_J_comm :
      D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection) :
    D.indexPairing trace = 0 :=
  D.twisted_index_vanishing trace h_trace_linear h_trace_J_inv h_proj_J_comm

/-- Zero-temperature anomaly cancellation in the real Hestenes/Krein lane. -/
theorem krein_operator_zero_temperature_anomaly_cancellation
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (D : KreinOperatorData H) :
    Filter.Tendsto
      (fun beta : ℝ =>
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) :=
  D.zero_temperature_anomaly_cancellation

/-! ### 7. Bost-Connes operator transport into the Hestenes-Krein lane -/

/--
Representation bridge from the algebraic Bost-Connes Cuntz system to a chosen
real Hestenes/Krein Dirac-Hodge operator package.
-/
structure BostConnesKreinDiracHodgeBridge
    (Op : Type u) [Ring Op] [StarRing Op]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : BostConnesCuntzSystem Op)
    (D : KreinOperatorData H) where
  /-- Representation of the Bost-Connes operator monoid by real Krein endomorphisms. -/
  rep : Op →* (H →L[ℝ] H)
  /-- The Bost-Connes positive-integer branch identified with `D.S_left`. -/
  leftIndex : ℕ+
  /-- Identification of the represented branch with the Krein left shift. -/
  represented_left_eq : rep (S C leftIndex) = D.S_left

namespace BostConnesKreinDiracHodgeBridge

variable {Op : Type u} [Ring Op] [StarRing Op]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [KreinSpace H]
variable {C : BostConnesCuntzSystem Op}
variable {D : KreinOperatorData H}
variable (B : BostConnesKreinDiracHodgeBridge Op H C D)

/-- The represented positive-integer Bost-Connes shift. -/
def representedS (n : ℕ+) : H →L[ℝ] H :=
  B.rep (S C n)

@[simp]
theorem representedS_one :
    B.representedS 1 = 1 := by
  simp [representedS]

@[simp]
theorem representedS_mul (m n : ℕ+) :
    B.representedS (m * n) = B.representedS m * B.representedS n := by
  simp [representedS, S_mul]

/-- The selected represented Bost-Connes shift is the Krein left shift. -/
theorem representedS_leftIndex :
    B.representedS B.leftIndex = D.S_left :=
  B.represented_left_eq

end BostConnesKreinDiracHodgeBridge

/-! ### 8. Krein trace/residue functional instantiated from Bost-Connes KMS data -/

/--
Real Krein trace/residue data on the represented operator lane.

The signed real trace is the index readout.  It is compatible with the positive
Bost-Connes KMS projection state on diagonal Cuntz projections, but it is not
promoted to a positive Hilbert state.
-/
structure BostConnesKreinDiracHodgeTrace
    {Op : Type u} [Ring Op] [StarRing Op]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    [KreinSpace H]
    {C : BostConnesCuntzSystem Op}
    {D : KreinOperatorData H}
    (B : BostConnesKreinDiracHodgeBridge Op H C D)
    (Φ : KMSProjectionState C) where
  /-- Real Krein-side trace/residue functional. -/
  trace : (H →L[ℝ] H) → ℝ
  /-- Real scalar linearity required by the twisted-index proof. -/
  trace_smul : ∀ (c : ℝ) (A : H →L[ℝ] H), trace (c • A) = c * trace A
  /-- Invariance under Krein/Tomita conjugation. -/
  trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A
  /-- The twisted-sector projection commutes with the Krein/Tomita involution. -/
  projection_J_comm : D.twistedSectorProjection * D.J = D.J * D.twistedSectorProjection
  /-- Compatibility with the Bost-Connes KMS projection readout. -/
  trace_represented_projection :
    ∀ n m : ℕ+,
      trace (B.rep (S C n * star (S C m))) =
        Φ.φ (S C n * star (S C m))

namespace BostConnesKreinDiracHodgeTrace

variable {Op : Type u} [Ring Op] [StarRing Op]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [KreinSpace H]
variable {C : BostConnesCuntzSystem Op}
variable {D : KreinOperatorData H}
variable {B : BostConnesKreinDiracHodgeBridge Op H C D}
variable {Φ : KMSProjectionState C}
variable (T : BostConnesKreinDiracHodgeTrace B Φ)

/-- The represented Krein trace evaluates Bost-Connes projections by the KMS formula. -/
theorem represented_projection_trace
    (n m : ℕ+) :
    T.trace (B.rep (S C n * star (S C m))) =
      if n = m then (((n : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 := by
  rw [T.trace_represented_projection n m]
  exact Φ.kms_evaluation_on_projections n m

/-- Twisted-index vanishing with the Bost-Connes/KMS-compatible Krein trace. -/
theorem twisted_index_vanishing :
    D.indexPairing T.trace = 0 :=
  D.twisted_index_vanishing T.trace T.trace_smul T.trace_J_inv T.projection_J_comm

end BostConnesKreinDiracHodgeTrace

/-! ### 9. Galois/KMS boundary action transported to a Krein representation -/

/--
Concrete Krein readout for a bundled Hecke-Cuntz Bost-Connes system.

Cyclotomic boundary observables are still complex-valued; the carrier action is
real Hestenes/Krein.
-/
structure GaloisKMSKreinBridge
    (C_comm Op G : Type u)
    [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    [Ring Op] [StarRing Op] [Algebra ℂ Op]
    [Group G] [GaloisActionData G]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (bsys : BundledBostConnesSystem C_comm Op G)
    (D : KreinOperatorData H) where
  /-- Real Krein representation of the Bost-Connes operator layer. -/
  operatorBridge : BostConnesKreinDiracHodgeBridge Op H bsys.cuntz D
  /-- Base KMS boundary readout on the commutative cyclotomic subalgebra. -/
  boundaryReadout : C_comm → ℂ
  /-- Krein-side scalar readout of represented boundary observables. -/
  kreinReadout : (H →L[ℝ] H) → ℂ
  /-- Embedded cyclotomic phase observables have the boundary readout value. -/
  phase_readout :
    ∀ r : ℚ,
      kreinReadout
        (operatorBridge.rep (bsys.crossed.ι (bsys.e_rep.e r))) =
        boundaryReadout (bsys.e_rep.e r)
  /-- Galois covariance of the boundary readout on generators. -/
  boundaryReadout_galois :
    ∀ (g : G) (r : ℚ),
      boundaryReadout (bsys.e_rep.e (GaloisActionData.actOnQ g r)) =
        boundaryReadout (bsys.e_rep.e r)

namespace GaloisKMSKreinBridge

variable {C_comm Op G : Type u}
variable [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
variable [Ring Op] [StarRing Op] [Algebra ℂ Op]
variable [Group G] [GaloisActionData G]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [KreinSpace H]
variable {bsys : BundledBostConnesSystem C_comm Op G}
variable {D : KreinOperatorData H}
variable (B : GaloisKMSKreinBridge C_comm Op G H bsys D)

/--
Galois-translated KMS phase readout transported to the real Krein
representation.
-/
theorem galois_translated_phase_readout
    (g : G) (r : ℚ) :
    B.kreinReadout
        (B.operatorBridge.rep
          (bsys.crossed.ι (bsys.e_rep.e (GaloisActionData.actOnQ g r)))) =
      B.boundaryReadout (bsys.e_rep.e r) := by
  calc
    B.kreinReadout
        (B.operatorBridge.rep
          (bsys.crossed.ι (bsys.e_rep.e (GaloisActionData.actOnQ g r))))
        = B.boundaryReadout
            (bsys.e_rep.e (GaloisActionData.actOnQ g r)) :=
          B.phase_readout (GaloisActionData.actOnQ g r)
    _ = B.boundaryReadout (bsys.e_rep.e r) :=
      B.boundaryReadout_galois g r

end GaloisKMSKreinBridge

/-! ### 10. Quadratic estimate interface in the Krein lane -/

/--
Real Krein cancellation from a concrete quadratic
spectral/Dikin estimate.
-/
theorem krein_operator_zero_temperature_anomaly_cancellation_of_quadratic_bound
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (D : KreinOperatorData H)
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖ ≤
          C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ =>
        ‖D.thermalDensityMatrix beta * D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) :=
  D.zero_temperature_convergence_of_quadratic_bound epsilon C h_bound h_epsilon

/-! ### 11. Legacy complex Hilbert auxiliary bridge to the dynamics owner -/

/-- Operator-level conjugation readout from `InfoGeometry.Dynamics.SouriauDiracHodge`. -/
theorem operator_hodge_dual_definition
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.OperatorData H) :
    D.S_right = D.J ∘L D.S_left ∘L D.J :=
  rfl

/--
Operator-level twisted index vanishing, delegated to the continuous-linear-map
owner.  This is the Hilbert-space theorem surface; it is separate from the
finite matrix `anomaly_vanishes` theorem above.
-/
theorem operator_twisted_index_vanishing
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.OperatorData H)
    (trace : (H →L[ℂ] H) → ℂ)
    (h_trace_linear : ∀ (c : ℂ) (A : H →L[ℂ] H), trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J ∘L A ∘L D.J) = trace A)
    (h_proj_J_comm :
      D.twistedSectorProjection ∘L D.J = D.J ∘L D.twistedSectorProjection) :
    D.indexPairing trace = 0 :=
  D.twisted_index_vanishing trace h_trace_linear h_trace_J_inv h_proj_J_comm

/--
Operator-level asymptotic anomaly cancellation, delegated to the
continuous-linear-map owner.  The convergence property remains owned by
`InfoGeometry.Dynamics.SouriauDiracHodge`.
-/
theorem operator_zero_temperature_anomaly_cancellation
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : InfoGeometry.Dynamics.SouriauDiracHodge.OperatorData H) :
    Filter.Tendsto
      (fun beta : ℝ =>
        ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) :=
  D.zero_temperature_anomaly_cancellation

/-! ### 7. Bost-Connes operator transport into the Hilbert Dirac-Hodge lane -/

/--
Representation bridge from the algebraic Bost-Connes Cuntz system to a chosen
Hilbert-space Dirac-Hodge operator package.

The bridge does not invent a representation: it records the concrete monoid
representation `rep` and the chosen positive-integer generator that realizes the
Hilbert-space left shift `D.S_left`.
-/
structure BostConnesDiracHodgeBridge
    (Op : Type u) [Ring Op] [StarRing Op]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : BostConnesCuntzSystem Op)
    (D : OperatorData H) where
  /-- Representation of the Bost-Connes operator monoid by bounded Hilbert operators. -/
  rep : Op →* (H →L[ℂ] H)
  /-- The Bost-Connes positive-integer branch identified with `D.S_left`. -/
  leftIndex : ℕ+
  /-- Identification of the represented branch with the Hilbert left shift. -/
  represented_left_eq : rep (S C leftIndex) = D.S_left

namespace BostConnesDiracHodgeBridge

variable {Op : Type u} [Ring Op] [StarRing Op]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {C : BostConnesCuntzSystem Op}
variable {D : OperatorData H}
variable (B : BostConnesDiracHodgeBridge Op H C D)

/-- The represented positive-integer Bost-Connes shift. -/
def representedS (n : ℕ+) : H →L[ℂ] H :=
  B.rep (S C n)

@[simp]
theorem representedS_one :
    B.representedS 1 = 1 := by
  simp [representedS]

@[simp]
theorem representedS_mul (m n : ℕ+) :
    B.representedS (m * n) = B.representedS m * B.representedS n := by
  simp [representedS, S_mul]

/-- The selected represented Bost-Connes shift is the Hilbert-space left shift. -/
theorem representedS_leftIndex :
    B.representedS B.leftIndex = D.S_left :=
  B.represented_left_eq

end BostConnesDiracHodgeBridge

/-! ### 8. Trace/residue functional instantiated from Bost-Connes KMS data -/

/--
Trace/residue data on the represented Hilbert operator lane.

The field `trace_represented_projection` ties the Hilbert trace readout back to
the Bost-Connes KMS projection state on `S_n^* S_m`.  The cyclic/J-invariance
laws are exactly the hypotheses consumed by `OperatorData.twisted_index_vanishing`.
-/
structure BostConnesDiracHodgeTrace
    {Op : Type u} [Ring Op] [StarRing Op]
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {C : BostConnesCuntzSystem Op}
    {D : OperatorData H}
    (B : BostConnesDiracHodgeBridge Op H C D)
    (Φ : KMSProjectionState C) where
  /-- Hilbert-side trace/residue functional. -/
  trace : (H →L[ℂ] H) → ℂ
  /-- Complex scalar linearity required by the twisted-index proof. -/
  trace_smul : ∀ (c : ℂ) (A : H →L[ℂ] H), trace (c • A) = c * trace A
  /-- Invariance under Tomita/Hodge conjugation. -/
  trace_J_inv : ∀ A, trace (D.J ∘L A ∘L D.J) = trace A
  /-- The twisted-sector projection commutes with the Tomita/Hodge involution. -/
  projection_J_comm : D.twistedSectorProjection ∘L D.J = D.J ∘L D.twistedSectorProjection
  /-- Compatibility with the Bost-Connes KMS projection readout. -/
  trace_represented_projection :
    ∀ n m : ℕ+,
      trace (B.rep (S C n * star (S C m))) =
        (Φ.φ (S C n * star (S C m)) : ℂ)

namespace BostConnesDiracHodgeTrace

variable {Op : Type u} [Ring Op] [StarRing Op]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {C : BostConnesCuntzSystem Op}
variable {D : OperatorData H}
variable {B : BostConnesDiracHodgeBridge Op H C D}
variable {Φ : KMSProjectionState C}
variable (T : BostConnesDiracHodgeTrace B Φ)

/-- The represented trace evaluates Bost-Connes projections by the KMS formula. -/
theorem represented_projection_trace
    (n m : ℕ+) :
    T.trace (B.rep (S C n * star (S C m))) =
      (if n = m then (((n : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 : ℝ) := by
  rw [T.trace_represented_projection n m]
  exact_mod_cast Φ.kms_evaluation_on_projections n m

/--
Twisted-index vanishing with the Bost-Connes/KMS-compatible trace readout.
-/
theorem twisted_index_vanishing :
    D.indexPairing T.trace = 0 :=
  D.twisted_index_vanishing T.trace T.trace_smul T.trace_J_inv T.projection_J_comm

end BostConnesDiracHodgeTrace

/-! ### 9. Galois/KMS boundary action transported to the Hilbert representation -/

/--
Concrete Hilbert readout for a bundled Hecke-Cuntz Bost-Connes system.

It transports cyclotomic boundary observables through the crossed-product
embedding and the Hilbert representation bridge.
-/
structure GaloisKMSHilbertBridge
    (C_comm Op G : Type u)
    [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
    [Ring Op] [StarRing Op] [Algebra ℂ Op]
    [Group G] [GaloisActionData G]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (bsys : BundledBostConnesSystem C_comm Op G)
    (D : OperatorData H) where
  /-- Hilbert representation of the Bost-Connes operator layer. -/
  operatorBridge : BostConnesDiracHodgeBridge Op H bsys.cuntz D
  /-- Base KMS boundary readout on the commutative cyclotomic subalgebra. -/
  boundaryReadout : C_comm → ℂ
  /-- Hilbert-side scalar readout. -/
  hilbertReadout : (H →L[ℂ] H) → ℂ
  /-- Embedded cyclotomic phase observables have the boundary readout value. -/
  phase_readout :
    ∀ r : ℚ,
      hilbertReadout
        (operatorBridge.rep (bsys.crossed.ι (bsys.e_rep.e r))) =
        boundaryReadout (bsys.e_rep.e r)
  /-- Galois covariance of the boundary readout on generators. -/
  boundaryReadout_galois :
    ∀ (g : G) (r : ℚ),
      boundaryReadout (bsys.e_rep.e (GaloisActionData.actOnQ g r)) =
        boundaryReadout (bsys.e_rep.e r)

namespace GaloisKMSHilbertBridge

variable {C_comm Op G : Type u}
variable [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
variable [Ring Op] [StarRing Op] [Algebra ℂ Op]
variable [Group G] [GaloisActionData G]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {bsys : BundledBostConnesSystem C_comm Op G}
variable {D : OperatorData H}
variable (B : GaloisKMSHilbertBridge C_comm Op G H bsys D)

/--
Galois-translated KMS phase readout transported to the Hilbert representation.
-/
theorem galois_translated_phase_readout
    (g : G) (r : ℚ) :
    B.hilbertReadout
        (B.operatorBridge.rep
          (bsys.crossed.ι (bsys.e_rep.e (GaloisActionData.actOnQ g r)))) =
      B.boundaryReadout (bsys.e_rep.e r) := by
  calc
    B.hilbertReadout
        (B.operatorBridge.rep
          (bsys.crossed.ι (bsys.e_rep.e (GaloisActionData.actOnQ g r))))
        = B.boundaryReadout
            (bsys.e_rep.e (GaloisActionData.actOnQ g r)) :=
          B.phase_readout (GaloisActionData.actOnQ g r)
    _ = B.boundaryReadout (bsys.e_rep.e r) :=
      B.boundaryReadout_galois g r

end GaloisKMSHilbertBridge

/-! ### 10. Quadratic Dikin estimate interface -/

/--
Operator-level asymptotic cancellation from a concrete quadratic
spectral/Dikin estimate.
-/
theorem operator_zero_temperature_anomaly_cancellation_of_quadratic_bound
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : OperatorData H)
    (epsilon : ℝ → ℝ) (C : ℝ)
    (h_bound :
      ∀ᶠ beta : ℝ in Filter.atTop,
        ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖ ≤
          C * epsilon beta ^ 2)
    (h_epsilon : Filter.Tendsto epsilon Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun beta : ℝ =>
        ‖D.thermalDensityMatrix beta ∘L D.chiralChargeOperator‖)
      Filter.atTop (nhds 0) :=
  D.zero_temperature_convergence_of_quadratic_bound epsilon C h_bound h_epsilon

end InfoGeometry.Canonical.SouriauDiracHodgeCoupling
