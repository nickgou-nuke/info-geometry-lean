import Mathlib
import InfoGeometry.Lie.CanonicalZornG2MasterRootSynthesis
import InfoGeometry.Canonical.CyclotomicOperatorSpine
import InfoGeometry.Canonical.ViazovskaLeechGolayWeld
import Omega.Zeta.CyclotomicSectorIdentity

noncomputable section

namespace InfoGeometry.Canonical.G2LeechCoxeterBoundaryBridge

open Complex
open InfoGeometry.Lie.CanonicalZornG2MasterRootSynthesis
open InfoGeometry.Lie.CanonicalZornG2RootMetricGeometry
open InfoGeometry.Lie.CanonicalZornG2CoxeterRelations
open InfoGeometry.Lie.CanonicalZornG2ToMatrixBridge
open Omega.Zeta.CyclotomicSectorIdentity
open InfoGeometry.Canonical.ViazovskaLeechGolayWeld

/-- Re-export of the repository's complete, already verified `G2` root packet:
12 nonzero root directions, explicit planar coordinates, exact long/short
length ratio, 150-degree simple-root angle, highest-root orthogonality, and
Weyl Coxeter relation of order six. -/
theorem verified_g2_root_coxeter_packet :=
  grand_g2_master_root_unification

/-- The first primitive 24th root used for the abstract Coxeter-plane readout. -/
def zeta24 : ℂ := rootOfUnity 24 1

/-- The selected 24th root is primitive. -/
theorem zeta24_isPrimitiveRoot : IsPrimitiveRoot zeta24 24 := by
  simpa [zeta24] using isPrimitiveRoot_rootOfUnity_one 24 (by norm_num)

@[simp] theorem zeta24_pow_24 : zeta24 ^ 24 = 1 :=
  zeta24_isPrimitiveRoot.pow_eq_one

/-- Abstract complex Coxeter-plane orbit of a nonzero projected vector. -/
def planeOrbit (z : ℂ) (k : ℕ) : ℂ :=
  zeta24 ^ k * z

/-- Every abstract order-24 orbit is 24-periodic. -/
theorem planeOrbit_add_24 (z : ℂ) (k : ℕ) :
    planeOrbit z (k + 24) = planeOrbit z k := by
  simp [planeOrbit, pow_add, mul_assoc]

/-- A nonzero projected vector has 24 distinct points in its first orbit cycle. -/
theorem planeOrbit_injective_on_range
    {z : ℂ} (hz : z ≠ 0) :
    Set.InjOn (planeOrbit z) (↑(Finset.range 24) : Set ℕ) := by
  intro a ha b hb hab
  have hp : zeta24 ^ a = zeta24 ^ b := by
    exact mul_right_cancel₀ hz hab
  exact zeta24_isPrimitiveRoot.pow_inj
    (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hp

/-- The 12-gon phase subsequence is obtained by taking every second point of
the primitive 24-gon.  This is a cyclotomic containment only; it is not an
identification with the `G2` root system. -/
def twelvePhaseOrbit (z : ℂ) (k : ℕ) : ℂ :=
  planeOrbit z (2 * k)

/-- The 12-phase subsequence is periodic with period 12. -/
theorem twelvePhaseOrbit_add_12 (z : ℂ) (k : ℕ) :
    twelvePhaseOrbit z (k + 12) = twelvePhaseOrbit z k := by
  simp [twelvePhaseOrbit, planeOrbit, Nat.mul_add, pow_add, mul_assoc]

/-- The 6-gon phase subsequence is obtained by taking every fourth point of
the primitive 24-gon. -/
def sixPhaseOrbit (z : ℂ) (k : ℕ) : ℂ :=
  planeOrbit z (4 * k)

/-- The 6-phase subsequence is periodic with period 6. -/
theorem sixPhaseOrbit_add_6 (z : ℂ) (k : ℕ) :
    sixPhaseOrbit z (k + 6) = sixPhaseOrbit z k := by
  simp [sixPhaseOrbit, planeOrbit, Nat.mul_add, pow_add, mul_assoc]

/-- A generic iterate used to state projection equivariance without assuming a
Leech-lattice carrier that the repository does not yet construct. -/
def iterate {V : Type*} (w : V → V) : ℕ → V → V
  | 0, x => x
  | n + 1, x => w (iterate w n x)

/-- If a projection intertwines an ambient action with multiplication by the
primitive 24th root, every projected iterate has the exact cyclotomic phase. -/
theorem projected_iterate_eq_planeOrbit
    {V : Type*} (w : V → V) (pi : V → ℂ)
    (hpi : ∀ x, pi (w x) = zeta24 * pi x)
    (x : V) (n : ℕ) :
    pi (iterate w n x) = planeOrbit (pi x) n := by
  induction n with
  | zero => simp [iterate, planeOrbit]
  | succ n ih =>
      rw [iterate, hpi, ih]
      simp [planeOrbit, pow_succ, mul_assoc]

/-- Under the same equivariance hypothesis, a nonzero projected vector has 24
distinct projected points in its first cycle. -/
theorem projected_first_cycle_injective
    {V : Type*} (w : V → V) (pi : V → ℂ)
    (hpi : ∀ x, pi (w x) = zeta24 * pi x)
    {x : V} (hx : pi x ≠ 0) :
    Set.InjOn (fun n => pi (iterate w n x)) (↑(Finset.range 24) : Set ℕ) := by
  intro a ha b hb hab
  rw [projected_iterate_eq_planeOrbit w pi hpi x a,
    projected_iterate_eq_planeOrbit w pi hpi x b] at hab
  exact planeOrbit_injective_on_range hx ha hb hab

/-- Existing exact Leech minimal-vector count.  This is a numerical/counting
owner theorem and does not supply a Coxeter projection. -/
theorem leech_minimal_vector_count_readout :
    leechMinimalVectorCount = 196560 :=
  leechMinimalVectorCount_eq

/-- Existing exact minimal squared norm readout. -/
theorem leech_minimal_norm_sq_readout : leechMinimalNormSq = 4 := by
  rfl

end InfoGeometry.Canonical.G2LeechCoxeterBoundaryBridge
