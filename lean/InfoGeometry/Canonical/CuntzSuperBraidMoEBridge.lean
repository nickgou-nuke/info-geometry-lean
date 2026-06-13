import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Canonical.FiniteMajoranaBraiding
import InfoGeometry.Canonical.MixtureOfExperts

/-!
# Finite Cuntz / Super-Braid / MoE Bridge

This module anchors the proposed Cuntz-superalgebraic braid layer in finite,
kernel-checked owner facts.

#### BUCKET 1: CLOSED FINITE THEOREMS

* the `B₆` permutation shadow satisfies the Artin braid relation and separated
  particle/hole sector commutation;
* the central adjacent generator swaps the boundary particle/hole strands;
* abstract `O₆` Cuntz range projections are idempotent, mutually orthogonal,
  and sum to one through the existing `CuntzNAlgebra` owner;
* the Nambu particle/hole split has a `Z₂` superparity with odd cross-sector
  pairs;
* a scalar dissipative residual vanishes exactly when the two jump weights agree;
* two-expert MoE gates preserve their declared partition of unity.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The Cuntz projection packet assumes an explicit `CuntzNAlgebra (N := 6)` witness.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here constructs a full braid-group representation in a Cuntz
`C*`-algebra, proves a Jones polynomial or knot invariant, proves non-unitary
dissipative dynamics, constructs a Krein-Fock representation, or identifies the
isotropic Pauli anchor with a central full twist.  Those remain open until the
needed analytic/operator-algebraic premises exist.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzSuperBraidMoEBridge

open InfoGeometry.Canonical.FiniteMajoranaBraiding
open InfoGeometry.Algebra.Cuntz

/-! ## B₆ permutation shadow -/

/-- The five adjacent-generator labels for the permutation shadow of `B₆`. -/
abbrev B6Gen := Fin 5

/-- The permutation shadow of the Artin generator `σᵢ` on six Nambu strands. -/
def sigmaB6 (i : B6Gen) : Equiv.Perm ℕ :=
  majoranaSwap i.val

/-- The first particle-sector Artin relation: `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂`. -/
theorem particle_sector_artin :
    sigmaB6 ⟨0, by decide⟩ * sigmaB6 ⟨1, by decide⟩ * sigmaB6 ⟨0, by decide⟩ =
      sigmaB6 ⟨1, by decide⟩ * sigmaB6 ⟨0, by decide⟩ * sigmaB6 ⟨1, by decide⟩ :=
  majoranaSwap_braid 0

/-- The hole-sector Artin relation: `σ₄ σ₅ σ₄ = σ₅ σ₄ σ₅`. -/
theorem hole_sector_artin :
    sigmaB6 ⟨3, by decide⟩ * sigmaB6 ⟨4, by decide⟩ * sigmaB6 ⟨3, by decide⟩ =
      sigmaB6 ⟨4, by decide⟩ * sigmaB6 ⟨3, by decide⟩ * sigmaB6 ⟨4, by decide⟩ :=
  majoranaSwap_braid 3

/-- Particle-sector and hole-sector braid generators commute in the finite shadow. -/
theorem particle_hole_sector_commute
    (i j : B6Gen) (hi : i.val ≤ 1) (hj : 3 ≤ j.val) :
    sigmaB6 i * sigmaB6 j = sigmaB6 j * sigmaB6 i := by
  exact majoranaSwap_comm_of_separated (i := i.val) (j := j.val) (by omega)

/-- The central dissipative-link generator sends strand `3` to strand `4` in 1-based language. -/
theorem central_generator_particle_to_hole :
    sigmaB6 ⟨2, by decide⟩ 2 = 3 := by
  simp [sigmaB6]

/-- The same central generator sends strand `4` back to strand `3` in the permutation shadow. -/
theorem central_generator_hole_to_particle :
    sigmaB6 ⟨2, by decide⟩ 3 = 2 := by
  simp [sigmaB6]

/-! ## Abstract Cuntz-6 projection owner readbacks -/

/--
The exact `O₆` projection facts are delegated to the abstract `CuntzNAlgebra`
owner.  This avoids pretending that the Cuntz algebra has a faithful finite
matrix representation.
-/
theorem cuntz6_projection_packet
    {Op : Type*} [Ring Op] [StarRing Op]
    (O : CuntzNAlgebra (N := 6) Op) :
    (∀ i : Fin 6,
      (O.S i * star (O.S i)) * (O.S i * star (O.S i)) = O.S i * star (O.S i)) ∧
    (∀ i j : Fin 6, i ≠ j →
      (O.S i * star (O.S i)) * (O.S j * star (O.S j)) = 0) ∧
    (∑ i : Fin 6, O.S i * star (O.S i)) = 1 := by
  exact ⟨range_projection_idempotent O, range_projection_orthogonal O,
    range_projections_sum_one O⟩

/-! ## Nambu particle/hole superparity -/

/-- The two Nambu sectors for the split `3 ⊕ 3*` carrier. -/
inductive NambuSector where
  | particle
  | hole
  deriving DecidableEq, Repr

namespace NambuSector

/-- `Z₂` parity sign: particles are even, holes are odd. -/
def parity : NambuSector → ℤ
  | particle => 1
  | hole => -1

/-- Every sector parity squares to one. -/
theorem parity_sq (s : NambuSector) : parity s * parity s = 1 := by
  cases s <;> norm_num [parity]

end NambuSector

/-- Six Nambu strands: `0,1,2` are particles and `3,4,5` are holes. -/
def strandSector (i : Fin 6) : NambuSector :=
  if i.val < 3 then NambuSector.particle else NambuSector.hole

/-- Particle strands have even parity. -/
theorem particle_strand_parity (i : Fin 6) (hi : i.val < 3) :
    NambuSector.parity (strandSector i) = 1 := by
  simp [strandSector, hi, NambuSector.parity]

/-- Hole strands have odd parity. -/
theorem hole_strand_parity (i : Fin 6) (hi : 3 ≤ i.val) :
    NambuSector.parity (strandSector i) = -1 := by
  have hnot : ¬ i.val < 3 := by omega
  simp [strandSector, hnot, NambuSector.parity]

/-- Cross-sector particle/hole operators are odd. -/
theorem cross_sector_parity_odd
    (i j : Fin 6) (hi : i.val < 3) (hj : 3 ≤ j.val) :
    NambuSector.parity (strandSector i) * NambuSector.parity (strandSector j) = -1 := by
  rw [particle_strand_parity i hi, hole_strand_parity j hj]
  norm_num

/-- Particle strand associated to an isotropic pair label. -/
def particleStrand (k : Fin 3) : Fin 6 :=
  ⟨k.val, by omega⟩

/-- Hole strand associated to an isotropic pair label. -/
def holeStrand (k : Fin 3) : Fin 6 :=
  ⟨k.val + 3, by omega⟩

/-- Each particle/hole pair in the isotropic anchor is odd under the superparity. -/
theorem isotropic_pair_cross_parity_odd (k : Fin 3) :
    NambuSector.parity (strandSector (particleStrand k)) *
      NambuSector.parity (strandSector (holeStrand k)) = -1 := by
  exact cross_sector_parity_odd (particleStrand k) (holeStrand k) (by simp [particleStrand])
    (by simp [holeStrand])

/-! ## Dissipative scalar residual and two-expert gate -/

/-- Scalar residual for asymmetric particle-to-hole and hole-to-particle jump weights. -/
def dissipativeResidual (forward backward : ℝ) : ℝ :=
  forward - backward

/-- The finite scalar residual vanishes exactly when the two jump weights agree. -/
theorem dissipativeResidual_eq_zero_iff (forward backward : ℝ) :
    dissipativeResidual forward backward = 0 ↔ forward = backward := by
  simp [dissipativeResidual, sub_eq_zero]

/-- Two-sector MoE gate for particle and hole experts. -/
structure TwoExpertGate where
  particleWeight : ℝ
  holeWeight : ℝ
  sum_one : particleWeight + holeWeight = 1

namespace TwoExpertGate

/-- Read back the declared partition of unity. -/
theorem weights_sum_one (g : TwoExpertGate) :
    g.particleWeight + g.holeWeight = 1 :=
  g.sum_one

end TwoExpertGate

/-- Closed finite packet for the Cuntz-super-braid/MoE bridge. -/
theorem finite_cuntz_super_braid_moe_packet :
    sigmaB6 ⟨2, by decide⟩ 2 = 3 ∧
    sigmaB6 ⟨2, by decide⟩ 3 = 2 ∧
    (∀ i j : B6Gen, i.val ≤ 1 → 3 ≤ j.val →
      sigmaB6 i * sigmaB6 j = sigmaB6 j * sigmaB6 i) ∧
    (∀ s : NambuSector, NambuSector.parity s * NambuSector.parity s = 1) ∧
    (∀ k : Fin 3,
      NambuSector.parity (strandSector (particleStrand k)) *
        NambuSector.parity (strandSector (holeStrand k)) = -1) ∧
    (∀ forward backward : ℝ,
      dissipativeResidual forward backward = 0 ↔ forward = backward) ∧
    (∀ g : TwoExpertGate, g.particleWeight + g.holeWeight = 1) := by
  exact ⟨central_generator_particle_to_hole, central_generator_hole_to_particle,
    particle_hole_sector_commute, NambuSector.parity_sq, isotropic_pair_cross_parity_odd,
    dissipativeResidual_eq_zero_iff, TwoExpertGate.weights_sum_one⟩

end InfoGeometry.Canonical.CuntzSuperBraidMoEBridge

end
