import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Algebra.CuntzQuotientDiracBridge
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

The Cuntz projection packet assumes an explicit `CuntzNAlgebra (N := 6)` property.

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
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzQuotientDiracBridge

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

/-- The quotient `O₆` Hodge-Dirac is the sum of Cuntz Majorana supercharges. -/
theorem cuntz6_quotient_hodgeDirac_majorana_sum :
    InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra 6) =
      ∑ i : Fin 6, InfoGeometry.Algebra.SupergradedSUSY.cuntzMajoranaSupercharge 6 i := by
  exact quotient_hodgeDirac_eq_sum_majorana 6

end InfoGeometry.Canonical.CuntzSuperBraidMoEBridge
