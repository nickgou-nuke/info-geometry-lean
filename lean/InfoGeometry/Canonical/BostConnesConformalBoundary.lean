import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordExternalChain

/-!
# Bost--Connes Conformal Boundary

This module connects the theorem-owned Bost--Connes KMS projection corridor to
the external `VirasoroProject` Sugawara boundary facts.

It deliberately does **not** claim a full split-Clifford-to-Heisenberg
bosonization isomorphism.  The currently closed content is the uncharged
Fock-space Sugawara vacuum surface and a conditional readout theorem saying
that any supplied Sugawara/graded-trace functional compatible with the
Bost--Connes projection state inherits the documented KMS matrix coefficient.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `uncharged_sugawaraL0_vacuum` proves that the uncharged vacuum has
  `L₀`-energy `0`.
* `uncharged_sugawara_central_vacuum` proves that the Virasoro central
  generator acts as the identity on the uncharged vacuum.
* `uncharged_sugawara_positive_modes_annihilate_vacuum` proves the
  highest-weight positive-mode annihilation.
* `uncharged_heisenberg_sugawara_centralCharge_one` reuses the external
  Heisenberg Sugawara central-charge owner.
* `sugawaraTrace_kms_evaluation_on_projections` transports the already proved
  Bost--Connes projection evaluation across an explicitly supplied trace
  compatibility premise.
* `sugawaraTrace_kms_evaluation_on_word_products` and
  `sugawaraTrace_kms_evaluation_on_prime_power_word_products` extend that
  transfer to multiplicative words and explicit prime-power decompositions.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

* `sugawaraTrace_kms_evaluation_on_projections` depends on the visible premise
  `hTrace`, which is the future graded-trace/Sugawara compatibility theorem.

#### BUCKET 3: OPEN CLOSURE DEBT

* Construct the actual split-Clifford/CAR current map into the Heisenberg
  current algebra, including normal-ordering compatibility.
* Prove the graded trace over the charged Fock space and identify its
  Bost--Connes KMS projection readout.
-/

noncomputable section

namespace InfoGeometry.Canonical.BostConnesConformalBoundary

open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.SplitCliffordExternalChain
open VirasoroProject

/-! ## 1. Uncharged Sugawara boundary -/

/-- The uncharged external Fock-space boundary. -/
abbrev UnchargedFockSpace :=
  VirasoroProject.ChargedFockSpace ℂ (0 : ℂ)

/-- The absolute-zero/uncharged vacuum vector in the external Fock space. -/
def unchargedVacuum : UnchargedFockSpace :=
  VirasoroProject.ChargedFockSpace.vacuum ℂ (0 : ℂ)

/-- The Sugawara conformal Hamiltonian `L₀` on the uncharged boundary. -/
def sugawaraL0 : UnchargedFockSpace →ₗ[ℂ] UnchargedFockSpace :=
  VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ (0 : ℂ) (.lgen ℂ 0)

/-- The uncharged vacuum has zero Sugawara `L₀` energy. -/
theorem uncharged_sugawaraL0_vacuum :
    sugawaraL0 unchargedVacuum = 0 := by
  simpa [sugawaraL0, unchargedVacuum] using
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum
      ℂ (0 : ℂ))

/-- The Virasoro central generator acts as the identity on the uncharged vacuum. -/
theorem uncharged_sugawara_central_vacuum :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ (0 : ℂ) (.cgen ℂ)
      unchargedVacuum = unchargedVacuum := by
  simp [unchargedVacuum]

/-- Positive Virasoro modes annihilate the uncharged vacuum. -/
theorem uncharged_sugawara_positive_modes_annihilate_vacuum
    {n : ℤ} (hn : 0 < n) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ (0 : ℂ) (.lgen ℂ n)
      unchargedVacuum = 0 := by
  simpa [unchargedVacuum] using
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum
      ℂ (0 : ℂ) hn)

/-- The external Heisenberg Sugawara boundary has central charge `1`. -/
theorem uncharged_heisenberg_sugawara_centralCharge_one :
    InfoGeometry.OperatorAlgebra.VirasoroProjectBridge.heisenbergSugawaraDatum.centralCharge = 1 :=
  externalHeisenberg_sugawaraDatum_centralCharge_one

/-! ## 2. Conditional Sugawara trace readout for Bost--Connes projections -/

variable {Op : Type*} [Ring Op] [StarRing Op]

/--
Conditional Sugawara trace readout for the Bost--Connes projection matrix
coefficients.

The functional `τL0` is intended to be the future graded trace determined by
the Sugawara Hamiltonian `L₀`.  This theorem does not construct that trace; it
states the exact payoff once the compatibility premise `hTrace` is proved.
-/
theorem sugawaraTrace_kms_evaluation_on_projections
    {C : BostConnesCuntzSystem Op}
    (Φ : KMSProjectionState C)
    (τL0 : Op → ℝ)
    (hTrace :
      ∀ n m : ℕ+,
        τL0 (S C n * star (S C m)) = Φ.φ (S C n * star (S C m)))
    (n m : ℕ+) :
    τL0 (S C n * star (S C m)) =
      if n = m then ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 := by
  rw [hTrace n m]
  exact Φ.kms_evaluation_on_projections n m

/--
Diagonal Sugawara trace readout, conditional on the same explicit trace
compatibility premise.
-/
theorem sugawaraTrace_kms_evaluation_on_diagonal_projection
    {C : BostConnesCuntzSystem Op}
    (Φ : KMSProjectionState C)
    (τL0 : Op → ℝ)
    (hTrace :
      ∀ n m : ℕ+,
        τL0 (S C n * star (S C m)) = Φ.φ (S C n * star (S C m)))
    (n : ℕ+) :
    τL0 (S C n * star (S C n)) = ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ := by
  simpa using sugawaraTrace_kms_evaluation_on_projections
    (C := C) Φ τL0 hTrace n n

/--
Sugawara trace readout after reducing arbitrary indexed words to their
multiplicative positive-integer products.
-/
theorem sugawaraTrace_kms_evaluation_on_word_products
    {C : BostConnesCuntzSystem Op}
    (Φ : KMSProjectionState C)
    (τL0 : Op → ℝ)
    (hTrace :
      ∀ n m : ℕ+,
        τL0 (S C n * star (S C m)) = Φ.φ (S C n * star (S C m)))
    (ns ms : List ℕ+) :
    τL0 (S C ns.prod * star (S C ms.prod)) =
      if ns.prod = ms.prod then
        (((ns.prod : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ
      else 0 := by
  rw [hTrace ns.prod ms.prod]
  exact Φ.kms_evaluation_on_word_products ns ms

/--
Sugawara trace readout for words supplied as explicit prime-power
factorization lists.

The accompanying generator rewrite is
`BostConnesKMS.S_prime_power_list_prod`; this theorem evaluates the resulting
matrix coefficient at the product index.
-/
theorem sugawaraTrace_kms_evaluation_on_prime_power_word_products
    {C : BostConnesCuntzSystem Op}
    (Φ : KMSProjectionState C)
    (τL0 : Op → ℝ)
    (hTrace :
      ∀ n m : ℕ+,
        τL0 (S C n * star (S C m)) = Φ.φ (S C n * star (S C m)))
    (left right : List PrimePowerIndex) :
    τL0
      (S C (left.map PrimePowerIndex.toPNat).prod *
        star (S C (right.map PrimePowerIndex.toPNat).prod)) =
      if (left.map PrimePowerIndex.toPNat).prod =
          (right.map PrimePowerIndex.toPNat).prod then
        ((((left.map PrimePowerIndex.toPNat).prod : ℕ+) : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ
      else 0 := by
  exact sugawaraTrace_kms_evaluation_on_word_products
    (C := C) Φ τL0 hTrace
    (left.map PrimePowerIndex.toPNat)
    (right.map PrimePowerIndex.toPNat)

end InfoGeometry.Canonical.BostConnesConformalBoundary
