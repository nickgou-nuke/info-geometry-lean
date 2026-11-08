/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Categorical.TypedPeirceArchetype
import InfoGeometry.Physics.ChevalleySpinorIdeal
import InfoGeometry.Physics.ChevalleyDyadIsomorphism
import InfoGeometry.Physics.Cl11WittChevalleyBridge
import InfoGeometry.Physics.NambuSpinorGrassmannian
import InfoGeometry.Physics.HyperbolicBogoliubovRotation
import InfoGeometry.Physics.KreinBdGMassDecoupling
import InfoGeometry.Physics.ChevalleyNambuCARBridge
import InfoGeometry.Physics.NambuSpinorHolonomy
import InfoGeometry.Physics.LogCFTSymplecticSpinorBridge
import InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset
import InfoGeometry.Physics.NoncommutativeZornBdGDerivations

/-!
# Canonical Mathematical Synthesis: The Archetypal Causal Poset

This module formalizes the unified mathematical machine underlying the raw stream
of ideas connecting nilpotents, Hodge chiral calculus, Claude Chevalley's spinors,
dyad operator algebras, and Bogoliubov-de Gennes mass condensation.

## The Shared Causal Prerequisite Poset

The stage order is owned by `CanonicalArchetypeCausalPoset`; this module adds
operator theorems on the represented CAR and Nambu carriers without declaring
a second stage type. Its relevant branches are:

```
  CAR nilpotents → Peirce involution → Chevalley dyads
                                      ├→ multi-mode CAR → Krein rotation → scalar mass model
                                      └→ CAR–Nambu fourth root → complex structure → spinor holonomy
```

All definitions and theorems in this file are genuine Lean 4 formalizations with complete proofs.
-/

namespace InfoGeometry.Physics.CanonicalSynthesis

open CategoryTheory
open CategoryTheory.Preadditive
open InfoGeometry.Physics.Chevalley
open InfoGeometry.Physics.ChevalleyDyad
open InfoGeometry.Physics.Cl11WittChevalleyBridge
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Physics.NambuGrassmannian
open InfoGeometry.Physics.Bogoliubov
open InfoGeometry.Physics.BdGCondensation
open InfoGeometry.Physics.NambuSpinorHolonomy
open InfoGeometry.QuantumContext.CanonicalArchetypeCausalPoset

/-! ### 1. Shared prerequisite-order integration

The relation itself is owned by `CanonicalArchetypeCausalPoset`. The theorems
below use its labels directly; operator identities are proved in the later
sections and are not inferred from a stage comparison. -/

/-! ### 2. Synthesis Theorem 0 → 1: From Nilpotent CAR to Peirce Involutions -/

section Stage0to1

variable {R : Type*} [Ring R]

/-- From a pair of square-zero elements `(n, p)` with CAR pairing
`n * p + p * n = 1`, derive the following Peirce identities:
1. `P₊² = P₊` and `P₋² = P₋` (orthogonal projectors)
2. `P₊ P₋ = 0` and `P₋ P₊ = 0` (mutual annihilation)
3. `P₊ + P₋ = 1` (partition of unity)
4. `ε² = 1` (split involution grading `ε = [n, p]`)
5. `ε n + n ε = 0` and `ε p + p ε = 0` (odd parity reflection). -/
theorem synthesis_stage0_to_stage1 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    (P_plus n p * P_plus n p = P_plus n p) ∧
    (P_minus n p * P_minus n p = P_minus n p) ∧
    (P_plus n p * P_minus n p = 0) ∧
    (P_minus n p * P_plus n p = 0) ∧
    (P_plus n p + P_minus n p = 1) ∧
    (chiralGrading n p * chiralGrading n p = 1) ∧
    (chiralGrading n p * n + n * chiralGrading n p = 0) ∧
    (chiralGrading n p * p + p * chiralGrading n p = 0) := by
  refine ⟨P_plus_sq n p h_nil_n h_car,
          P_minus_sq n p h_nil_p h_car,
          P_plus_mul_P_minus_zero n p h_nil_p,
          P_minus_mul_P_plus_zero n p h_nil_n,
          partition_of_unity n p h_car,
          chiralGrading_sq n p h_nil_n h_nil_p h_car,
          chiralGrading_anticommutes_n n p h_nil_n h_car,
          chiralGrading_anticommutes_p n p h_nil_p h_car⟩

end Stage0to1

/-! ### 3. Synthesis Theorem 1 → 2: Peirce Idempotents to Chevalley Dyads -/

section Stage1to2

variable {R : Type*} [Ring R]

/-- Under the CAR hypotheses, the Chevalley dyads satisfy:
1. The four algebraic overlaps are `e₀`, `0`, `0`, `e₀` (these are not scalar-valued
   Hilbert-space inner products).
2. `E₀₀ = n p`, `E₀₁ = n`, `E₁₀ = p`, `E₁₁ = p n` (algebra generators)
3. `E₀₀ + E₁₁ = 1` (resolution of identity)
This theorem gives these identities in `R`; it does not assert an isomorphism
between `R` and a matrix ring. The matrix-unit multiplication laws are proved
separately in the dyad owner. -/
theorem synthesis_stage1_to_stage2 (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    (bra0 n p * ket0 n p = e0 n p) ∧
    (bra0 n p * ket1 n p = 0) ∧
    (bra1 n p * ket0 n p = 0) ∧
    (bra1 n p * ket1 n p = e0 n p) ∧
    (E00 n p = n * p) ∧
    (E01 n p = n) ∧
    (E10 n p = p) ∧
    (E11 n p = p * n) ∧
    (E00 n p + E11 n p = 1) := by
  refine ⟨inner00 n p h_nil_n h_car,
          inner01 n p h_nil_p,
          inner10 n p h_nil_n,
          inner11 n p h_nil_n h_nil_p h_car,
          E00_eval n p h_nil_n h_car,
          E01_eval n p h_nil_n h_car,
          E10_eval n p h_nil_p h_car,
          E11_eval n p h_nil_n h_nil_p h_car,
          resolution_of_identity n p h_nil_n h_nil_p h_car⟩

/-- Pauli-Nambu bivector realization directly from dyad units. -/
theorem synthesis_pauli_nambu_algebra (n p : R)
    (h_nil_n : n * n = 0)
    (h_nil_p : p * p = 0)
    (h_car : n * p + p * n = 1) :
    (tau1 n p * tau1 n p = 1) ∧
    (tau3 n p * tau3 n p = 1) ∧
    (diracVector n p * diracVector n p = -1) ∧
    (tau1 n p * tau3 n p + tau3 n p * tau1 n p = 0) ∧
    (diracVector n p * tau1 n p + tau1 n p * diracVector n p = 0) ∧
    (diracVector n p * tau1 n p = tau3 n p) := by
  refine ⟨tau1_sq n p h_nil_n h_nil_p h_car,
          tau3_sq n p h_nil_n h_nil_p h_car,
          diracVector_sq n p h_nil_n h_nil_p h_car,
          tau1_anticommutes_tau3 n p h_nil_n h_nil_p h_car,
          diracVector_anticommutes_tau1 n p h_nil_n h_nil_p h_car,
          diracVector_mul_tau1_eq_tau3 n p h_nil_n h_nil_p h_car⟩

end Stage1to2

/-! ### Concrete Mathlib instance: the Witt pair in `Cl(1,1)` -/

section Cl11Instance

/-- The repo's concrete Witt creation and annihilation elements in
`CliffordAlgebra q11` instantiate the abstract CAR-to-Peirce-to-dyad chain.
The final four equalities identify the abstract Chevalley matrix units with
the existing Witt matrix units under `cl11EquivMat`; the diagonal order is
the one proved by `Cl11WittChevalleyBridge`. -/
theorem cl11_witt_pair_to_matrix_dyads :
    (P_plus cliffordWittAnnihilation cliffordWittCreation *
      P_plus cliffordWittAnnihilation cliffordWittCreation =
      P_plus cliffordWittAnnihilation cliffordWittCreation) ∧
    (P_minus cliffordWittAnnihilation cliffordWittCreation *
      P_minus cliffordWittAnnihilation cliffordWittCreation =
      P_minus cliffordWittAnnihilation cliffordWittCreation) ∧
    (P_plus cliffordWittAnnihilation cliffordWittCreation +
      P_minus cliffordWittAnnihilation cliffordWittCreation = 1) ∧
    (chiralGrading cliffordWittAnnihilation cliffordWittCreation *
      chiralGrading cliffordWittAnnihilation cliffordWittCreation = 1) ∧
    (cl11EquivMat (E00 cliffordWittAnnihilation cliffordWittCreation) =
      wittAnnihilationBase * wittCreationBase) ∧
    (cl11EquivMat (E01 cliffordWittAnnihilation cliffordWittCreation) =
      wittAnnihilationBase) ∧
    (cl11EquivMat (E10 cliffordWittAnnihilation cliffordWittCreation) =
      wittCreationBase) ∧
    (cl11EquivMat (E11 cliffordWittAnnihilation cliffordWittCreation) =
      wittCreationBase * wittAnnihilationBase) := by
  have hn := cliffordWittAnnihilation_sq
  have hp := cliffordWittCreation_sq
  have hcar := cliffordWitt_car
  have hpeirce := synthesis_stage0_to_stage1
    cliffordWittAnnihilation cliffordWittCreation hn hp hcar
  refine ⟨hpeirce.1, hpeirce.2.1, hpeirce.2.2.2.2.1,
    hpeirce.2.2.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [chevalley_E00_matrix, wittAnnihilation_mul_wittCreation_eq_matrixUnit]
  · exact chevalley_E01_matrix
  · exact chevalley_E10_matrix
  · rw [chevalley_E11_matrix, wittCreation_mul_wittAnnihilation_eq_matrixUnit]

end Cl11Instance

/-! ### 4. Synthesis Theorem 2 → 3: Multi-Mode CAR & Grassmannian Cooper Nilpotents -/

section Stage2to3

variable {R : Type*} [Ring R]

/-- Synthesis of Archetype 2 to 3:
Extending to multiple CAR modes, the product of even-degree idempotents commutes
identically, `[P₁, P₂] = 0`, yielding a composite vacuum `e₀ = P₁ P₂` that annihilates
all annihilation operators, while Cooper pair creation `Δ = p₁ p₂` is strictly nilpotent. -/
theorem synthesis_stage2_to_stage3 (M : TwoModeCAR R) :
    (P1 M * P2 M = P2 M * P1 M) ∧
    (e0_two M * e0_two M = e0_two M) ∧
    (M.n1 * e0_two M = 0) ∧
    (M.n2 * e0_two M = 0) ∧
    (e0_two M * M.p1 = 0) ∧
    (e0_two M * M.p2 = 0) ∧
    (superconductingPairing M * superconductingPairing M = 0) ∧
    ((M.p1 * M.p2 + M.n2 * M.n1) * e0_two M = (M.p1 * M.p2) * e0_two M) := by
  refine ⟨P1_comm_P2 M,
          e0_two_sq M,
          n1_mul_e0_two M,
          n2_mul_e0_two M,
          e0_two_mul_p1 M,
          e0_two_mul_p2 M,
          pairing_is_nilpotent M,
          bcs_pair_creation M⟩

end Stage2to3

/-! ### 5. Synthesis Theorem 3 → 4: Algebraic Doublet Rotation -/

section Stage3to4

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Synthesis of the algebraic doublet identities:
the operators named `tau3` and `tau1` define a hyperbolic rotation whose inverse and
preservation identities hold under the stated biproduct and hyperbola hypotheses.
This theorem does not assert a Krein inner product, adjoint, or positivity structure. -/
theorem synthesis_stage3_to_stage4 {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (c s : ℤ) (h_hyp : c * c - s * s = 1) :
    let U := bogoliubovRotation p1 i1 p2 i2 c s
    -- 1. Invertibility along the hyperbola
    (U ≫ bogoliubovRotation p1 i1 p2 i2 c (-s) = 𝟙 E) ∧
    -- 2. Preservation of the `tau3` endomorphism
    (U ≫ tau3 p1 i1 p2 i2 ≫ U = tau3 p1 i1 p2 i2) := by
  intro U
  dsimp [U]
  refine ⟨bogoliubov_rotation_inverse p1 i1 p2 i2 hid1 hid2 horth12 horth21 h_decomp c s h_hyp,
          bogoliubov_preserves_krein_metric p1 i1 p2 i2 hid1 hid2 horth12 horth21 h_decomp c s h_hyp⟩

end Stage3to4

/-! ### 6. Conditional Scalar Dispersion Identities -/

section Stage4to5

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Conditional scalar-dispersion theorem:
assuming an endomorphism `H` already satisfies `H² = m² 𝟙_E` and `μ m = 1`,
the normalized operator `ε = μ • H` squares to the identity and has the following
eigenvalue and annihilation identities. The terms `𝟙_E ± ε` are twice the usual
spectral idempotents; this theorem does not divide by `2` or derive the dispersion
relation from weak-value amplification. -/
theorem synthesis_stage4_to_stage5 {E : C}
    (H : E ⟶ E) (m μ : ℤ)
    (h_inv : μ * m = 1)
    (h_dispersion : H ≫ H = (m * m) • 𝟙 E) :
    ((μ • H) ≫ (μ • H) = 𝟙 E) ∧
    ((𝟙 E + μ • H) ≫ H = m • (𝟙 E + μ • H)) ∧
    ((𝟙 E - μ • H) ≫ H = - (m • (𝟙 E - μ • H))) ∧
    ((𝟙 E + μ • H) ≫ (𝟙 E - μ • H) = 0) ∧
    ((𝟙 E + μ • H) + (𝟙 E - μ • H) = (2 : ℤ) • 𝟙 E) := by
  refine ⟨normalized_bdg_is_split_involution H m μ h_inv h_dispersion,
          normalized_bdg_positive_sector_eigenvalue H m μ h_inv h_dispersion,
          normalized_bdg_negative_sector_eigenvalue H m μ h_inv h_dispersion,
          normalized_bdg_peirce_annihilation H m μ h_inv h_dispersion,
          normalized_bdg_peirce_partition H μ⟩

end Stage4to5

/-! ### 7. CAR–Nambu branch: the fourth-root identity -/

section CARNambuSynthesis

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The CAR data and the Nambu biproduct produce an exact operator identity:
the Chevalley grading is involutive, the doubled Hamiltonian square is the
off-diagonal grading block, and its fourth power is `-𝟙`. This is the CAR
branch of the prerequisite poset, distinct from the scalar-dispersion theorem
`synthesis_stage4_to_stage5`. -/
theorem synthesis_car_nambu_fourth_root {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (InfoGeometry.Physics.ChevalleyNambuBridge.chevalleyGrading D M ≫
        InfoGeometry.Physics.ChevalleyNambuBridge.chevalleyGrading D M = 𝟙 Ω) ∧
    (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M =
      p1 ≫ InfoGeometry.Physics.ChevalleyNambuBridge.chevalleyGrading D M ≫ i2 -
        p2 ≫ InfoGeometry.Physics.ChevalleyNambuBridge.chevalleyGrading D M ≫ i1) ∧
    ((bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) ≫
      (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) = -𝟙 E) := by
  exact ⟨InfoGeometry.Physics.ChevalleyNambuBridge.chevalleyGrading_sq
      D M hD hM hCAR,
    InfoGeometry.Physics.ChevalleyNambuBridge.carBdg_squared_eq_offdiagonal
      p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR,
    InfoGeometry.Physics.ChevalleyNambuBridge.carBdg_fourth_power_neg_identity
      p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR⟩

end CARNambuSynthesis

/-! ### 8. Nambu spinor holonomy -/

section NambuHolonomySynthesis

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The CAR-derived fourth-root identity yields the Nambu complex-structure
square and the eighth-power closure on the same doublet. The component
identities are proved by the CAR–Nambu and holonomy owners; this theorem records
their joint consequence under the common biproduct and CAR hypotheses. -/
theorem synthesis_car_nambu_holonomy {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    (nambuComplexStructure p1 i1 p2 i2 D M ≫
        nambuComplexStructure p1 i1 p2 i2 D M = -𝟙 E) ∧
    (((bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) ≫
        (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M)) ≫
      ((bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M) ≫
        (bdgHamiltonian p1 i1 p2 i2 D M ≫ bdgHamiltonian p1 i1 p2 i2 D M)) = 𝟙 E) := by
  exact ⟨nambuComplexStructure_sq p1 i1 p2 i2 D M hid1 hid2 horth12
      horth21 h_decomp hD hM hCAR,
    bdg_pow_eight p1 i1 p2 i2 D M hid1 hid2 horth12 horth21
      h_decomp hD hM hCAR⟩

end NambuHolonomySynthesis

/-! ### 9. LogCFT Symplectic Spinor and Jordan Shear Synthesis -/

section LogCFTSynthesis

variable {C : Type u} [Category.{v} C] [Preadditive C]

open InfoGeometry.Physics.ChevalleyDyads (E01)
open InfoGeometry.Physics.LogCFTSymplecticBridge

/-- Synthesis of Archetype LogCFT Jordan Shear from the Chevalley transition dyad:
the nilpotent element $E_{01}$ satisfies $E_{01}^2 = 0$ and induces the strictly invertible
unipotent shear $(\mathbb{1} + E_{01})(\mathbb{1} - E_{01}) = \mathbb{1}$. -/
theorem synthesis_chevalley_to_logcft_shear {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    unipotentShear (E01 n p) ≫ unipotentShearInv (E01 n p) = 𝟙 X :=
  chevalley_unipotent_shear_identity n p hn hcar

/-- Synthesis of Archetype LogCFT Symplectic Master:
unifies Nambu $\mathbb{Z}_4$-Maslov holonomy, $4\pi$ spinor holonomy, fermionic parity transmutation,
and LogCFT unipotent shear into a single sound system. -/
theorem synthesis_nambu_logcft_master {E Ω : C}
    (p1 : E ⟶ Ω) (i1 : Ω ⟶ E) (p2 : E ⟶ Ω) (i2 : Ω ⟶ E)
    (D M : Ω ⟶ Ω)
    (hid1 : i1 ≫ p1 = 𝟙 Ω) (hid2 : i2 ≫ p2 = 𝟙 Ω)
    (horth12 : i1 ≫ p2 = 0) (horth21 : i2 ≫ p1 = 0)
    (h_decomp : p1 ≫ i1 + p2 ≫ i2 = 𝟙 E)
    (hD : D ≫ D = 0) (hM : M ≫ M = 0)
    (hCAR : D ≫ M + M ≫ D = 𝟙 Ω) :
    let J := symplecticJ p1 i1 p2 i2 D M
    let P_plus := p1 ≫ i1
    let P_minus := p2 ≫ i2
    let H := bdgHamiltonian p1 i1 p2 i2 D M
    J ≫ J = -𝟙 E ∧
    (J ≫ J) ≫ (J ≫ J) = 𝟙 E ∧
    ((H ≫ H) ≫ (H ≫ H)) ≫ ((H ≫ H) ≫ (H ≫ H)) = 𝟙 E ∧
    (P_plus ≫ J ≫ P_minus) ≫ (P_minus ≫ J ≫ P_plus) = -P_plus ∧
    unipotentShear (E01 D M) ≫ unipotentShearInv (E01 D M) = 𝟙 Ω :=
  master_symplectic_spinor_soundness p1 i1 p2 i2 D M hid1 hid2 horth12 horth21 h_decomp hD hM hCAR

end LogCFTSynthesis

/-! ### 10. Master integration of the shared prerequisite poset -/

/-- Collects the selected prerequisite-order comparisons encoded in the causal-poset
owner. These comparisons establish the declared order only; they do not by themselves
derive the operator theorems, physical interpretations, or analytic consequences. -/
theorem master_causal_poset_soundness :
    (CanonicalArchetype.carNilpotentBase ≤ CanonicalArchetype.carPeirceInvolution) ∧
    (CanonicalArchetype.carPeirceInvolution ≤ CanonicalArchetype.chevalleySpinorDyad) ∧
    (CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.multiModeCAR) ∧
    (CanonicalArchetype.multiModeCAR ≤ CanonicalArchetype.kreinHyperbolicRotation) ∧
    (CanonicalArchetype.kreinHyperbolicRotation ≤ CanonicalArchetype.scalarBdGMassModel) ∧
    (CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.carNambuFourthRoot) ∧
    (CanonicalArchetype.carNambuFourthRoot ≤ CanonicalArchetype.nambuComplexStructure) ∧
    (CanonicalArchetype.nambuComplexStructure ≤ CanonicalArchetype.nambuSpinorHolonomy) ∧
    (CanonicalArchetype.chevalleySpinorDyad ≤ CanonicalArchetype.logCFTJordanShear) ∧
    (CanonicalArchetype.nambuSpinorHolonomy ≤ CanonicalArchetype.logCFTSymplecticMaster) ∧
    (CanonicalArchetype.logCFTJordanShear ≤ CanonicalArchetype.logCFTSymplecticMaster) ∧
    (CanonicalArchetype.noncommutativeOperatorRing ≤
      CanonicalArchetype.noncommutativeBdGBlocks) ∧
    (CanonicalArchetype.noncommutativeOperatorRing ≤
      CanonicalArchetype.noncommutativeZornMultiplication) ∧
    (CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornMatrixSliceEmbedding) ∧
    (CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornLeibnizDerivation) ∧
    (CanonicalArchetype.noncommutativeZornMultiplication ≤
      CanonicalArchetype.zornPairingActionFormula) ∧
    (CanonicalArchetype.noncommutativeBdGBlocks ≤
      CanonicalArchetype.zornBdGCurvatureReadout) ∧
    (CanonicalArchetype.zornMatrixSliceEmbedding ≤
      CanonicalArchetype.zornBdGCurvatureReadout) := by
  exact ⟨car_base_precedes_peirce,
    car_peirce_precedes_chevalley_dyad,
    chevalley_dyad_precedes_multimode_car,
    multimode_car_precedes_krein_rotation,
    krein_rotation_precedes_scalar_mass_model,
    chevalley_dyad_precedes_car_nambu,
    car_nambu_precedes_complex_structure,
    complex_structure_precedes_spinor_holonomy,
    chevalley_dyad_precedes_logcft_shear,
    spinor_holonomy_precedes_logcft_master,
    logcft_shear_precedes_logcft_master,
    noncommutative_ring_precedes_bdg_blocks,
    noncommutative_ring_precedes_zorn_multiplication,
    zorn_multiplication_precedes_matrix_slice,
    zorn_multiplication_precedes_leibniz_derivation,
    zorn_multiplication_precedes_pairing_formula,
    bdg_blocks_precede_zorn_curvature_readout,
    zorn_matrix_slice_precedes_curvature_readout⟩

end InfoGeometry.Physics.CanonicalSynthesis
