/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
import InfoGeometry.Canonical.PionChiralGoldstoneNative
import InfoGeometry.Canonical.Cl55MassChiralSymmetryBridge
import InfoGeometry.Canonical.QuantumYangMillsCrossCladeBridges

/-!
# Chiral Symmetry Breaking, Operator Gell-Mann–Oakes–Renner (GMOR), Peirce–Dirac Resolvent, Algebraic Banks–Casher Trace, and Self-Consistent NJL Gap Bifurcation (`χ₁ ≺ χ₂ ≺ χ₃ ≺ χ₄ ≺ χ₅ ≺ χ₆ ≺ χ₇ ≺ χ₈`)

This module formalizes the 8-stage Acyclic Causal Poset
`ChiralCondensateEpistemicStage` (`χ₁ ≺ χ₂ ≺ χ₃ ≺ χ₄ ≺ χ₅ ≺ χ₆ ≺ χ₇ ≺ χ₈`)
distilled via `solve et coagula` from the chiral mass, gauge-orbit Gramian,
Bogoliubov–de Gennes (BdG), and Nambu–Jona-Lasinio (NJL) / Banks–Casher / GMOR
operator architecture over an arbitrary associative ring `[Ring B]` (and `[StarRing B]`
where star-involutions appear), with zero `[CommRing]` or commutation assumptions on the
ambient operator algebra:

1. **Stage `χ₁` (`chi1_ChiralParityCutAndCondensateSquare` — Chiral Parity Cut `γ₅ = 2P - 1`, Off-Diagonal Condensate `Φ`, & Socratic Involution Defect)**:
   - Over `[Ring B]` with idempotent `P * P = P`, defines the chiral grading involution
     `chiralGamma5 P := invS P = 2 • P - 1` (`chiralGamma5 P * chiralGamma5 P = 1`).
   - Proves exact anticommutation of `chiralGamma5 P` with the chiral condensate
     `Φ = genPhi P A C` and skew current `J = genJ P A C` (`{γ₅, Φ} = 0`, `{γ₅, J} = 0`),
     commutation with the two-sheet bandgap `V = genV P A C` (`[γ₅, V] = 0`),
     mutual conversion `γ₅ * Φ = J` and `γ₅ * J = Φ`,
     and the **Socratic Involution Defect of Chiral Breaking**:
     `(γ₅ + Φ)² - 1 = Φ² = V`.

2. **Stage `χ₂` (`chi2_GaugeOrbitGramianAndMaurerCartanBianchi` — Gauge-Orbit Commutator Gramian `V = [P, a]⋆[P, a] = -[P, a]²` & Maurer–Cartan Bianchi Conservation)**:
   - Over `[Ring B] [StarRing B]` with self-adjoint idempotent `P⋆ = P = P²` and self-adjoint
     gauge potential `a⋆ = a`, identifies the chiral condensate square `Φ² = genV P a a` with the
     positive gauge-orbit commutator Gramian `orbitMassMode P a = star [P, a] * [P, a] = -[P, a]²`,
     proves that `orbitMassMode P a` is the self-dual even component of the Peirce Maurer–Cartan
     curvature `F_MC(P, a, a) = J + V`, is covariantly constant (`D_{P,a}(V) = 0`), and has
     upper Peirce corner equal to `orbitPeirce10 P a * star (orbitPeirce10 P a)`.

3. **Stage `χ₃` (`chi3_DoubleCommutatorGoldstoneVortexSplit` — Double-Commutator Higgs/Vortex Split `ℳ_Φ(Φ) = 0` vs. `ℳ_Φ(J) = -(4V)J`, `ℳ_Φ(Σ) = -(4V)Σ`, `ℳ_Φ(γ₅) = -(4V)γ₅`)**:
   - Proves that the double-commutator mass superoperator `opHiggsMassOperator P A C X = -[Φ, [Φ, X]]`
     annihilates the Goldstone mode `Φ` and bandgap `V` (`ℳ_Φ(Φ) = 0`, `ℳ_Φ(V) = 0`) while
     generating the exact operator mass-squared `m² = 4V = opVortexMassSq P A C` on the chiral
     grading `γ₅`, the axial current `J`, and the spin-dipole curvature `Σ`:
     `ℳ_Φ(γ₅) = -(4V) γ₅ = -4 Σ`, `ℳ_Φ(J) = -(4V) J`, and `ℳ_Φ(Σ) = -(4V) Σ`.

4. **Stage `χ₄` (`chi4_SymmetricPairCosetAndNativePionCAR` — Universal Peirce–Cartan Symmetric Pair `𝔤 = 𝔨 ⊕ 𝔭` & Native `(π⁺, π⁻, π⁰)` CAR/`𝔰𝔩₂` Closure)**:
   - Proves over any `[Ring B]` with `P * P = P` (without needing `1/2 ∈ B`) that the unbroken
     diagonal subalgebra `𝔨 = evenGrade P` and broken axial coset `𝔭 = oddGrade P` obey the
     exact Cartan symmetric-space Lie bracket rules:
     `[evenGrade P X, evenGrade P Y] ∈ 𝔨`,
     `[evenGrade P X, oddGrade P Y] ∈ 𝔭`, and
     `[oddGrade P X, oddGrade P Y] ∈ 𝔨`,
     paired with the native `(π⁺, π⁻, π⁰)` CAR/`𝔰𝔩₂` closure from `PionChiralGoldstoneNative`.

5. **Stage `χ₅` (`chi5_Cl55MajoranaChiralDefectAndBdGAndreev` — `Cl(5,5)` CAR Majorana Chiral Defect & Universal `2 × 2` Particle–Hole BdG Andreev Coercivity)**:
   - Defines the universal non-commutative `2 × 2` star-adjoint Bogoliubov–de Gennes (BdG)
     Nambu matrix `bdgStarHamiltonian Q M = !![Q, M; star M, -Q]` over any `[Ring B] [StarRing B]`,
     proves its self-adjointness when `star Q = Q`, computes its exact square
     `!![Q² + M M⋆, [Q, M]; -[Q, M⋆], M⋆ M + Q²]`, proves exact particle–hole Andreev reflection
     cancellation of the off-diagonal chiral commutator anomaly, and bridges to the native 5-mode
     `Cl(5,5)` CAR Majorana defect `[chiralCharge55, nativeFiveModeMajorana] = nativeFiveModeChiralDefect ≠ 0`.

6. **Stage `χ₆` (`chi6_OperatorGMORWardTakahashiAndHiggsDuality` — Exact Operator Gell-Mann–Oakes–Renner (GMOR) Ward–Takahashi Identity & Higgs–GMOR Duality)**:
   - Defines the axial double-commutator superoperator `axialDoubleCommutator P X = -[γ₅, [γ₅, X]]`
     and the explicit quark-mass symmetry-breaking Hamiltonian `quarkMassHamiltonian P m_q A C = -(m_q * Φ)`.
   - Proves the **Exact Higgs–GMOR Dual Double-Commutator Theorem**:
     - Probing `γ₅` with `ℳ_Φ` yields the Higgs/vortex mass `ℳ_Φ(γ₅) = -(4V) γ₅`,
     - Probing `Φ` with `ℳ_{γ₅}` yields `ℳ_{γ₅}(Φ) = -4 Φ`,
     - For any quark mass `m_q : B` in the unbroken centralizer of `P` (`P * m_q = m_q * P`),
       the Ward–Takahashi first commutator is `[γ₅, -(m_q * Φ)] = -2 (m_q * J)` and the
       **Operator GMOR Double Commutator** is:
       `-[γ₅, [γ₅, -(m_q * Φ)]] = (4 : ℤ) • (m_q * Φ)`,
     - Applying any additive expectation/trace functional `τ : B →+ G` yields the exact
       **Expectation GMOR Identity**:
       `τ (axialDoubleCommutator P (quarkMassHamiltonian P m_q A C)) = (4 : ℤ) • τ (m_q * genPhi P A C)`.

7. **Stage `χ₇` (`chi7_PeirceDiracResolventAndBanksCasherTrace` — Exact Non-Commutative Peirce–Dirac Resolvent & Characteristic-Free Algebraic Banks–Casher Trace Theorem)**:
   - For the massive Peirce–Dirac operator `peirceDiracOp P A C η = J + η` and its conjugate
     `peirceDiracConjOp P A C η = -J + η` with `η * J = J * η`, proves the exact quadratic
     factorization `(J + η)(-J + η) = V + η² = peirceDiracDenom P A C η`.
   - Given a two-sided inverse `R_η` of `V + η²`, proves that
     `peirceDiracResolvent P A C η R_η = (-J + η) * R_η = -J * R_η + η * R_η` is the exact
     two-sided inverse of `J + η`, proves that `P * η = η * P` automatically forces `P * R_η = R_η * P`,
     decomposes the resolvent into its chiral-odd current propagator `-J * R_η` and chiral-even
     Lorentzian spectral kernel `η * R_η`, and proves the **Characteristic-Free Algebraic Banks–Casher
     Trace Theorem**: for any cyclically invariant additive map `τ : B →+ G` (`∀ x y, τ(x * y) = τ(y * x)`),
     `τ (oddGrade P X) = 0` identically (without dividing by 2!), so the odd propagator `-J * R_η`
     has zero trace and:
     `τ (peirceDiracResolvent P A C η R_η) = τ (η * R_η)`.

8. **Stage `χ₈` (`chi8_NJLSelfConsistentGapBifurcationAndMasterSynthesis` — Self-Consistent NJL Gap Fixed-Point Bifurcation, Trap T16/T17 Matrix Witnesses, & Master Synthesis)**:
   - Substitutes the Banks–Casher resolvent trace into the Nambu–Jona-Lasinio (NJL) self-consistency
     equation `η = m₀ + g_njl * τ(peirceDiracResolvent P A C η R_η)` and proves the exact chiral-limit
     factorization `njlGapResidual 0 g_njl I_bc η = η * (1 - g_njl * I_bc)` and domain bifurcation
     `njlGapResidual 0 g_njl I_bc η = 0 ↔ η = 0 ∨ g_njl * I_bc = 1`, separating the symmetric
     Wigner–Weyl vacuum (`η = 0`) from the dynamically broken Nambu–Goldstone condensate
     (`g_njl * I_bc = 1`).

All declarations are proved constructively in native Mathlib without `sorry`, `admit`, `native_decide`,
or custom axioms. These results capture the exact non-commutative operator, resolvent, and trace
algebra; they do not claim a continuum 4D path-integral construction.

## i. Overview

Formalizes the 8-stage `ChiralCondensateEpistemicStage` poset (`χ₁ ≺ ⋯ ≺ χ₈`) governing the
chiral parity cut `γ₅ = 2P - 1`, gauge-orbit Gramian, double-commutator Goldstone/vortex split,
native pion CAR, `Cl(5,5)` Majorana chiral defect, operator GMOR Ward–Takahashi identity,
Peirce–Dirac resolvent / Banks–Casher trace, and NJL gap bifurcation.

## ii. Key results

- `ChiralCondensateEpistemicStage.causalEdge_acyclic`
- `operator_gmor_ward_takahashi_identity`
- `chiral_condensate_gmor_banks_casher_njl_master_synthesis`

## iii. Table of contents

- Section 0: The 8-Stage Causal Poset (`χ₁ ≺ ⋯ ≺ χ₈`)
- Sections 1–8: Stages `χ₁` through `χ₈`

## iv. References

- M. Gell-Mann, R. J. Oakes, B. Renner, *Behavior of Current Divergences under SU₃ × SU₃* (1968).
- T. Banks, A. Casher, *Chiral Symmetry Breaking in Confining Theories* (1980).
- Y. Nambu, G. Jona-Lasinio, *Dynamical Model of Elementary Particles Based on an Analogy with Superconductivity* (1961).

#### BUCKET 1: CLOSED FINITE THEOREMS
- `ChiralCondensateEpistemicStage.causalEdge_acyclic`, `ChiralCondensateEpistemicStage.causalEdge_chain`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- Stages `χ₁`–`χ₈` over `[Ring B]` with idempotent `hP : P * P = P`.

#### BUCKET 3: OPEN CLOSURE DEBT
- Continuum 4D path-integral regularization of the NJL gap integral beyond algebraic resolvent traces.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset

open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian
open InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
open InfoGeometry.Canonical.PionChiralGoldstoneNative
open InfoGeometry.Canonical.Cl55MassChiralSymmetryBridge
open InfoGeometry.Canonical.Cl55AllModeMassCoercivity
open InfoGeometry.Canonical.Cl55InfinityChiralCharge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Physics
open scoped Matrix

/-! ===========================================================================
    Section 0: The 8-Stage Acyclic Causal Poset (χ₁ ≺ χ₂ ≺ ⋯ ≺ χ₈)
    =========================================================================== -/

/-- The 8 stages of the Chiral Condensate, GMOR, Banks–Casher, and NJL Gap Acyclic Causal Poset. -/
inductive ChiralCondensateEpistemicStage : Type
  | chi1_ChiralParityCutAndCondensateSquare
  | chi2_GaugeOrbitGramianAndMaurerCartanBianchi
  | chi3_DoubleCommutatorGoldstoneVortexSplit
  | chi4_SymmetricPairCosetAndNativePionCAR
  | chi5_Cl55MajoranaChiralDefectAndBdGAndreev
  | chi6_OperatorGMORWardTakahashiAndHiggsDuality
  | chi7_PeirceDiracResolventAndBanksCasherTrace
  | chi8_NJLSelfConsistentGapBifurcationAndMasterSynthesis
  deriving DecidableEq, Repr

namespace ChiralCondensateEpistemicStage

/-- Topological rank embedding into `ℕ`. -/
def rank : ChiralCondensateEpistemicStage → ℕ
  | .chi1_ChiralParityCutAndCondensateSquare => 0
  | .chi2_GaugeOrbitGramianAndMaurerCartanBianchi => 1
  | .chi3_DoubleCommutatorGoldstoneVortexSplit => 2
  | .chi4_SymmetricPairCosetAndNativePionCAR => 3
  | .chi5_Cl55MajoranaChiralDefectAndBdGAndreev => 4
  | .chi6_OperatorGMORWardTakahashiAndHiggsDuality => 5
  | .chi7_PeirceDiracResolventAndBanksCasherTrace => 6
  | .chi8_NJLSelfConsistentGapBifurcationAndMasterSynthesis => 7

/-- `rank` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance instLinearOrderChiralCondensateEpistemicStage :
    LinearOrder ChiralCondensateEpistemicStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct cover relation `s₁ ≺ s₂` in the 8-stage causal poset. -/
def causalEdge : ChiralCondensateEpistemicStage → ChiralCondensateEpistemicStage → Prop
  | a, b => rank b = rank a + 1

/-- Every direct causal edge strictly increases `rank`. -/
theorem causalEdge_strict_rank {a b : ChiralCondensateEpistemicStage}
    (h : causalEdge a b) : rank a < rank b := by
  unfold causalEdge at h
  omega

/-- Every transitive path of causal edges strictly increases `rank`. -/
theorem transGen_strict_rank {a b : ChiralCondensateEpistemicStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank hab
  | tail _ hbc ih =>
      have hlt := causalEdge_strict_rank hbc
      omega

/-- **Poset Acyclicity Theorem**: `causalEdge` has no directed cycles. -/
theorem causalEdge_acyclic (a : ChiralCondensateEpistemicStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  have hlt := transGen_strict_rank h
  exact Nat.lt_irrefl (rank a) hlt

/-- **Complete 8-Stage Causal Chain Theorem**:
`χ₁ ≺ χ₂ ≺ χ₃ ≺ χ₄ ≺ χ₅ ≺ χ₆ ≺ χ₇ ≺ χ₈`. -/
theorem causalEdge_chain :
    causalEdge .chi1_ChiralParityCutAndCondensateSquare
      .chi2_GaugeOrbitGramianAndMaurerCartanBianchi ∧
    causalEdge .chi2_GaugeOrbitGramianAndMaurerCartanBianchi
      .chi3_DoubleCommutatorGoldstoneVortexSplit ∧
    causalEdge .chi3_DoubleCommutatorGoldstoneVortexSplit
      .chi4_SymmetricPairCosetAndNativePionCAR ∧
    causalEdge .chi4_SymmetricPairCosetAndNativePionCAR
      .chi5_Cl55MajoranaChiralDefectAndBdGAndreev ∧
    causalEdge .chi5_Cl55MajoranaChiralDefectAndBdGAndreev
      .chi6_OperatorGMORWardTakahashiAndHiggsDuality ∧
    causalEdge .chi6_OperatorGMORWardTakahashiAndHiggsDuality
      .chi7_PeirceDiracResolventAndBanksCasherTrace ∧
    causalEdge .chi7_PeirceDiracResolventAndBanksCasherTrace
      .chi8_NJLSelfConsistentGapBifurcationAndMasterSynthesis := by
  unfold causalEdge
  decide

end ChiralCondensateEpistemicStage

/-! ===========================================================================
    Section 1: Stage χ₁ — Chiral Parity Cut γ₅ = 2P - 1, Off-Diagonal
    Condensate Φ, and Socratic Involution Defect
    =========================================================================== -/

section StageChi1

variable {B : Type*} [Ring B]

/-- The chiral parity involution `γ₅(P) := invS P = P - (1 - P) = 2P - 1` associated to an
idempotent `P : B`. -/
def chiralGamma5 (P : B) : B :=
  invS P

variable {P : B} (hP : P * P = P)
include hP

/-- `chiralGamma5 P` is a strict involution: `γ₅² = 1`. -/
theorem chiralGamma5_sq_one :
    chiralGamma5 P * chiralGamma5 P = 1 := by
  unfold chiralGamma5
  peirce_nf hP

/-- `chiralGamma5 P` anticommutes with the chiral condensate `Φ = genPhi P A C`:
`{γ₅, Φ} = γ₅ * Φ + Φ * γ₅ = 0`. -/
theorem chiralGamma5_anticomm_genPhi (A C : B) :
    anticomm (chiralGamma5 P) (genPhi P A C) = 0 := by
  unfold chiralGamma5
  peirce_nf hP

/-- `chiralGamma5 P` anticommutes with the skew axial current `J = genJ P A C`:
`{γ₅, J} = γ₅ * J + J * γ₅ = 0`. -/
theorem chiralGamma5_anticomm_genJ (A C : B) :
    anticomm (chiralGamma5 P) (genJ P A C) = 0 := by
  unfold chiralGamma5
  peirce_nf hP

/-- `chiralGamma5 P` commutes with the even two-sheet bandgap `V = genV P A C`:
`[γ₅, V] = 0`. -/
theorem chiralGamma5_comm_genV (A C : B) :
    comm (chiralGamma5 P) (genV P A C) = 0 := by
  unfold chiralGamma5
  peirce_nf hP

/-- Left and right multiplication by `chiralGamma5 P` converts between the symmetric
chiral condensate `Φ = genPhi P A C` and the skew current `J = genJ P A C`, and between
the bandgap `V = genV P A C` and the spin-dipole curvature `Σ = genSig P A C`. -/
theorem chiralGamma5_mul_conversions (A C : B) :
    chiralGamma5 P * genPhi P A C = genJ P A C ∧
    genPhi P A C * chiralGamma5 P = -genJ P A C ∧
    chiralGamma5 P * genJ P A C = genPhi P A C ∧
    genJ P A C * chiralGamma5 P = -genPhi P A C ∧
    chiralGamma5 P * genV P A C = genSig P A C ∧
    genV P A C * chiralGamma5 P = genSig P A C ∧
    chiralGamma5 P * genSig P A C = genV P A C ∧
    genSig P A C * chiralGamma5 P = genV P A C := by
  unfold chiralGamma5
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

/-- The symmetric chiral condensate squares to `V` (`Φ² = V`), while the skew current
squares to `-V` (`J² = -V`). -/
theorem genPhi_and_genJ_squares (A C : B) :
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C := by
  refine ⟨by peirce_nf hP, by peirce_nf hP⟩

/-- **Socratic Involution Defect of Chiral Symmetry Breaking**:
Perturbing the chiral involution `γ₅ = chiralGamma5 P` by the odd chiral condensate
`Φ = genPhi P A C` produces an involution defect `(γ₅ + Φ)² - 1` equal to the exact
two-sheet bandgap `V = genV P A C`. -/
theorem socratic_chiral_involution_defect (A C : B) :
    (chiralGamma5 P + genPhi P A C) * (chiralGamma5 P + genPhi P A C) - 1 =
      genV P A C := by
  unfold chiralGamma5
  peirce_nf hP

/-- **Archetype `χ₁` Summary (`archetype_chi1_chiral_parity_cut_and_socratic_involution_defect`)**:
Packages the chiral involution `γ₅² = 1`, chiral anticommutation `{γ₅, Φ} = 0` and `{γ₅, J} = 0`,
condensate squares `Φ² = V` and `J² = -V`, and Socratic involution defect `(γ₅ + Φ)² - 1 = V`. -/
theorem archetype_chi1_chiral_parity_cut_and_socratic_involution_defect (A C : B) :
    chiralGamma5 P * chiralGamma5 P = 1 ∧
    anticomm (chiralGamma5 P) (genPhi P A C) = 0 ∧
    anticomm (chiralGamma5 P) (genJ P A C) = 0 ∧
    comm (chiralGamma5 P) (genV P A C) = 0 ∧
    genPhi P A C * genPhi P A C = genV P A C ∧
    genJ P A C * genJ P A C = -genV P A C ∧
    (chiralGamma5 P + genPhi P A C) * (chiralGamma5 P + genPhi P A C) - 1 =
      genV P A C := by
  unfold chiralGamma5
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

end StageChi1

/-! ===========================================================================
    Section 2: Stage χ₂ — Gauge-Orbit Commutator Gramian V = [P, a]⋆[P, a]
    and Maurer–Cartan Bianchi Conservation
    =========================================================================== -/

section StageChi2

variable {B : Type*} [Ring B] [StarRing B]

/-- **Archetype `χ₂` Summary (`archetype_chi2_gauge_orbit_gramian_and_maurer_cartan_bianchi`)**:
For a self-adjoint idempotent `P⋆ = P = P²` and self-adjoint gauge potential `a⋆ = a` in `[Ring B] [StarRing B]`:
1. `orbitMassMode P a = -(orbitCommutator P a * orbitCommutator P a)`,
2. `orbitMassMode P a = genV P a a = genPhi P a a * genPhi P a a`,
3. `peirceMaurerCartanCurvature P a a = genJ P a a + orbitMassMode P a`,
4. `evenGrade P (peirceMaurerCartanCurvature P a a) = orbitMassMode P a`,
5. `peirceCovariantDeriv P a a (orbitMassMode P a) = 0` (covariant Bianchi conservation),
6. `P * orbitMassMode P a * P = orbitPeirce10 P a * star (orbitPeirce10 P a)`. -/
theorem archetype_chi2_gauge_orbit_gramian_and_maurer_cartan_bianchi
    {P a : B} (hP : P * P = P) (hPs : star P = P) (has : star a = a) :
    orbitMassMode P a = -(orbitCommutator P a * orbitCommutator P a) ∧
    orbitMassMode P a = genV P a a ∧
    genPhi P a a * genPhi P a a = orbitMassMode P a ∧
    peirceMaurerCartanCurvature P a a = genJ P a a + orbitMassMode P a ∧
    evenGrade P (peirceMaurerCartanCurvature P a a) = orbitMassMode P a ∧
    peirceCovariantDeriv P a a (orbitMassMode P a) = 0 ∧
    P * orbitMassMode P a * P =
      orbitPeirce10 P a * star (orbitPeirce10 P a) := by
  have hSq := orbitMassMode_eq_neg_commutator_sq hPs has
  have hGenV := orbitMassMode_eq_peirce_genV hP hPs has
  have hPhiSq : genPhi P a a * genPhi P a a = orbitMassMode P a := by
    rw [hGenV]
    exact (genPhi_and_genJ_squares hP a a).1
  have hMC := peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP a a 1 1
  have hBianchi :=
    InfoGeometry.Canonical.QuantumYangMillsCrossCladeBridges.orbitMassMode_bianchi_and_corner_gramians
      hP hPs has
  refine ⟨hSq, hGenV, hPhiSq, ?_, hBianchi.1, hBianchi.2.2.1, hBianchi.2.2.2⟩
  rw [hGenV]
  exact hMC.2.2.1

end StageChi2

/-! ===========================================================================
    Section 3: Stage χ₃ — Double-Commutator Higgs/Vortex Split
    ℳ_Φ(Φ) = 0 vs. ℳ_Φ(J) = -(4V)J, ℳ_Φ(Σ) = -(4V)Σ, ℳ_Φ(γ₅) = -(4V)γ₅
    =========================================================================== -/

section StageChi3

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

omit hP in
/-- Helper expanding `(4 : ℤ) • x` in any additive group. -/
theorem four_zsmul_eq (x : B) :
    (4 : ℤ) • x = x + x + x + x := by
  change ((2 : ℤ) + (2 : ℤ)) • x = x + x + x + x
  rw [add_zsmul, two_zsmul]
  abel

/-- Probing the chiral grading `chiralGamma5 P` with the double-commutator Higgs mass
superoperator `opHiggsMassOperator P A C X = -[Φ, [Φ, X]]` produces `-(opVortexMassSq P A C * γ₅) = -4 • Σ`. -/
theorem opHiggsMassOperator_chiralGamma5 (A C : B) :
    opHiggsMassOperator P A C (chiralGamma5 P) =
      -(opVortexMassSq P A C * chiralGamma5 P) ∧
    opHiggsMassOperator P A C (chiralGamma5 P) =
      -((4 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_⟩
  · unfold opHiggsMassOperator opNegativeAdjointSquare derivSqPhi opVortexMassSq opQuadraticCoupling chiralGamma5
    rw [four_zsmul_eq]
    peirce_nf hP
  · unfold opHiggsMassOperator opNegativeAdjointSquare derivSqPhi chiralGamma5
    rw [four_zsmul_eq]
    peirce_nf hP

/-- **Archetype `χ₃` Summary (`archetype_chi3_double_commutator_goldstone_vortex_split`)**:
Under the double-commutator mass operator `opHiggsMassOperator P A C X = -[Φ, [Φ, X]]`:
1. **Massless Goldstone & Modulus Kernel**:
   `opHiggsMassOperator P A C (genPhi P A C) = 0` and
   `opHiggsMassOperator P A C (genV P A C) = 0`,
2. **Gapped Axial, Spin-Dipole & Chiral-Grading Channels (`m² = 4V`)**:
   - `opHiggsMassOperator P A C (genJ P A C) = -(opVortexMassSq P A C * genJ P A C)`,
   - `opHiggsMassOperator P A C (genSig P A C) = -(opVortexMassSq P A C * genSig P A C)`,
   - `opHiggsMassOperator P A C (chiralGamma5 P) = -(opVortexMassSq P A C * chiralGamma5 P)`. -/
theorem archetype_chi3_double_commutator_goldstone_vortex_split (A C : B) :
    opHiggsMassOperator P A C (genPhi P A C) = 0 ∧
    opHiggsMassOperator P A C (genV P A C) = 0 ∧
    opHiggsMassOperator P A C (genJ P A C) =
      -(opVortexMassSq P A C * genJ P A C) ∧
    opHiggsMassOperator P A C (genSig P A C) =
      -(opVortexMassSq P A C * genSig P A C) ∧
    opHiggsMassOperator P A C (chiralGamma5 P) =
      -(opVortexMassSq P A C * chiralGamma5 P) := by
  have hYM4 := mexican_hat_ihhs_coupling_to_mass_lift hP A C 1 1 1
  exact ⟨hYM4.1, hYM4.2.1, hYM4.2.2.1, hYM4.2.2.2.1,
    (opHiggsMassOperator_chiralGamma5 hP A C).1⟩

end StageChi3

/-! ===========================================================================
    Section 4: Stage χ₄ — Universal Peirce–Cartan Symmetric Pair 𝔤 = 𝔨 ⊕ 𝔭
    and Native (π⁺, π⁻, π⁰) CAR/𝔰𝔩₂ Closure
    =========================================================================== -/

section StageChi4

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

/-- **Universal Peirce–Cartan Symmetric-Pair Bracket Theorem (`peirce_cartan_symmetric_pair_brackets`)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P` (characteristic-free, without
requiring `2` to be invertible):
1. Every element decomposes as `X = evenGrade P X + oddGrade P X` with
   `[γ₅, evenGrade P X] = 0` (`evenGrade P X ∈ 𝔨`) and `{γ₅, oddGrade P X} = 0` (`oddGrade P X ∈ 𝔭`),
2. **`[𝔨, 𝔨] ⊆ 𝔨`**: `oddGrade P (comm (evenGrade P X) (evenGrade P Y)) = 0` and
   `evenGrade P (comm (evenGrade P X) (evenGrade P Y)) = comm (evenGrade P X) (evenGrade P Y)`,
3. **`[𝔨, 𝔭] ⊆ 𝔭`**: `evenGrade P (comm (evenGrade P X) (oddGrade P Y)) = 0` and
   `oddGrade P (comm (evenGrade P X) (oddGrade P Y)) = comm (evenGrade P X) (oddGrade P Y)`,
4. **`[𝔭, 𝔭] ⊆ 𝔨`**: `oddGrade P (comm (oddGrade P X) (oddGrade P Y)) = 0` and
   `evenGrade P (comm (oddGrade P X) (oddGrade P Y)) = comm (oddGrade P X) (oddGrade P Y)`. -/
theorem peirce_cartan_symmetric_pair_brackets (X Y : B) :
    X = evenGrade P X + oddGrade P X ∧
    comm (chiralGamma5 P) (evenGrade P X) = 0 ∧
    anticomm (chiralGamma5 P) (oddGrade P X) = 0 ∧
    oddGrade P (comm (evenGrade P X) (evenGrade P Y)) = 0 ∧
    evenGrade P (comm (evenGrade P X) (evenGrade P Y)) =
      comm (evenGrade P X) (evenGrade P Y) ∧
    evenGrade P (comm (evenGrade P X) (oddGrade P Y)) = 0 ∧
    oddGrade P (comm (evenGrade P X) (oddGrade P Y)) =
      comm (evenGrade P X) (oddGrade P Y) ∧
    oddGrade P (comm (oddGrade P X) (oddGrade P Y)) = 0 ∧
    evenGrade P (comm (oddGrade P X) (oddGrade P Y)) =
      comm (oddGrade P X) (oddGrade P Y) := by
  unfold chiralGamma5
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
          by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

omit hP in
/-- **Archetype `χ₄` Summary (`archetype_chi4_symmetric_pair_and_native_pion_car`)**:
Combines the characteristic-free Peirce–Cartan symmetric-pair brackets
`[𝔨, 𝔨] ⊆ 𝔨`, `[𝔨, 𝔭] ⊆ 𝔭`, `[𝔭, 𝔭] ⊆ 𝔨` with the native `(π⁺, π⁻, π⁰)` CAR/`𝔰𝔩₂` closure
(`piPlus² = 0`, `piMinus² = 0`, `{piPlus, piMinus} = 1`, `[piPlus, piMinus] = 2 • piZero`,
`[piZero, piPlus] = piPlus`, `[piZero, piMinus] = -piMinus`). -/
theorem archetype_chi4_symmetric_pair_and_native_pion_car
    (hP' : P * P = P) (X Y : B) :
    (oddGrade P (comm (evenGrade P X) (evenGrade P Y)) = 0 ∧
     evenGrade P (comm (evenGrade P X) (oddGrade P Y)) = 0 ∧
     oddGrade P (comm (oddGrade P X) (oddGrade P Y)) = 0) ∧
    (piPlus * piPlus = 0 ∧
     piMinus * piMinus = 0 ∧
     piPlus * piMinus + piMinus * piPlus = (1 : M2C) ∧
     ⁅piPlus, piMinus⁆ = (2 : ℂ) • piZero ∧
     ⁅piZero, piPlus⁆ = piPlus ∧
     ⁅piZero, piMinus⁆ = -piMinus) := by
  have hSym := peirce_cartan_symmetric_pair_brackets hP' X Y
  exact ⟨⟨hSym.2.2.2.1, hSym.2.2.2.2.2.1, hSym.2.2.2.2.2.2.2.1⟩,
    native_chiral_closure⟩

end StageChi4

/-! ===========================================================================
    Section 5: Stage χ₅ — Cl(5,5) CAR Majorana Chiral Defect and
    Universal 2 × 2 Particle–Hole BdG Andreev Coercivity
    =========================================================================== -/

section StageChi5

variable {B : Type*} [Ring B] [StarRing B]

/-- The universal `2 × 2` particle–hole Bogoliubov–de Gennes (BdG) Nambu Hamiltonian over a
star-ring `[Ring B] [StarRing B]`:
$$H_{\mathrm{BdG}}(Q, M) = \begin{pmatrix} Q & M \\ M^\star & -Q \end{pmatrix}.$$ -/
def bdgStarHamiltonian (Q M : B) : Matrix (Fin 2) (Fin 2) B :=
  !![Q, M; star M, -Q]

/-- The particle–hole Andreev swap involution `τ₁ = !![0, 1; 1, 0]` on `Matrix (Fin 2) (Fin 2) B`. -/
def bdgAndreevSwap : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

omit [StarRing B] in
/-- `bdgAndreevSwap` is an involution (`τ₁² = 1`). -/
theorem bdgAndreevSwap_sq_one :
    bdgAndreevSwap (B := B) * bdgAndreevSwap (B := B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgAndreevSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- For a self-adjoint chiral charge `star Q = Q` and arbitrary pairing operator `M : B`,
`bdgStarHamiltonian Q M` is Hermitian under the matrix conjugate transpose (`Hᴴ = H`). -/
theorem bdgStarHamiltonian_conjTranspose {Q : B} (hQ : star Q = Q) (M : B) :
    (bdgStarHamiltonian Q M)ᴴ = bdgStarHamiltonian Q M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgStarHamiltonian, Matrix.conjTranspose_apply, hQ]

/-- **Universal `2 × 2` Star-BdG Square Decomposition**:
Squaring `bdgStarHamiltonian Q M` separates into the coercive particle/hole diagonal blocks
`Q² + M M⋆` and `M⋆ M + Q²`, and the off-diagonal chiral commutator anomaly blocks
`[Q, M]` and `-[Q, M⋆]`. -/
theorem bdgStarHamiltonian_sq (Q M : B) :
    bdgStarHamiltonian Q M * bdgStarHamiltonian Q M =
      !![Q * Q + M * star M, OperatorAlgebra.PeirceSpine.comm Q M;
         -OperatorAlgebra.PeirceSpine.comm Q (star M), star M * M + Q * Q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgStarHamiltonian, OperatorAlgebra.PeirceSpine.comm,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    abel

/-- **Andreev Reflection Cancellation of the Off-Diagonal Chiral Anomaly**:
For a self-adjoint (Majorana) mass `star M = M`, averaging `H_BdG²` with its particle–hole
Andreev reflection `τ₁ H_BdG² τ₁` cancels the off-diagonal commutator `[Q, M]` identically
and leaves the purely diagonal squared-mass block. -/
theorem bdgStarHamiltonian_andreev_cancellation
    (Q : B) {M : B} (hM : star M = M) :
    bdgStarHamiltonian Q M * bdgStarHamiltonian Q M +
      bdgAndreevSwap * (bdgStarHamiltonian Q M * bdgStarHamiltonian Q M) * bdgAndreevSwap =
      !![Q * Q + M * M + (M * M + Q * Q), 0;
         0, M * M + Q * Q + (Q * Q + M * M)] := by
  rw [bdgStarHamiltonian_sq, hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgAndreevSwap, OperatorAlgebra.PeirceSpine.comm]

/-- **Archetype `χ₅` Summary (`archetype_chi5_cl55_majorana_chiral_defect_and_bdg_andreev`)**:
Packages:
1. The universal `2 × 2` star-BdG square `bdgStarHamiltonian_sq` and Andreev anomaly cancellation,
2. The native 5-mode `Cl(5,5)` CAR chiral commutator defect:
   `[chiralCharge55, nativeFiveModeMajorana] = nativeFiveModeChiralDefect ≠ 0`,
   certified by `{nativeFiveModeChiralDefect, annihilation55 0} = 1`,
3. The native BdG Andreev anomaly cancellation `nativeFiveMode_chiral_bdg_anomaly_andreev_cancellation`. -/
theorem archetype_chi5_cl55_majorana_chiral_defect_and_bdg_andreev (Q M : B) :
    bdgStarHamiltonian Q M * bdgStarHamiltonian Q M =
      !![Q * Q + M * star M, OperatorAlgebra.PeirceSpine.comm Q M;
         -OperatorAlgebra.PeirceSpine.comm Q (star M), star M * M + Q * Q] ∧
    chiralCharge55 * nativeFiveModeMajorana -
      nativeFiveModeMajorana * chiralCharge55 = nativeFiveModeChiralDefect ∧
    nativeFiveModeChiralDefect * annihilation55 0 +
      annihilation55 0 * nativeFiveModeChiralDefect = 1 ∧
    chiralCharge55 * nativeFiveModeMajorana -
      nativeFiveModeMajorana * chiralCharge55 ≠ 0 ∧
    massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana +
      andreevSwap *
        massiveBdGCommutatorAnomaly chiralCharge55 nativeFiveModeMajorana *
        andreevSwap = 0 := by
  refine ⟨bdgStarHamiltonian_sq Q M,
    chiralCharge55_commutator_nativeFiveModeMajorana,
    nativeFiveModeChiralDefect_anticomm_annihilation_zero,
    ?_,
    nativeFiveMode_chiral_bdg_anomaly_andreev_cancellation.2.1⟩
  intro h_zero
  have h_anti := nativeFiveModeChiralDefect_anticomm_annihilation_zero
  rw [← chiralCharge55_commutator_nativeFiveModeMajorana, h_zero, zero_mul, mul_zero, add_zero] at h_anti
  exact zero_ne_one h_anti

end StageChi5

/-! ===========================================================================
    Section 6: Stage χ₆ — Exact Operator Gell-Mann–Oakes–Renner (GMOR)
    Ward–Takahashi Identity & Higgs–GMOR Duality
    =========================================================================== -/

section StageChi6

variable {B : Type*} [Ring B]

/-- The axial double-commutator superoperator `ℳ_{γ₅}(X) := -[γ₅, [γ₅, X]]` probing the
response of an operator `X : B` to chiral rotations generated by `chiralGamma5 P`. -/
def axialDoubleCommutator (P X : B) : B :=
  -comm (chiralGamma5 P) (comm (chiralGamma5 P) X)

/-- The explicit chiral-symmetry-breaking quark-mass Hamiltonian `H_m(P, m_q, A, C) := -(m_q * Φ)`
pairing a quark-mass operator `m_q : B` with the chiral condensate `Φ = genPhi P A C`. -/
def quarkMassHamiltonian (P m_q A C : B) : B :=
  -(m_q * genPhi P A C)

variable {P : B} (hP : P * P = P)
include hP

/-- **Ward–Takahashi First Axial Commutator**:
1. `[γ₅, Φ] = 2 • J` and `[γ₅, J] = 2 • Φ`,
2. `[γ₅, evenGrade P X] = 0`,
3. `[γ₅, oddGrade P X] = 2 • (γ₅ * oddGrade P X)`. -/
theorem ward_takahashi_first_axial_commutator (A C X : B) :
    comm (chiralGamma5 P) (genPhi P A C) = (2 : ℤ) • genJ P A C ∧
    comm (chiralGamma5 P) (genJ P A C) = (2 : ℤ) • genPhi P A C ∧
    comm (chiralGamma5 P) (evenGrade P X) = 0 ∧
    comm (chiralGamma5 P) (oddGrade P X) =
      (2 : ℤ) • (chiralGamma5 P * oddGrade P X) := by
  unfold chiralGamma5
  simp only [two_zsmul]
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

/-- **Universal Axial Double-Commutator Eigenvalue Law**:
1. `axialDoubleCommutator P (evenGrade P X) = 0` (the unbroken subalgebra `𝔨` has zero axial susceptibility),
2. `axialDoubleCommutator P (oddGrade P X) = -((4 : ℤ) • oddGrade P X)` (every broken chiral-odd operator
   has exact axial eigenvalue `-4`),
3. In particular, `axialDoubleCommutator P (genPhi P A C) = -((4 : ℤ) • genPhi P A C)` and
   `axialDoubleCommutator P (genJ P A C) = -((4 : ℤ) • genJ P A C)`. -/
theorem axialDoubleCommutator_even_and_odd_eigenvalues (A C X : B) :
    axialDoubleCommutator P (evenGrade P X) = 0 ∧
    axialDoubleCommutator P (oddGrade P X) = -((4 : ℤ) • oddGrade P X) ∧
    axialDoubleCommutator P (genPhi P A C) = -((4 : ℤ) • genPhi P A C) ∧
    axialDoubleCommutator P (genJ P A C) = -((4 : ℤ) • genJ P A C) := by
  unfold axialDoubleCommutator chiralGamma5
  simp only [four_zsmul_eq]
  refine ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩

omit hP in
/-- Helper: any operator `m_q : B` that commutes with `P` (`P * m_q = m_q * P`) commutes with
`chiralGamma5 P`. -/
theorem chiralGamma5_comm_of_comm_proj {m_q : B} (hm : P * m_q = m_q * P) :
    chiralGamma5 P * m_q = m_q * chiralGamma5 P := by
  unfold chiralGamma5 invS
  calc
    (P - (1 - P)) * m_q = (P * m_q + P * m_q) - m_q := by noncomm_ring
    _ = (m_q * P + m_q * P) - m_q := by rw [hm]
    _ = m_q * (P - (1 - P)) := by noncomm_ring

/-- **Operator Gell-Mann–Oakes–Renner (GMOR) Ward–Takahashi Identity**:
For any quark-mass operator `m_q : B` in the unbroken centralizer of `P` (`P * m_q = m_q * P`):
1. The first axial commutator (axial current divergence) of `H_m = -(m_q * Φ)` is:
   `comm (chiralGamma5 P) (quarkMassHamiltonian P m_q A C) = -((2 : ℤ) • (m_q * genJ P A C))`,
2. The axial double commutator (pion axial susceptibility) of `H_m = -(m_q * Φ)` is:
   `axialDoubleCommutator P (quarkMassHamiltonian P m_q A C) = (4 : ℤ) • (m_q * genPhi P A C)`. -/
theorem operator_gmor_ward_takahashi_identity
    {m_q : B} (hm : P * m_q = m_q * P) (A C : B) :
    comm (chiralGamma5 P) (quarkMassHamiltonian P m_q A C) =
      -((2 : ℤ) • (m_q * genJ P A C)) ∧
    axialDoubleCommutator P (quarkMassHamiltonian P m_q A C) =
      (4 : ℤ) • (m_q * genPhi P A C) := by
  have hγm : chiralGamma5 P * m_q = m_q * chiralGamma5 P :=
    chiralGamma5_comm_of_comm_proj hm
  have hConv := chiralGamma5_mul_conversions hP A C
  have hFirst :
      comm (chiralGamma5 P) (quarkMassHamiltonian P m_q A C) =
        -((2 : ℤ) • (m_q * genJ P A C)) := by
    unfold quarkMassHamiltonian OperatorAlgebra.PeirceSpine.comm
    calc
      chiralGamma5 P * -(m_q * genPhi P A C) - -(m_q * genPhi P A C) * chiralGamma5 P
          = -((chiralGamma5 P * m_q) * genPhi P A C) +
            m_q * (genPhi P A C * chiralGamma5 P) := by noncomm_ring
      _ = -(m_q * (chiralGamma5 P * genPhi P A C)) +
            m_q * (-genJ P A C) := by rw [hγm, hConv.2.1]; noncomm_ring
      _ = -(m_q * genJ P A C) + m_q * (-genJ P A C) := by rw [hConv.1]
      _ = -((2 : ℤ) • (m_q * genJ P A C)) := by
        simp only [two_zsmul]
        noncomm_ring
  refine ⟨hFirst, ?_⟩
  unfold axialDoubleCommutator
  rw [hFirst]
  unfold OperatorAlgebra.PeirceSpine.comm
  calc
    -(chiralGamma5 P * -((2 : ℤ) • (m_q * genJ P A C)) -
        -((2 : ℤ) • (m_q * genJ P A C)) * chiralGamma5 P)
        = (2 : ℤ) • ((chiralGamma5 P * m_q) * genJ P A C) -
          (2 : ℤ) • (m_q * (genJ P A C * chiralGamma5 P)) := by
          simp only [two_zsmul]
          noncomm_ring
    _ = (2 : ℤ) • (m_q * (chiralGamma5 P * genJ P A C)) -
          (2 : ℤ) • (m_q * (-genPhi P A C)) := by
          rw [hγm, hConv.2.2.2.1]
          simp only [two_zsmul]
          noncomm_ring
    _ = (2 : ℤ) • (m_q * genPhi P A C) - (2 : ℤ) • (m_q * (-genPhi P A C)) := by
          rw [hConv.2.2.1]
    _ = (4 : ℤ) • (m_q * genPhi P A C) := by
          simp only [two_zsmul, four_zsmul_eq]
          noncomm_ring

/-- **Expectation / Trace Readout of the Operator GMOR Identity**:
For any additive state/trace functional `τ : B →+ G` into an `AddCommGroup G` and any quark mass
`m_q : B` with `P * m_q = m_q * P`, the expectation of the axial double commutator equals four
times the quark-mass condensate expectation `4 • τ(m_q * Φ)`. -/
theorem expectation_gmor_trace_identity
    {G : Type*} [AddCommGroup G] (τ : B →+ G)
    {m_q : B} (hm : P * m_q = m_q * P) (A C : B) :
    τ (axialDoubleCommutator P (quarkMassHamiltonian P m_q A C)) =
      (4 : ℤ) • τ (m_q * genPhi P A C) := by
  rw [(operator_gmor_ward_takahashi_identity hP hm A C).2, map_zsmul]

/-- **Archetype `χ₆` Summary (`archetype_chi6_higgs_gmor_dual_double_commutator`)**:
Exhibits the exact non-commutative duality between:
1. **The Higgs/Vortex Mass Double Commutator** (probing `γ₅` with `ℳ_Φ`):
   `opHiggsMassOperator P A C (chiralGamma5 P) = -(opVortexMassSq P A C * chiralGamma5 P)`,
2. **The GMOR Axial Double Commutator** (probing `Φ` and `H_m = -(m_q * Φ)` with `ℳ_{γ₅}`):
   `axialDoubleCommutator P (genPhi P A C) = -((4 : ℤ) • genPhi P A C)` and
   `axialDoubleCommutator P (quarkMassHamiltonian P m_q A C) = (4 : ℤ) • (m_q * genPhi P A C)`. -/
theorem archetype_chi6_higgs_gmor_dual_double_commutator
    {m_q : B} (hm : P * m_q = m_q * P) (A C : B) :
    opHiggsMassOperator P A C (chiralGamma5 P) =
      -(opVortexMassSq P A C * chiralGamma5 P) ∧
    axialDoubleCommutator P (genPhi P A C) = -((4 : ℤ) • genPhi P A C) ∧
    comm (chiralGamma5 P) (quarkMassHamiltonian P m_q A C) =
      -((2 : ℤ) • (m_q * genJ P A C)) ∧
    axialDoubleCommutator P (quarkMassHamiltonian P m_q A C) =
      (4 : ℤ) • (m_q * genPhi P A C) := by
  refine ⟨(opHiggsMassOperator_chiralGamma5 hP A C).1, ?_,
    (operator_gmor_ward_takahashi_identity hP hm A C).1,
    (operator_gmor_ward_takahashi_identity hP hm A C).2⟩
  unfold axialDoubleCommutator chiralGamma5
  simp only [four_zsmul_eq]
  peirce_nf hP

end StageChi6

/-! ===========================================================================
    Section 7: Stage χ₇ — Exact Non-Commutative Peirce–Dirac Resolvent and
    Characteristic-Free Algebraic Banks–Casher Trace Theorem
    =========================================================================== -/

section StageChi7

variable {B : Type*} [Ring B]

/-- The massive Peirce–Dirac operator `D(P, A, C, η) := J + η = genJ P A C + η`. -/
def peirceDiracOp (P A C η : B) : B :=
  genJ P A C + η

/-- The chiral-conjugate Peirce–Dirac numerator `D̃(P, A, C, η) := -J + η = -genJ P A C + η`. -/
def peirceDiracConjOp (P A C η : B) : B :=
  -genJ P A C + η

/-- The positive-definite Lorentzian denominator `D₂(P, A, C, η) := V + η² = genV P A C + η * η`. -/
def peirceDiracDenom (P A C η : B) : B :=
  genV P A C + η * η

/-- Given an inverse witness `R_η : B` for `peirceDiracDenom P A C η`, the **Peirce–Dirac Resolvent**
is `G_Dirac(P, A, C, η, R_η) := (-J + η) * R_η`. -/
def peirceDiracResolvent (P A C η R_η : B) : B :=
  peirceDiracConjOp P A C η * R_η

/-- The chiral-odd current propagator component `-J * R_η` of the Peirce–Dirac resolvent. -/
def peirceDiracResolventOdd (P A C R_η : B) : B :=
  -genJ P A C * R_η

/-- The chiral-even Lorentzian spectral kernel `η * R_η` of the Peirce–Dirac resolvent. -/
def peirceDiracResolventEven (η R_η : B) : B :=
  η * R_η

variable {P : B} (hP : P * P = P)
include hP

/-- **Quadratic Factorization of the Massive Peirce–Dirac Operator**:
For any mass parameter `η : B` commuting with the Dirac current `J = genJ P A C`
(`η * J = J * η`), multiplying `J + η` and `-J + η` in either order yields the Lorentzian
denominator `V + η² = peirceDiracDenom P A C η`. -/
theorem peirceDiracOp_mul_conj (A C : B) {η : B}
    (hηJ : η * genJ P A C = genJ P A C * η) :
    peirceDiracOp P A C η * peirceDiracConjOp P A C η = peirceDiracDenom P A C η ∧
    peirceDiracConjOp P A C η * peirceDiracOp P A C η = peirceDiracDenom P A C η := by
  have hJSq : genJ P A C * genJ P A C = -genV P A C :=
    (genPhi_and_genJ_squares hP A C).2
  unfold peirceDiracOp peirceDiracConjOp peirceDiracDenom
  refine ⟨?_, ?_⟩
  · calc
      (genJ P A C + η) * (-genJ P A C + η)
          = -(genJ P A C * genJ P A C) + (genJ P A C * η - η * genJ P A C) + η * η := by
            noncomm_ring
      _ = -(-genV P A C) + (genJ P A C * η - genJ P A C * η) + η * η := by
            rw [hJSq, hηJ]
      _ = genV P A C + η * η := by noncomm_ring
  · calc
      (-genJ P A C + η) * (genJ P A C + η)
          = -(genJ P A C * genJ P A C) + (η * genJ P A C - genJ P A C * η) + η * η := by
            noncomm_ring
      _ = -(-genV P A C) + (genJ P A C * η - genJ P A C * η) + η * η := by
            rw [hJSq, hηJ]
      _ = genV P A C + η * η := by noncomm_ring

/-- **Exact Two-Sided Inverse Law of the Peirce–Dirac Resolvent**:
If `η` commutes with `J = genJ P A C` and `R_η` is a two-sided inverse of `V + η²`
(`(V + η²) * R_η = 1` and `R_η * (V + η²) = 1`), then:
1. `peirceDiracOp P A C η * peirceDiracResolvent P A C η R_η = 1`,
2. `peirceDiracResolvent P A C η R_η * peirceDiracOp P A C η = 1`,
3. `R_η` automatically commutes with `peirceDiracConjOp P A C η = -J + η`,
4. `peirceDiracResolvent P A C η R_η = peirceDiracResolventOdd P A C R_η + peirceDiracResolventEven η R_η`. -/
theorem peirceDiracResolvent_two_sided_inverse (A C : B) {η R_η : B}
    (hηJ : η * genJ P A C = genJ P A C * η)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    peirceDiracOp P A C η * peirceDiracResolvent P A C η R_η = 1 ∧
    peirceDiracResolvent P A C η R_η * peirceDiracOp P A C η = 1 ∧
    R_η * peirceDiracConjOp P A C η = peirceDiracConjOp P A C η * R_η ∧
    peirceDiracResolvent P A C η R_η =
      peirceDiracResolventOdd P A C R_η + peirceDiracResolventEven η R_η := by
  have hQuad := peirceDiracOp_mul_conj hP A C hηJ
  have hDG : peirceDiracOp P A C η * (peirceDiracConjOp P A C η * R_η) = 1 := by
    rw [← mul_assoc, hQuad.1, hR_right]
  have hLD : (R_η * peirceDiracConjOp P A C η) * peirceDiracOp P A C η = 1 := by
    rw [mul_assoc, hQuad.2, hR_left]
  have hLG : R_η * peirceDiracConjOp P A C η = peirceDiracConjOp P A C η * R_η := by
    calc
      R_η * peirceDiracConjOp P A C η
          = (R_η * peirceDiracConjOp P A C η) * 1 := by rw [mul_one]
      _ = (R_η * peirceDiracConjOp P A C η) *
            (peirceDiracOp P A C η * (peirceDiracConjOp P A C η * R_η)) := by rw [hDG]
      _ = ((R_η * peirceDiracConjOp P A C η) * peirceDiracOp P A C η) *
            (peirceDiracConjOp P A C η * R_η) := by noncomm_ring
      _ = 1 * (peirceDiracConjOp P A C η * R_η) := by rw [hLD]
      _ = peirceDiracConjOp P A C η * R_η := by rw [one_mul]
  refine ⟨hDG, ?_, hLG, ?_⟩
  · unfold peirceDiracResolvent
    rw [← hLG]
    exact hLD
  · unfold peirceDiracResolvent peirceDiracConjOp peirceDiracResolventOdd peirceDiracResolventEven
    noncomm_ring

/-- **Automatic Commutation of the Resolvent Inverse `R_η` with the Chiral Projector `P`**:
Whenever `P * η = η * P`, `P` commutes with `peirceDiracDenom P A C η = V + η²`, and therefore
automatically commutes with any two-sided inverse `R_η` of `V + η²`. -/
theorem proj_comm_resolvent_of_comm_eta (A C : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    P * peirceDiracDenom P A C η = peirceDiracDenom P A C η * P ∧
    P * R_η = R_η * P := by
  have hPV : P * genV P A C = genV P A C * P := by peirce_nf hP
  have hPη2 : P * (η * η) = (η * η) * P := by
    calc
      P * (η * η) = (P * η) * η := by rw [mul_assoc]
      _ = (η * P) * η := by rw [hPη]
      _ = η * (P * η) := by rw [mul_assoc]
      _ = η * (η * P) := by rw [hPη]
      _ = (η * η) * P := by rw [mul_assoc]
  have hPDenom : P * peirceDiracDenom P A C η = peirceDiracDenom P A C η * P := by
    unfold peirceDiracDenom
    calc
      P * (genV P A C + η * η) = P * genV P A C + P * (η * η) := by noncomm_ring
      _ = genV P A C * P + (η * η) * P := by rw [hPV, hPη2]
      _ = (genV P A C + η * η) * P := by noncomm_ring
  refine ⟨hPDenom, ?_⟩
  calc
    P * R_η = (R_η * peirceDiracDenom P A C η) * (P * R_η) := by rw [hR_left, one_mul]
    _ = R_η * (peirceDiracDenom P A C η * P) * R_η := by noncomm_ring
    _ = R_η * (P * peirceDiracDenom P A C η) * R_η := by rw [hPDenom]
    _ = (R_η * P) * (peirceDiracDenom P A C η * R_η) := by noncomm_ring
    _ = R_η * P := by rw [hR_right, mul_one]

omit hP in
/-- Helper: right multiplication by any element `Y : B` commuting with `P` (`P * Y = Y * P`)
intertwines `evenGrade P` and `oddGrade P`. -/
theorem evenGrade_and_oddGrade_mul_of_comm_proj (X : B) {Y : B}
    (hPY : P * Y = Y * P) :
    evenGrade P (X * Y) = evenGrade P X * Y ∧
    oddGrade P (X * Y) = oddGrade P X * Y := by
  refine ⟨?_, ?_⟩
  · unfold evenGrade
    calc
      P * (X * Y) * P + (1 - P) * (X * Y) * (1 - P)
          = P * X * (Y * P) + (1 - P) * X * (Y - Y * P) := by noncomm_ring
      _ = P * X * (P * Y) + (1 - P) * X * (Y - P * Y) := by rw [← hPY]
      _ = (P * X * P + (1 - P) * X * (1 - P)) * Y := by noncomm_ring
  · unfold oddGrade
    calc
      P * (X * Y) * (1 - P) + (1 - P) * (X * Y) * P
          = P * X * (Y - Y * P) + (1 - P) * X * (Y * P) := by noncomm_ring
      _ = P * X * (Y - P * Y) + (1 - P) * X * (P * Y) := by rw [← hPY]
      _ = (P * X * (1 - P) + (1 - P) * X * P) * Y := by noncomm_ring

/-- **Exact Chiral Parity Decomposition of the Peirce–Dirac Resolvent**:
When `P * η = η * P` and `R_η` is a two-sided inverse of `V + η²`:
1. The odd propagator `-J * R_η` is purely chiral-odd (`evenGrade P (-J * R_η) = 0`,
   `oddGrade P (-J * R_η) = -J * R_η`),
2. The Lorentzian kernel `η * R_η` is purely chiral-even (`evenGrade P (η * R_η) = η * R_η`,
   `oddGrade P (η * R_η) = 0`),
3. The full resolvent satisfies `evenGrade P (peirceDiracResolvent P A C η R_η) = η * R_η` and
   `oddGrade P (peirceDiracResolvent P A C η R_η) = -J * R_η`. -/
theorem peirceDiracResolvent_chiral_parity_decomposition (A C : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    evenGrade P (peirceDiracResolventOdd P A C R_η) = 0 ∧
    oddGrade P (peirceDiracResolventOdd P A C R_η) =
      peirceDiracResolventOdd P A C R_η ∧
    evenGrade P (peirceDiracResolventEven η R_η) =
      peirceDiracResolventEven η R_η ∧
    oddGrade P (peirceDiracResolventEven η R_η) = 0 ∧
    evenGrade P (peirceDiracResolvent P A C η R_η) =
      peirceDiracResolventEven η R_η ∧
    oddGrade P (peirceDiracResolvent P A C η R_η) =
      peirceDiracResolventOdd P A C R_η := by
  have hPR : P * R_η = R_η * P :=
    (proj_comm_resolvent_of_comm_eta hP A C hPη hR_right hR_left).2
  have hOddMul := evenGrade_and_oddGrade_mul_of_comm_proj (-genJ P A C) hPR
  have hEvenMul := evenGrade_and_oddGrade_mul_of_comm_proj η hPR
  have hJ_even : evenGrade P (-genJ P A C) = 0 := by peirce_nf hP
  have hJ_odd : oddGrade P (-genJ P A C) = -genJ P A C := by peirce_nf hP
  have hη_even : evenGrade P η = η := by
    have h1 := (evenGrade_and_oddGrade_mul_of_comm_proj (1 : B) hPη).1
    have h1_even : evenGrade P (1 : B) = 1 := by peirce_nf hP
    simpa [one_mul, h1_even] using h1
  have hη_odd : oddGrade P η = 0 := by
    have h1 := (evenGrade_and_oddGrade_mul_of_comm_proj (1 : B) hPη).2
    have h1_odd : oddGrade P (1 : B) = 0 := by peirce_nf hP
    simpa [one_mul, h1_odd] using h1
  have hROdd_even : evenGrade P (peirceDiracResolventOdd P A C R_η) = 0 := by
    unfold peirceDiracResolventOdd
    rw [hOddMul.1, hJ_even, zero_mul]
  have hROdd_odd :
      oddGrade P (peirceDiracResolventOdd P A C R_η) =
        peirceDiracResolventOdd P A C R_η := by
    unfold peirceDiracResolventOdd
    rw [hOddMul.2, hJ_odd]
  have hREven_even :
      evenGrade P (peirceDiracResolventEven η R_η) =
        peirceDiracResolventEven η R_η := by
    unfold peirceDiracResolventEven
    rw [hEvenMul.1, hη_even]
  have hREven_odd : oddGrade P (peirceDiracResolventEven η R_η) = 0 := by
    unfold peirceDiracResolventEven
    rw [hEvenMul.2, hη_odd, zero_mul]
  have hConj_even : evenGrade P (peirceDiracConjOp P A C η) = η := by
    unfold peirceDiracConjOp evenGrade
    calc
      P * (-genJ P A C + η) * P + (1 - P) * (-genJ P A C + η) * (1 - P)
          = evenGrade P (-genJ P A C) + evenGrade P η := by
            unfold evenGrade
            noncomm_ring
      _ = 0 + η := by rw [hJ_even, hη_even]
      _ = η := zero_add η
  have hConj_odd : oddGrade P (peirceDiracConjOp P A C η) = -genJ P A C := by
    unfold peirceDiracConjOp oddGrade
    calc
      P * (-genJ P A C + η) * (1 - P) + (1 - P) * (-genJ P A C + η) * P
          = oddGrade P (-genJ P A C) + oddGrade P η := by
            unfold oddGrade
            noncomm_ring
      _ = -genJ P A C + 0 := by rw [hJ_odd, hη_odd]
      _ = -genJ P A C := add_zero _
  have hFullMul := evenGrade_and_oddGrade_mul_of_comm_proj (peirceDiracConjOp P A C η) hPR
  refine ⟨hROdd_even, hROdd_odd, hREven_even, hREven_odd, ?_, ?_⟩
  · unfold peirceDiracResolvent peirceDiracResolventEven
    rw [hFullMul.1, hConj_even]
  · unfold peirceDiracResolvent peirceDiracResolventOdd
    rw [hFullMul.2, hConj_odd]

/-- **Characteristic-Free Cyclic Trace Annihilation of `conePlus`, `coneMinus`, and `oddGrade`**:
For any additive homomorphism `τ : B →+ G` satisfying cyclic invariance
`∀ x y : B, τ (x * y) = τ (y * x)` (over any ring `B`, with no division by `2` required):
1. `τ (conePlus P X) = 0`,
2. `τ (coneMinus P X) = 0`,
3. `τ (oddGrade P X) = 0`,
4. `τ X = τ (evenGrade P X)`. -/
theorem cyclic_trace_oddGrade_zero_and_eq_evenGrade
    {G : Type*} [AddCommGroup G] (τ : B →+ G)
    (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x)) (X : B) :
    τ (conePlus P X) = 0 ∧
    τ (coneMinus P X) = 0 ∧
    τ (oddGrade P X) = 0 ∧
    τ X = τ (evenGrade P X) := by
  have h1P : (1 - P) * (P * X) = 0 := by peirce_nf hP
  have hP1 : P * ((1 - P) * X) = 0 := by peirce_nf hP
  have hPlus : τ (conePlus P X) = 0 := by
    unfold conePlus
    calc
      τ (P * X * (1 - P)) = τ ((1 - P) * (P * X)) := hτ_cyc (P * X) (1 - P)
      _ = τ 0 := by rw [h1P]
      _ = 0 := map_zero τ
  have hMinus : τ (coneMinus P X) = 0 := by
    unfold coneMinus
    calc
      τ ((1 - P) * X * P) = τ (P * ((1 - P) * X)) := hτ_cyc ((1 - P) * X) P
      _ = τ 0 := by rw [hP1]
      _ = 0 := map_zero τ
  have hOddEq : oddGrade P X = conePlus P X + coneMinus P X := rfl
  have hOdd : τ (oddGrade P X) = 0 := by
    rw [hOddEq, map_add, hPlus, hMinus, add_zero]
  have hDecomp : X = evenGrade P X + oddGrade P X := by peirce_nf hP
  refine ⟨hPlus, hMinus, hOdd, ?_⟩
  conv_lhs => rw [hDecomp]
  rw [map_add, hOdd, add_zero]

/-- **Characteristic-Free Algebraic Banks–Casher Resolvent Trace Theorem**:
For any cyclically invariant additive map `τ : B →+ G` (`∀ x y, τ(x * y) = τ(y * x)`),
whenever `P * η = η * P` and `R_η` is a two-sided inverse of `V + η²`:
1. The chiral-odd current propagator has trace zero:
   `τ (peirceDiracResolventOdd P A C R_η) = 0`,
2. The trace of the full Peirce–Dirac resolvent reduces to the trace of the chiral-even
   Lorentzian spectral kernel `η * R_η = η * (V + η²)⁻¹`:
   `τ (peirceDiracResolvent P A C η R_η) = τ (η * R_η)`. -/
theorem algebraic_banks_casher_resolvent_trace_identity
    {G : Type*} [AddCommGroup G] (τ : B →+ G)
    (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A C : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1) :
    τ (peirceDiracResolventOdd P A C R_η) = 0 ∧
    τ (peirceDiracResolvent P A C η R_η) = τ (η * R_η) := by
  have hParity :=
    peirceDiracResolvent_chiral_parity_decomposition hP A C hPη hR_right hR_left
  have hTraceOdd :=
    (cyclic_trace_oddGrade_zero_and_eq_evenGrade hP τ hτ_cyc
      (peirceDiracResolventOdd P A C R_η)).2.2.2
  have hTraceFull :=
    (cyclic_trace_oddGrade_zero_and_eq_evenGrade hP τ hτ_cyc
      (peirceDiracResolvent P A C η R_η)).2.2.2
  refine ⟨?_, ?_⟩
  · rw [hTraceOdd, hParity.1, map_zero]
  · rw [hTraceFull, hParity.2.2.2.2.1]
    rfl

end StageChi7

/-! ===========================================================================
    Section 8: Stage χ₈ — Self-Consistent NJL Gap Fixed-Point Bifurcation,
    Trap T16/T17 Non-Commutative Matrix Witnesses, and Master Synthesis
    =========================================================================== -/

section StageChi8

/-- The Nambu–Jona-Lasinio (NJL) self-consistent gap residual
`njlGapResidual m₀ g_njl I_bc η := η - (m₀ + g_njl * (η * I_bc))`
for bare mass `m₀`, four-fermion coupling `g_njl = 2G`, Lorentzian spectral integral `I_bc`,
and dynamical constituent mass `η`. -/
def njlGapResidual {R : Type*} [Ring R] (m₀ g_njl I_bc η : R) : R :=
  η - (m₀ + g_njl * (η * I_bc))

/-- **Exact Chiral-Limit NJL Gap Factorization**:
In the chiral limit `m₀ = 0`, whenever `g_njl` commutes with `η` (`g_njl * η = η * g_njl`),
the NJL gap residual factors into `η * (1 - g_njl * I_bc)`. -/
theorem njl_chiral_limit_factorization {R : Type*} [Ring R]
    {g_njl I_bc η : R} (h_comm : g_njl * η = η * g_njl) :
    njlGapResidual 0 g_njl I_bc η = η * (1 - g_njl * I_bc) := by
  unfold njlGapResidual
  calc
    η - (0 + g_njl * (η * I_bc))
        = η - (g_njl * η) * I_bc := by noncomm_ring
    _ = η - (η * g_njl) * I_bc := by rw [h_comm]
    _ = η * (1 - g_njl * I_bc) := by noncomm_ring

/-- **Self-Consistent NJL Gap Bifurcation Theorem (`njl_chiral_limit_bifurcation_iff`)**:
Over any domain `[Ring R] [NoZeroDivisors R]` with `g_njl * η = η * g_njl`, the chiral-limit
NJL gap equation `njlGapResidual 0 g_njl I_bc η = 0` holds if and only if either:
1. `η = 0` (the chirally symmetric Wigner–Weyl vacuum), or
2. `g_njl * I_bc = 1` (the dynamically broken Nambu–Goldstone condensate branch). -/
theorem njl_chiral_limit_bifurcation_iff {R : Type*} [Ring R] [NoZeroDivisors R]
    {g_njl I_bc η : R} (h_comm : g_njl * η = η * g_njl) :
    njlGapResidual 0 g_njl I_bc η = 0 ↔ η = 0 ∨ g_njl * I_bc = 1 := by
  rw [njl_chiral_limit_factorization h_comm, mul_eq_zero, sub_eq_zero, eq_comm (a := (1 : R))]

/-- **Operator-to-Scalar NJL Self-Consistency Bridge via Banks–Casher**:
When a cyclic trace `τ : B →+ R` satisfies `τ (η * R_η) = η_s * τ R_η` for a scalar mass
readout `η_s : R`, substituting `τ (peirceDiracResolvent P A C η R_η)` into the NJL gap
equation reduces directly to `njlGapResidual m₀ g_njl (τ R_η) η_s`. -/
theorem njl_operator_self_consistency_from_banks_casher
    {B R : Type*} [Ring B] [Ring R]
    {P : B} (hP : P * P = P)
    (τ : B →+ R) (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    (A C : B) {η R_η : B}
    (hPη : P * η = η * P)
    (hR_right : peirceDiracDenom P A C η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P A C η = 1)
    (m₀ g_njl η_s : R)
    (hτ_scale : τ (η * R_η) = η_s * τ R_η) :
    η_s - (m₀ + g_njl * τ (peirceDiracResolvent P A C η R_η)) =
      njlGapResidual m₀ g_njl (τ R_η) η_s := by
  have hBC :=
    (algebraic_banks_casher_resolvent_trace_identity hP τ hτ_cyc A C hPη hR_right hR_left).2
  rw [hBC, hτ_scale]
  rfl

/-! ### Concrete Non-Commutative `2 × 2` Matrix Witnesses (`Trap T16` & `Trap T17`) -/

/-- Concrete `2 × 2` projector `P₂ = !![1, 0; 0, 0]` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def witnessProj2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 0; 0, 0]

/-- Concrete `2 × 2` off-diagonal gauge potential `A₂ = !![0, 1; 1, 0]` in `Matrix (Fin 2) (Fin 2) ℤ`. -/
def witnessPot2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; 1, 0]

/-- Polymorphic `2 × 2` projector `!![1, 0; 0, 0]` over any ring `B`. -/
def witnessMatProj2 {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![1, 0; 0, 0]

/-- Polymorphic `2 × 2` off-diagonal gauge potential `!![0, 1; 1, 0]` over any ring `B`. -/
def witnessMatPot2 {B : Type*} [Ring B] : Matrix (Fin 2) (Fin 2) B :=
  !![0, 1; 1, 0]

/-- Explicit non-commutativity of `witnessMatProj2` and `witnessMatPot2` over any nontrivial ring `B`,
and specifically over `ℤ` (`witnessProj2 * witnessPot2 ≠ witnessPot2 * witnessProj2`). -/
theorem witnessMatProj2_witnessMatPot2_noncomm {B : Type*} [Ring B] [Nontrivial B] :
    (witnessMatProj2 : Matrix (Fin 2) (Fin 2) B) * (witnessMatPot2 : Matrix (Fin 2) (Fin 2) B) ≠
      (witnessMatPot2 : Matrix (Fin 2) (Fin 2) B) * (witnessMatProj2 : Matrix (Fin 2) (Fin 2) B) ∧
    witnessProj2 * witnessPot2 ≠ witnessPot2 * witnessProj2 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [witnessMatProj2, witnessMatPot2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  · intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [witnessProj2, witnessPot2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- `witnessProj2` is an idempotent (`P₂ * P₂ = P₂`). -/
theorem witnessProj2_idempotent :
    witnessProj2 * witnessProj2 = witnessProj2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessProj2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit evaluations of `chiralGamma5`, `genPhi`, and `genV` on `(witnessProj2, witnessPot2)`. -/
theorem witnessProj2_pot2_evals :
    chiralGamma5 witnessProj2 = !![1, 0; 0, -1] ∧
    genPhi witnessProj2 witnessPot2 witnessPot2 = !![0, 1; 1, 0] ∧
    genV witnessProj2 witnessPot2 witnessPot2 = !![1, 0; 0, 1] := by
  have hPhi : genPhi witnessProj2 witnessPot2 witnessPot2 = !![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [genPhi, conePlus, coneMinus, witnessProj2, witnessPot2,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  refine ⟨?_, hPhi, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralGamma5, invS, witnessProj2]
  · have hSq := (genPhi_and_genJ_squares witnessProj2_idempotent witnessPot2 witnessPot2).1
    rw [← hSq, hPhi]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Trap T16 & T17 Witness (`chiral_gmor_and_resolvent_matrix_witness`)**:
In `Matrix (Fin 2) (Fin 2) ℤ`:
1. `chiralGamma5 witnessProj2` and `genPhi witnessProj2 witnessPot2 witnessPot2` do not commute (`T16`),
2. The operator GMOR double commutator `axialDoubleCommutator witnessProj2 (genPhi witnessProj2 witnessPot2 witnessPot2)`
   is `!![0, -4; -4, 0] ≠ 0` (`T17`),
3. At `η = 1`, the Lorentzian denominator is `peirceDiracDenom witnessProj2 witnessPot2 witnessPot2 1 = !![2, 0; 0, 2] ≠ 0`
   with trace `4 ≠ 0` (`T17`). -/
theorem chiral_gmor_and_resolvent_matrix_witness :
    chiralGamma5 witnessProj2 * genPhi witnessProj2 witnessPot2 witnessPot2 ≠
      genPhi witnessProj2 witnessPot2 witnessPot2 * chiralGamma5 witnessProj2 ∧
    axialDoubleCommutator witnessProj2 (genPhi witnessProj2 witnessPot2 witnessPot2) =
      !![0, -4; -4, 0] ∧
    axialDoubleCommutator witnessProj2 (genPhi witnessProj2 witnessPot2 witnessPot2) ≠ 0 ∧
    peirceDiracDenom witnessProj2 witnessPot2 witnessPot2 1 = !![2, 0; 0, 2] ∧
    Matrix.trace (peirceDiracDenom witnessProj2 witnessPot2 witnessPot2 1) = 4 := by
  have hEv := witnessProj2_pot2_evals
  have hAx :=
    (axialDoubleCommutator_even_and_odd_eigenvalues witnessProj2_idempotent
      witnessPot2 witnessPot2 0).2.2.1
  have hDenom : peirceDiracDenom witnessProj2 witnessPot2 witnessPot2 1 = !![2, 0; 0, 2] := by
    unfold peirceDiracDenom
    rw [hEv.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp
  refine ⟨?_, ?_, ?_, hDenom, ?_⟩
  · rw [hEv.1, hEv.2.1]
    intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  · rw [hAx, hEv.2.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp
  · rw [hAx, hEv.2.1]
    intro h
    have h01 := congr_fun (congr_fun h 0) 1
    simp at h01
  · rw [hDenom]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **Master `solve et coagula` Chiral Condensate, GMOR, Banks–Casher & NJL Synthesis
(`chiral_condensate_gmor_banks_casher_njl_master_synthesis`)**:
Coagulates the complete 8-stage Acyclic Causal Poset `χ₁ ≺ χ₂ ≺ χ₃ ≺ χ₄ ≺ χ₅ ≺ χ₆ ≺ χ₇ ≺ χ₈`
into a single kernel-verified theorem over `[Ring B] [StarRing B]`. -/
theorem chiral_condensate_gmor_banks_casher_njl_master_synthesis
    {B R : Type*} [Ring B] [StarRing B] [Ring R] [NoZeroDivisors R]
    {P a m_q η R_η Q M : B}
    (hP : P * P = P) (hPs : star P = P) (has : star a = a)
    (hm : P * m_q = m_q * P)
    (hPη : P * η = η * P)
    (hηJ : η * genJ P a a = genJ P a a * η)
    (hR_right : peirceDiracDenom P a a η * R_η = 1)
    (hR_left : R_η * peirceDiracDenom P a a η = 1)
    (τ : B →+ R) (hτ_cyc : ∀ x y : B, τ (x * y) = τ (y * x))
    {g_njl I_bc η_s : R} (h_comm : g_njl * η_s = η_s * g_njl) :
    -- (0) Acyclic 8-stage causal poset χ₁ ≺ ⋯ ≺ χ₈
    ((∀ st : ChiralCondensateEpistemicStage,
        ¬ Relation.TransGen ChiralCondensateEpistemicStage.causalEdge st st) ∧
     ChiralCondensateEpistemicStage.causalEdge
       .chi1_ChiralParityCutAndCondensateSquare
       .chi2_GaugeOrbitGramianAndMaurerCartanBianchi ∧
     ChiralCondensateEpistemicStage.causalEdge
       .chi7_PeirceDiracResolventAndBanksCasherTrace
       .chi8_NJLSelfConsistentGapBifurcationAndMasterSynthesis) ∧
    -- (1) Stage χ₁: Chiral involution, anticommutation & Socratic involution defect
    (chiralGamma5 P * chiralGamma5 P = 1 ∧
     anticomm (chiralGamma5 P) (genPhi P a a) = 0 ∧
     (chiralGamma5 P + genPhi P a a) * (chiralGamma5 P + genPhi P a a) - 1 = genV P a a) ∧
    -- (2) Stage χ₂: Gauge-orbit commutator Gramian & Maurer–Cartan Bianchi conservation
    (orbitMassMode P a = genV P a a ∧
     peirceMaurerCartanCurvature P a a = genJ P a a + orbitMassMode P a ∧
     peirceCovariantDeriv P a a (orbitMassMode P a) = 0) ∧
    -- (3) Stage χ₃: Double-commutator Goldstone zero mode & m² = 4V axial/vortex mass
    (opHiggsMassOperator P a a (genPhi P a a) = 0 ∧
     opHiggsMassOperator P a a (genV P a a) = 0 ∧
     opHiggsMassOperator P a a (genJ P a a) = -(opVortexMassSq P a a * genJ P a a) ∧
     opHiggsMassOperator P a a (genSig P a a) = -(opVortexMassSq P a a * genSig P a a) ∧
     opHiggsMassOperator P a a (chiralGamma5 P) = -(opVortexMassSq P a a * chiralGamma5 P)) ∧
    -- (4) Stage χ₄: Symmetric-pair coset [𝔨, 𝔭] ⊆ 𝔭, [𝔭, 𝔭] ⊆ 𝔨 & native (π⁺, π⁻, π⁰) CAR
    (evenGrade P (comm (evenGrade P a) (oddGrade P a)) = 0 ∧
     oddGrade P (comm (oddGrade P a) (oddGrade P a)) = 0 ∧
     piPlus * piMinus + piMinus * piPlus = (1 : M2C) ∧
     ⁅piPlus, piMinus⁆ = (2 : ℂ) • piZero) ∧
    -- (5) Stage χ₅: Universal 2×2 star-BdG square & Cl(5,5) CAR Majorana chiral defect
    (bdgStarHamiltonian Q M * bdgStarHamiltonian Q M =
       !![Q * Q + M * star M, comm Q M; -comm Q (star M), star M * M + Q * Q] ∧
     chiralCharge55 * nativeFiveModeMajorana -
       nativeFiveModeMajorana * chiralCharge55 = nativeFiveModeChiralDefect ∧
     chiralCharge55 * nativeFiveModeMajorana -
       nativeFiveModeMajorana * chiralCharge55 ≠ 0) ∧
    -- (6) Stage χ₆: Operator GMOR Ward–Takahashi double commutator & trace identity
    (axialDoubleCommutator P (quarkMassHamiltonian P m_q a a) =
       (4 : ℤ) • (m_q * genPhi P a a) ∧
     τ (axialDoubleCommutator P (quarkMassHamiltonian P m_q a a)) =
       (4 : ℤ) • τ (m_q * genPhi P a a)) ∧
    -- (7) Stage χ₇: Two-sided Peirce–Dirac resolvent & Banks–Casher trace reduction
    (peirceDiracOp P a a η * peirceDiracResolvent P a a η R_η = 1 ∧
     peirceDiracResolvent P a a η R_η * peirceDiracOp P a a η = 1 ∧
     τ (peirceDiracResolventOdd P a a R_η) = 0 ∧
     τ (peirceDiracResolvent P a a η R_η) = τ (η * R_η)) ∧
    -- (8) Stage χ₈: Self-consistent NJL chiral-limit gap bifurcation
    (njlGapResidual 0 g_njl I_bc η_s = η_s * (1 - g_njl * I_bc) ∧
     (njlGapResidual 0 g_njl I_bc η_s = 0 ↔ η_s = 0 ∨ g_njl * I_bc = 1)) := by
  have hChi1 := archetype_chi1_chiral_parity_cut_and_socratic_involution_defect hP a a
  have hChi2 := archetype_chi2_gauge_orbit_gramian_and_maurer_cartan_bianchi hP hPs has
  have hChi3 := archetype_chi3_double_commutator_goldstone_vortex_split hP a a
  have hChi4 := archetype_chi4_symmetric_pair_and_native_pion_car hP a a
  have hChi5 := archetype_chi5_cl55_majorana_chiral_defect_and_bdg_andreev Q M
  have hChi6 := archetype_chi6_higgs_gmor_dual_double_commutator hP hm a a
  have hRes := peirceDiracResolvent_two_sided_inverse hP a a hηJ hR_right hR_left
  have hBC :=
    algebraic_banks_casher_resolvent_trace_identity hP τ hτ_cyc a a hPη hR_right hR_left
  refine ⟨⟨ChiralCondensateEpistemicStage.causalEdge_acyclic,
           ChiralCondensateEpistemicStage.causalEdge_chain.1,
           ChiralCondensateEpistemicStage.causalEdge_chain.2.2.2.2.2.2⟩,
          ⟨hChi1.1, hChi1.2.1, hChi1.2.2.2.2.2.2⟩,
          ⟨hChi2.2.1, hChi2.2.2.2.1, hChi2.2.2.2.2.2.1⟩,
          hChi3,
          ⟨hChi4.1.2.1, hChi4.1.2.2, hChi4.2.2.2.1, hChi4.2.2.2.2.1⟩,
          ⟨hChi5.1, hChi5.2.1, hChi5.2.2.2.1⟩,
          ⟨hChi6.2.2.2, expectation_gmor_trace_identity hP τ hm a a⟩,
          ⟨hRes.1, hRes.2.1, hBC.1, hBC.2⟩,
          ⟨njl_chiral_limit_factorization h_comm,
           njl_chiral_limit_bifurcation_iff h_comm⟩⟩

end StageChi8

end InfoGeometry.Canonical.ChiralCondensateGMORBanksCasherNJLPoset

end
