/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSheetedYangMillsInductiveColimit
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
import InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian

/-!
# Two-Sheeted Yang–Mills: Nilpotent-to-Unipotent Condensate, Ordered Möbius–Bruhat / Steinberg Braid Vortices, Vortex Mass `m² = 4V`, and Operator Cyclotomic Locking (`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇`)

This module formalizes the 7-stage Acyclic Causal Poset
`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇` unifying the two-sheeted non-commutative
operator Yang–Mills architecture over an arbitrary associative ring `[Ring B]`
(and `[StarRing B]` where star-involutions or inductive star-colimits appear):

1. **Stage `YM₁` (`ym1_nilpotentToUnipotentCut` — Binary Cut & Nilpotent-to-Unipotent Exponential Condensation)**:
   The forward/backward nilpotent Peirce horizon waves `N₊ = conePlus P A` and `N₋ = coneMinus P C`
   (`N₊² = 0`, `N₋² = 0`) exponentiate via exact truncated series `exp(N₊) = 1 + N₊ = opUnipotentPlus P A`
   and `exp(-N₋) = 1 - N₋ = opUnipotentMinus P C` into one-parameter unipotent groups satisfying
   `U₊(A₁) * U₊(A₂) = U₊(A₁ + A₂)`, `U₋(C₁) * U₋(C₂) = U₋(C₁ + C₂)`, and two-sided invertibility
   `U₊(A) * U₊(-A) = 1`, `U₋(C) * U₋(-C) = 1`.

2. **Stage `YM₂` (`ym2_fourfoldMoebiusBruhatVortexAnatomy` — Fourfold Ordered Möbius–Bruhat Vortex Anatomy, Symmetric Coupling `V`, & Commutator Holonomy `-Σ`)**:
   - The forward unipotent condensate displacement is
     `opCondensateDisplacement P A C := U₊(A) * U₋(C) - 1 = genJ P A C - qgtPlus P A C`
     (`= N₊ - N₋ - N₊ N₋`, carrying the upper sheet cycle `qgtPlus = P V P`),
   - The backward unipotent condensate displacement is
     `opCondensateDisplacementDual P A C := U₋(C) * U₊(A) - 1 = genJ P A C - qgtMinus P A C`
     (`= N₊ - N₋ - N₋ N₊`, carrying the lower sheet cycle `qgtMinus = (1 - P) V (1 - P)`),
   - Their symmetric sum recovers twice the axial current minus the full two-sheet coupling `V = {N₊, N₋}`:
     `opCondensateDisplacement P A C + opCondensateDisplacementDual P A C = (2 : ℤ) • genJ P A C - genV P A C`,
   - Their antisymmetric difference (the unipotent commutator holonomy) is the negative spin-dipole curvature `-Σ = -[N₊, N₋]`:
     `comm (opUnipotentPlus P A) (opUnipotentMinus P C) = -genSig P A C`,
   - The ordered Möbius–Bruhat vortex `g = U₊(A) * U₋(C)` has exact two-sided inverse
     `g⁻¹ = U₋(-C) * U₊(-A)` and preserves the quadratic coupling `g * V * g⁻¹ = V`.

3. **Stage `YM₃` (`ym3_steinbergBraidAndMaurerCartanSelfDual` — Transcendent Function: Steinberg 3-Factor Braid Vortices, Maurer–Cartan Curvature `F = J + V`, & Covariant Bianchi `D_P(V) = 0`)**:
   - The 3-factor Steinberg braid vortices `steinbergBraid P A C = (1 + N₊)(1 - N₋)(1 + N₊)` and
     `steinbergBraidDual P A C = (1 - N₋)(1 + N₊)(1 - N₋)` expand as
     `W + (1 - V) N₊` and `W - (1 - V) N₋` with difference `(1 - V) Φ` and palindromic trace sum
     `steinbergBraid + steinbergBraidInv = (2 : ℤ) • (1 - V)`,
   - The Peirce Maurer–Cartan curvature decomposes into anti-self-dual axial `J` and self-dual metric `V`
     (`peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`), and `V` satisfies the exact
     covariant Bianchi / vacuum self-dual Yang–Mills identity `peirceCovariantDeriv P A C (genV P A C) = 0`.

4. **Stage `YM₄` (`ym4_mexicanHatIhhsVortexMassGeneration` — Socratic Aporia & Mexican-Hat / IHHS Double-Commutator Vortex Mass `m² = 4V`)**:
   The double-commutator mass operator `opHiggsMassOperator P A C X = -[Φ, [Φ, X]]` annihilates
   the Goldstone mode `Φ` and Higgs modulus `V` (`M(Φ) = 0`, `M(V) = 0`) while lifting the
   two-sheet coupling `V = opQuadraticCoupling P A C` into the operatorial vortex mass squared
   `opVortexMassSq P A C = (4 : ℤ) • V` on the axial vortex `J₅ = opAxial P A C` and spin-dipole
   vortex `Σ = opSpinDipole P A C`:
   `opHiggsMassOperator P A C (opAxial P A C) = -(opVortexMassSq P A C * opAxial P A C)` and
   `opHiggsMassOperator P A C (opSpinDipole P A C) = -(opVortexMassSq P A C * opSpinDipole P A C)`.

5. **Stage `YM₅` (`ym5_cyclotomicVortexLockingAndEquivariance` — Operator Cyclotomic `Φ₁₂`/`Φ₂₄` Vortex Reduction & Unipotent/Braid Equivariance)**:
   - Evaluates `opCyclotomicPhi12 X = X⁴ - X² + 1` and `opCyclotomicPhi24 X = X⁸ - X⁴ + 1` on the
     axial vortex `J₅` and spin-dipole vortex `Σ` directly in terms of the coupling `V`:
     `opCyclotomicPhi12 (opAxial P A C) = V ^ 2 + V + 1`,
     `opCyclotomicPhi24 (opAxial P A C) = opCyclotomicPhi12 V`,
     `opCyclotomicPhi12 (opSpinDipole P A C) = opCyclotomicPhi12 V`, and
     `opCyclotomicPhi24 (opSpinDipole P A C) = opCyclotomicPhi24 V`,
   - Proves exact equivariance of `opCyclotomicPhi12` and `opCyclotomicPhi24` under conjugation by
     the ordered Möbius–Bruhat vortex unit `g = U₊(A) * U₋(C)` and by `steinbergBraid P A C`,
     together with cyclotomic root locking (`Φ₁₂(X) = 0 → X⁶ = -1 ∧ X¹² = 1`,
     `Φ₂₄(X) = 0 → X¹² = -1 ∧ X²⁴ = 1`).

6. **Stage `YM₆` (`ym6_inductiveColimitAndMultiChannelVortexDescent` — Functorial `StarRingHom` Transport, Inductive Colimit Vortex Mass Lift, & Multi-Channel Decoupling)**:
   - Intertwining of the unipotent condensate, Möbius–Bruhat displacements, vortex mass `m² = 4V`,
     and cyclotomic potentials under any `StarRingHom`,
   - Multi-step inductive colimit invariance (`k → k + m → ∞`) in `InductiveStarColimitCone`,
   - Multi-channel orthogonal additivity and cross-channel annihilation of `opVortexMassSq`.

7. **Stage `YM₇` (`ym7_masterCondensateVortexSynthesisAndMatrixWitness` — Master Synthesis & Concrete `2 × 2` Non-Commutative Matrix Vortex Witness)**:
   - Certifies non-commutativity (`T16`) and non-vanishing unipotent vortex holonomy, condensate
     displacement, and vortex mass (`T17`) in `Matrix (Fin 2) (Fin 2) ℤ`.
-/

namespace InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass

open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis
open scoped Matrix

/-! ## 0. The 7-Stage Acyclic Causal Poset (`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇`) -/

/-- The 7 stages of the Two-Sheeted Yang–Mills Nilpotent-to-Unipotent Condensate & Vortex Mass Poset. -/
inductive TwoSheetedCondensateVortexStage : Type
  | ym1_nilpotentToUnipotentCut
  | ym2_fourfoldMoebiusBruhatVortexAnatomy
  | ym3_steinbergBraidAndMaurerCartanSelfDual
  | ym4_mexicanHatIhhsVortexMassGeneration
  | ym5_cyclotomicVortexLockingAndEquivariance
  | ym6_inductiveColimitAndMultiChannelVortexDescent
  | ym7_masterCondensateVortexSynthesisAndMatrixWitness
  deriving DecidableEq, Repr

namespace TwoSheetedCondensateVortexStage

/-- Numerical causal depth of each stage (`0` through `6`). -/
def rank : TwoSheetedCondensateVortexStage → ℕ
  | .ym1_nilpotentToUnipotentCut => 0
  | .ym2_fourfoldMoebiusBruhatVortexAnatomy => 1
  | .ym3_steinbergBraidAndMaurerCartanSelfDual => 2
  | .ym4_mexicanHatIhhsVortexMassGeneration => 3
  | .ym5_cyclotomicVortexLockingAndEquivariance => 4
  | .ym6_inductiveColimitAndMultiChannelVortexDescent => 5
  | .ym7_masterCondensateVortexSynthesisAndMatrixWitness => 6

/-- Strict causal precedence `s₁ ≺ s₂` in the Two-Sheeted Condensate & Vortex Mass Poset. -/
abbrev causalEdge (s₁ s₂ : TwoSheetedCondensateVortexStage) : Prop :=
  s₁.rank < s₂.rank

/-- Reflexive-transitive causal order `s₁ ≼ s₂`. -/
abbrev causalLe (s₁ s₂ : TwoSheetedCondensateVortexStage) : Prop :=
  s₁.rank ≤ s₂.rank

instance instLT : LT TwoSheetedCondensateVortexStage := ⟨causalEdge⟩
instance instLE : LE TwoSheetedCondensateVortexStage := ⟨causalLe⟩

/-- `TwoSheetedCondensateVortexStage` forms a strict `LinearOrder` with 7 distinct stages. -/
instance instLinearOrder : LinearOrder TwoSheetedCondensateVortexStage where
  le := causalLe
  lt := causalEdge
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    have hEq : a.rank = b.rank := Nat.le_antisymm hab hba
    cases a <;> cases b <;> first | rfl | cases hEq
  le_total a b := Nat.le_total a.rank b.rank
  toDecidableLE := fun a b => Nat.decLe a.rank b.rank
  toDecidableLT := fun a b => Nat.decLt a.rank b.rank
  toDecidableEq := inferInstance

/-- **Poset Acyclicity & Strict 7-Stage Chain Theorem**:
`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇` is strictly ordered, irreflexive, asymmetric, and transitive. -/
theorem poset_chain_and_acyclicity :
    (causalEdge .ym1_nilpotentToUnipotentCut .ym2_fourfoldMoebiusBruhatVortexAnatomy ∧
     causalEdge .ym2_fourfoldMoebiusBruhatVortexAnatomy .ym3_steinbergBraidAndMaurerCartanSelfDual ∧
     causalEdge .ym3_steinbergBraidAndMaurerCartanSelfDual .ym4_mexicanHatIhhsVortexMassGeneration ∧
     causalEdge .ym4_mexicanHatIhhsVortexMassGeneration .ym5_cyclotomicVortexLockingAndEquivariance ∧
     causalEdge .ym5_cyclotomicVortexLockingAndEquivariance .ym6_inductiveColimitAndMultiChannelVortexDescent ∧
     causalEdge .ym6_inductiveColimitAndMultiChannelVortexDescent .ym7_masterCondensateVortexSynthesisAndMatrixWitness) ∧
    (∀ s : TwoSheetedCondensateVortexStage, ¬ causalEdge s s) ∧
    (∀ s₁ s₂ : TwoSheetedCondensateVortexStage, causalEdge s₁ s₂ → ¬ causalEdge s₂ s₁) ∧
    (∀ s₁ s₂ s₃ : TwoSheetedCondensateVortexStage,
      causalEdge s₁ s₂ → causalEdge s₂ s₃ → causalEdge s₁ s₃) := by
  refine ⟨ by decide, ?_, ?_, ?_⟩
  · intro s
    exact Nat.lt_irrefl s.rank
  · intro s₁ s₂ h12 h21
    exact Nat.lt_asymm h12 h21
  · intro s₁ s₂ s₃ h12 h23
    exact Nat.lt_trans h12 h23

end TwoSheetedCondensateVortexStage

/-! ## 1. Stage `YM₁`: Binary Cut & Nilpotent-to-Unipotent Exponential Condensation -/

section RingIdentities

variable {B : Type*} [Ring B]

/-- Forward unipotent horizon operator `U₊(P, A) = 1 + N₊ = 1 + conePlus P A`. -/
def opUnipotentPlus (P A : B) : B := 1 + conePlus P A

/-- Backward unipotent horizon operator `U₋(P, C) = 1 - N₋ = 1 - coneMinus P C`. -/
def opUnipotentMinus (P C : B) : B := 1 - coneMinus P C

/-- Ordered Möbius–Bruhat vortex unit `g(P, A, C) = U₊(P, A) * U₋(P, C) = (1 + N₊)(1 - N₋)`. -/
def opMoebiusBruhatVortex (P A C : B) : B :=
  opUnipotentPlus P A * opUnipotentMinus P C

/-- Exact two-sided inverse `g⁻¹(P, A, C) = U₋(P, -C) * U₊(P, -A) = (1 + N₋)(1 - N₊)` of the
ordered Möbius–Bruhat vortex unit. -/
def opMoebiusBruhatVortexInv (P A C : B) : B :=
  opUnipotentMinus P (-C) * opUnipotentPlus P (-A)

/-- Forward condensate displacement `U₊(P, A) * U₋(P, C) - 1`. -/
def opCondensateDisplacement (P A C : B) : B :=
  opUnipotentPlus P A * opUnipotentMinus P C - 1

/-- Dual (backward-ordered) condensate displacement `U₋(P, C) * U₊(P, A) - 1`. -/
def opCondensateDisplacementDual (P A C : B) : B :=
  opUnipotentMinus P C * opUnipotentPlus P A - 1

/-- Operator vortex mass squared `m² = 4V = (4 : ℤ) • opQuadraticCoupling P A C`. -/
def opVortexMassSq (P A C : B) : B :=
  (4 : ℤ) • opQuadraticCoupling P A C

/-- In the diagonal self-adjoint specialization `C = A`, the two-sheet
    vortex mass is four times the ordered orbit Gramian. This is an identity
    on the shared ring carrier; it does not assert positivity or an analytic
    spectral gap. -/
theorem diagonal_vortex_mass_eq_four_orbit_gramian
    [StarRing B] (P A : B)
    (hP : P * P = P)
    (hPstar : star P = P)
    (hAstar : star A = A) :
    opVortexMassSq P A A =
      (4 : ℤ) • InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian.orbitMassMode P A := by
  change (4 : ℤ) • genV P A A =
    (4 : ℤ) • InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian.orbitMassMode P A
  rw [← InfoGeometry.OperatorAlgebra.YangMillsOrbitGramian.orbitMassMode_eq_peirce_genV
    hP hPstar hAstar]

/-- The 12th cyclotomic polynomial `Φ₁₂(X) = X⁴ - X² + 1` on `B`. -/
def opCyclotomicPhi12 (X : B) : B :=
  X ^ 4 - X ^ 2 + 1

/-- The 24th cyclotomic polynomial `Φ₂₄(X) = X⁸ - X⁴ + 1` on `B`. -/
def opCyclotomicPhi24 (X : B) : B :=
  X ^ 8 - X ^ 4 + 1

/--Mexican–hat / IHHS double-commutator mass lift operator `X ↦ -[Φ, [Φ, X]]`. -/
def opMexicanHatMassLift (P A C X : B) : B :=
  opHiggsMassOperator P A C X

variable {P : B} (hP : P * P = P)
include hP

/-- **Stage `YM₁` Theorem (`nilpotent_to_unipotent_exponential_group_laws`)**:
Over any associative ring `[Ring B]` with idempotent `P * P = P`:
1. The horizon nilpotents satisfy `conePlus P A * conePlus P A = 0` and
   `coneMinus P C * coneMinus P C = 0`,
2. Their truncated exponentials `opUnipotentPlus P A = 1 + conePlus P A` and
   `opUnipotentMinus P C = 1 - coneMinus P C` form exact additive one-parameter unipotent groups:
   `opUnipotentPlus P A₁ * opUnipotentPlus P A₂ = opUnipotentPlus P (A₁ + A₂)` and
   `opUnipotentMinus P C₁ * opUnipotentMinus P C₂ = opUnipotentMinus P (C₁ + C₂)`,
3. Each unipotent factor has an exact two-sided inverse given by sign negation of its generator:
   `opUnipotentPlus P A * opUnipotentPlus P (-A) = 1`,
   `opUnipotentPlus P (-A) * opUnipotentPlus P A = 1`,
   `opUnipotentMinus P C * opUnipotentMinus P (-C) = 1`, and
   `opUnipotentMinus P (-C) * opUnipotentMinus P C = 1`. -/
theorem nilpotent_to_unipotent_exponential_group_laws (A A₁ A₂ C C₁ C₂ : B) :
    conePlus P A * conePlus P A = 0 ∧
    coneMinus P C * coneMinus P C = 0 ∧
    opUnipotentPlus P A₁ * opUnipotentPlus P A₂ = opUnipotentPlus P (A₁ + A₂) ∧
    opUnipotentMinus P C₁ * opUnipotentMinus P C₂ = opUnipotentMinus P (C₁ + C₂) ∧
    opUnipotentPlus P A * opUnipotentPlus P (-A) = 1 ∧
    opUnipotentPlus P (-A) * opUnipotentPlus P A = 1 ∧
    opUnipotentMinus P C * opUnipotentMinus P (-C) = 1 ∧
    opUnipotentMinus P (-C) * opUnipotentMinus P C = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · peirce_nf hP
  · simp only [opUnipotentPlus]; peirce_nf hP
  · simp only [opUnipotentMinus]; peirce_nf hP
  · simp only [opUnipotentPlus]; peirce_nf hP
  · simp only [opUnipotentPlus]; peirce_nf hP
  · simp only [opUnipotentMinus]; peirce_nf hP
  · simp only [opUnipotentMinus]; peirce_nf hP

/-! ## 2. Stage `YM₂`: Fourfold Ordered Möbius–Bruhat Vortex Anatomy, Symmetric Coupling `V`, & Commutator Holonomy `-Σ` -/

/-- The forward condensate displacement `U₊(A) * U₋(C) - 1` expands to the axial current
`J₅ = N₊ - N₋` minus the upper Peirce cycle `qgtPlus P A C = N₊ * N₋ = P * V * P`. -/
theorem condensate_displacement_expand (A C : B) :
    opCondensateDisplacement P A C =
      conePlus P A - coneMinus P C - conePlus P A * coneMinus P C ∧
    opCondensateDisplacement P A C =
      genJ P A C - qgtPlus P A C ∧
    opCondensateDisplacement P A C =
      genJ P A C - peirce11 P (genV P A C) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [opCondensateDisplacement, opUnipotentPlus, opUnipotentMinus]
    noncomm_ring
  · simp only [opCondensateDisplacement, opUnipotentPlus, opUnipotentMinus, genJ, qgtPlus]
    noncomm_ring
  · simp only [opCondensateDisplacement, opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP

/-- The dual (backward-ordered) condensate displacement `U₋(C) * U₊(A) - 1` expands to the axial
current `J₅ = N₊ - N₋` minus the lower Peirce cycle `qgtMinus P A C = N₋ * N₊ = (1 - P) * V * (1 - P)`. -/
theorem condensate_displacement_dual_expand (A C : B) :
    opCondensateDisplacementDual P A C =
      conePlus P A - coneMinus P C - coneMinus P C * conePlus P A ∧
    opCondensateDisplacementDual P A C =
      genJ P A C - qgtMinus P A C ∧
    opCondensateDisplacementDual P A C =
      genJ P A C - peirce00 P (genV P A C) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [opCondensateDisplacementDual, opUnipotentPlus, opUnipotentMinus]
    noncomm_ring
  · simp only [opCondensateDisplacementDual, opUnipotentPlus, opUnipotentMinus, genJ, qgtMinus]
    noncomm_ring
  · simp only [opCondensateDisplacementDual, opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP

/-- The forward unipotent product `U₊(A) * U₋(C)` deviates from `1` by `J₅ - qgtPlus P A C`,
while the symmetrized sum of forward and backward displacements extracts the full two-sheet
quadratic coupling `V = N₊ N₋ + N₋ N₊` and their difference extracts the spin-vortex holonomy `-Σ`. -/
theorem unipotent_product_deviation (A C : B) :
    opUnipotentPlus P A * opUnipotentMinus P C =
      1 + conePlus P A - coneMinus P C - conePlus P A * coneMinus P C ∧
    opCondensateDisplacement P A C + opCondensateDisplacementDual P A C =
      (2 : ℤ) • genJ P A C - genV P A C ∧
    opCondensateDisplacement P A C - opCondensateDisplacementDual P A C =
      -genSig P A C ∧
    comm (opUnipotentPlus P A) (opUnipotentMinus P C) =
      -genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [opUnipotentPlus, opUnipotentMinus]
    noncomm_ring
  · simp only [opCondensateDisplacement, opCondensateDisplacementDual,
      opUnipotentPlus, opUnipotentMinus, genJ, genV, anticomm]
    noncomm_ring
  · simp only [opCondensateDisplacement, opCondensateDisplacementDual,
      opUnipotentPlus, opUnipotentMinus, genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  · simp only [opUnipotentPlus, opUnipotentMinus, genSig,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring

/-- **Stage `YM₂` Theorem (`fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance`)**:
1. Forward and backward condensate displacements separate the upper (`qgtPlus`) and lower
   (`qgtMinus`) Peirce cycles, while their sum and difference isolate `(2 : ℤ) • J - V` and `-Σ`,
2. `opMoebiusBruhatVortex P A C` and `opMoebiusBruhatVortexInv P A C` are exact two-sided inverses:
   `opMoebiusBruhatVortex P A C * opMoebiusBruhatVortexInv P A C = 1` and
   `opMoebiusBruhatVortexInv P A C * opMoebiusBruhatVortex P A C = 1`,
3. Conjugation by the ordered Möbius–Bruhat vortex preserves the idempotency of the cut `P`
   and leaves the two-sheet quadratic coupling `V = genV P A C` strictly invariant:
   `opMoebiusBruhatVortex P A C * genV P A C * opMoebiusBruhatVortexInv P A C = genV P A C`. -/
theorem fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance (A C : B) :
    opCondensateDisplacement P A C = genJ P A C - qgtPlus P A C ∧
    opCondensateDisplacementDual P A C = genJ P A C - qgtMinus P A C ∧
    opCondensateDisplacement P A C + opCondensateDisplacementDual P A C =
      (2 : ℤ) • genJ P A C - genV P A C ∧
    comm (opUnipotentPlus P A) (opUnipotentMinus P C) = -genSig P A C ∧
    opMoebiusBruhatVortex P A C * opMoebiusBruhatVortexInv P A C = 1 ∧
    opMoebiusBruhatVortexInv P A C * opMoebiusBruhatVortex P A C = 1 ∧
    (opMoebiusBruhatVortex P A C * P * opMoebiusBruhatVortexInv P A C) *
      (opMoebiusBruhatVortex P A C * P * opMoebiusBruhatVortexInv P A C) =
      opMoebiusBruhatVortex P A C * P * opMoebiusBruhatVortexInv P A C ∧
    opMoebiusBruhatVortex P A C * genV P A C * opMoebiusBruhatVortexInv P A C =
      genV P A C := by
  refine ⟨(condensate_displacement_expand hP A C).2.1,
    (condensate_displacement_dual_expand hP A C).2.1,
    (unipotent_product_deviation hP A C).2.1,
    (unipotent_product_deviation hP A C).2.2.2,
    ?_, ?_, ?_, ?_⟩
  · simp only [opMoebiusBruhatVortex, opMoebiusBruhatVortexInv,
      opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP
  · simp only [opMoebiusBruhatVortex, opMoebiusBruhatVortexInv,
      opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP
  · simp only [opMoebiusBruhatVortex, opMoebiusBruhatVortexInv,
      opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP
  · simp only [opMoebiusBruhatVortex, opMoebiusBruhatVortexInv,
      opUnipotentPlus, opUnipotentMinus]
    peirce_nf hP

/-! ## 3. Stage `YM₃`: Steinberg 3-Factor Braid Vortices, Maurer–Cartan Curvature `F = J + V`, & Self-Dual Yang–Mills -/

/-- **Stage `YM₃` Theorem (`steinberg_braid_vortices_and_maurer_cartan_self_dual_bianchi`)**:
1. **Steinberg 3-Factor Braid Vortices**:
   `steinbergBraid P A C = opUnipotentPlus P A * opUnipotentMinus P C * opUnipotentPlus P A`
   and `steinbergBraidDual P A C = opUnipotentMinus P C * opUnipotentPlus P A * opUnipotentMinus P C`
   satisfy:
   - `steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A`,
   - `steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C`,
   - `steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C`,
   - `steinbergBraid P A C + steinbergBraidInv P A C = (2 : ℤ) • (1 - genV P A C)`,
   - `steinbergBraid P A C * steinbergBraidInv P A C = 1` and
     `steinbergBraidInv P A C * steinbergBraid P A C = 1`.
2. **Peirce Maurer–Cartan Curvature & Self-Dual Yang–Mills Bianchi Identity**:
   - `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`,
   - `parityConj P (genV P A C) = genV P A C` (even metric curvature is self-dual) and
     `parityConj P (genJ P A C) = -genJ P A C` (odd axial curvature is anti-self-dual),
   - `peirceCovariantDeriv P A C (genV P A C) = 0` (exact covariant Bianchi / vacuum self-dual Yang–Mills identity). -/
theorem steinberg_braid_vortices_and_maurer_cartan_self_dual_bianchi (A C : B) :
    steinbergBraid P A C = weylJ P A C + (1 - genV P A C) * conePlus P A ∧
    steinbergBraidDual P A C = weylJ P A C - (1 - genV P A C) * coneMinus P C ∧
    steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C ∧
    steinbergBraid P A C + steinbergBraidInv P A C = (2 : ℤ) • (1 - genV P A C) ∧
    steinbergBraid P A C * steinbergBraidInv P A C = 1 ∧
    steinbergBraidInv P A C * steinbergBraid P A C = 1 ∧
    peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
    parityConj P (genV P A C) = genV P A C ∧
    parityConj P (genJ P A C) = -genJ P A C ∧
    peirceCovariantDeriv P A C (genV P A C) = 0 := by
  have hA16 := archetype_A16_cayley_weyl_steinberg_reflection hP A C
  have hDual := steinbergBraid_dual_expansion_and_difference hP A C
  have hInv := steinbergBraid_mul_inv hP A C
  have hMC := peirce_maurer_cartan_curvature_bianchi_and_self_dual_yang_mills hP A C 0 0
  exact ⟨hA16.2.2.2.2.2.2.2, hDual.1, hDual.2.1, hDual.2.2.1,
    hInv.1, hInv.2, hMC.2.2.1, hMC.2.2.2.2.2.1, hMC.2.2.2.2.2.2.1,
    hMC.2.2.2.2.2.2.2.2.2.1⟩

/-! ## 4. Stage `YM₄`: Mexican-Hat / IHHS Double-Commutator Vortex Mass Generation `m² = 4V` -/

/-- The vortex mass squared `m² = 4V = opVortexMassSq P A C` governs the axial vortex eigenvalue
`opHiggsMassOperator P A C (opAxial P A C) = -((4 : ℤ) • (opQuadraticCoupling P A C * opAxial P A C))`. -/
theorem vortex_mass_sq_axial_eigenvalue (A C : B) :
    opHiggsMassOperator P A C (opAxial P A C) =
      -((4 : ℤ) • (opQuadraticCoupling P A C * opAxial P A C)) :=
  (archetype_A5_klein_hadamard_spectra_and_partition hP A C (0 : B)).2.2.2.1

/-- The vortex mass squared `m² = 4V = opVortexMassSq P A C` governs the spin-dipole vortex eigenvalue
`opHiggsMassOperator P A C (opSpinDipole P A C) = -((4 : ℤ) • (opQuadraticCoupling P A C * opSpinDipole P A C))`. -/
theorem vortex_mass_sq_spin_dipole_eigenvalue (A C : B) :
    opHiggsMassOperator P A C (opSpinDipole P A C) =
      -((4 : ℤ) • (opQuadraticCoupling P A C * opSpinDipole P A C)) :=
  (archetype_A5_klein_hadamard_spectra_and_partition hP A C (0 : B)).2.2.2.2.1

/-- **Stage `YM₄` Theorem (`mexican_hat_ihhs_coupling_to_mass_lift`)**:
The Mexican-hat / IHHS double-commutator mass operator `opHiggsMassOperator P A C X = -[Φ, [Φ, X]]`:
1. Annihilates the Goldstone mode `opHiggsField P A C` (`Φ`) and the Higgs quadratic modulus
   `opHiggsVEVSq P A C` (`V`),
2. Lifts the two-sheet quadratic coupling `V = opQuadraticCoupling P A C` into the operatorial
   vortex mass squared `opVortexMassSq P A C = (4 : ℤ) • V` on both the axial vortex `J₅ = opAxial P A C`
   and the spin-dipole vortex `Σ = opSpinDipole P A C`:
   - `opHiggsMassOperator P A C (opAxial P A C) = -(opVortexMassSq P A C * opAxial P A C)`,
   - `opHiggsMassOperator P A C (opSpinDipole P A C) = -(opVortexMassSq P A C * opSpinDipole P A C)`,
3. Projects any linear combination `α • Φ + β • J₅` onto its massive axial vortex component
   `β • (-(opVortexMassSq P A C * opAxial P A C))`,
4. Scales quadratically (`(N * N) • opVortexMassSq P A C`) under `N`-fold coherent mode condensation
   `(N • A, N • C)`. -/
theorem mexican_hat_ihhs_coupling_to_mass_lift (A C : B) (α β N : ℤ) :
    opHiggsMassOperator P A C (opHiggsField P A C) = 0 ∧
    opHiggsMassOperator P A C (opHiggsVEVSq P A C) = 0 ∧
    opHiggsMassOperator P A C (opAxial P A C) =
      -(opVortexMassSq P A C * opAxial P A C) ∧
    opHiggsMassOperator P A C (opSpinDipole P A C) =
      -(opVortexMassSq P A C * opSpinDipole P A C) ∧
    opHiggsMassOperator P A C (α • opHiggsField P A C + β • opAxial P A C) =
      β • (-(opVortexMassSq P A C * opAxial P A C)) ∧
    opVortexMassSq P (N • A) (N • C) = (N * N) • opVortexMassSq P A C := by
  have hSpectral := archetype_A5_klein_hadamard_spectra_and_partition hP A C (0 : B)
  have hMPhi : opHiggsMassOperator P A C (opHiggsField P A C) = 0 := hSpectral.2.1
  have hMV : opHiggsMassOperator P A C (opHiggsVEVSq P A C) = 0 := hSpectral.2.2.1
  have hMJ :
      opHiggsMassOperator P A C (opAxial P A C) =
        -((4 : ℤ) • (opQuadraticCoupling P A C * opAxial P A C)) := hSpectral.2.2.2.1
  have hMSpin :
      opHiggsMassOperator P A C (opSpinDipole P A C) =
        -((4 : ℤ) • (opQuadraticCoupling P A C * opSpinDipole P A C)) := hSpectral.2.2.2.2.1
  have hMassJ :
      opHiggsMassOperator P A C (opAxial P A C) =
        -(opVortexMassSq P A C * opAxial P A C) := by
    rw [hMJ]
    dsimp [opVortexMassSq]
    rw [smul_mul_assoc]
  have hMassSpin :
      opHiggsMassOperator P A C (opSpinDipole P A C) =
        -(opVortexMassSq P A C * opSpinDipole P A C) := by
    rw [hMSpin]
    dsimp [opVortexMassSq]
    rw [smul_mul_assoc]
  have hLin :
      opHiggsMassOperator P A C (α • opHiggsField P A C + β • opAxial P A C) =
        α • opHiggsMassOperator P A C (opHiggsField P A C) +
        β • opHiggsMassOperator P A C (opAxial P A C) := by
    change -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
          (α • opHiggsField P A C + β • opAxial P A C)) =
      α • (-InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (opHiggsField P A C))) +
      β • (-InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C)
        (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (opAxial P A C)))
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
               smul_sub, smul_add, smul_neg, neg_sub]
    abel
  refine ⟨hMPhi, hMV, hMassJ, hMassSpin, ?_, ?_⟩
  · rw [hLin, hMPhi, hMassJ, smul_zero, zero_add]
  · dsimp [opVortexMassSq, opQuadraticCoupling, genV, anticomm, conePlus, coneMinus]
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
    rw [mul_comm (4 : ℤ) (N * N)]

/-! ## 5. Stage `YM₅`: Operator Cyclotomic `Φ₁₂`/`Φ₂₄` Vortex Reduction & Unipotent/Braid Equivariance -/

/-- Because `(opAxial P A C)² = -V` (`J₅² = -V`), the 12th cyclotomic polynomial `Φ₁₂(X) = X⁴ - X² + 1`
evaluated on the axial vortex `opAxial P A C` reduces to `V² + V + 1`. -/
theorem cyclotomic_phi12_on_axial (A C : B) :
    opCyclotomicPhi12 (opAxial P A C) =
      opQuadraticCoupling P A C ^ 2 + opQuadraticCoupling P A C + 1 := by
  have hJSq : opAxial P A C * opAxial P A C = -opQuadraticCoupling P A C :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.1
  have hJ2 : opAxial P A C ^ 2 = -opQuadraticCoupling P A C := by
    rw [sq, hJSq]
  have hJ4 : opAxial P A C ^ 4 = opQuadraticCoupling P A C ^ 2 := by
    calc
      opAxial P A C ^ 4 = (opAxial P A C ^ 2) ^ 2 := by noncomm_ring
      _ = (-opQuadraticCoupling P A C) ^ 2 := by rw [hJ2]
      _ = opQuadraticCoupling P A C ^ 2 := by noncomm_ring
  dsimp [opCyclotomicPhi12]
  rw [hJ4, hJ2]
  noncomm_ring

/-- Because `(opAxial P A C)² = -V` (`J₅⁴ = V²`), the 24th cyclotomic polynomial
`Φ₂₄(X) = X⁸ - X⁴ + 1` evaluated on the axial vortex `opAxial P A C` reduces to
`V⁴ - V² + 1 = opCyclotomicPhi12 (opQuadraticCoupling P A C)`. -/
theorem cyclotomic_phi24_on_axial (A C : B) :
    opCyclotomicPhi24 (opAxial P A C) =
      opQuadraticCoupling P A C ^ 4 - opQuadraticCoupling P A C ^ 2 + 1 ∧
    opCyclotomicPhi24 (opAxial P A C) =
      opCyclotomicPhi12 (opQuadraticCoupling P A C) := by
  have hJSq : opAxial P A C * opAxial P A C = -opQuadraticCoupling P A C :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP A C).2.2.2.1
  have hJ2 : opAxial P A C ^ 2 = -opQuadraticCoupling P A C := by
    rw [sq, hJSq]
  have hJ4 : opAxial P A C ^ 4 = opQuadraticCoupling P A C ^ 2 := by
    calc
      opAxial P A C ^ 4 = (opAxial P A C ^ 2) ^ 2 := by noncomm_ring
      _ = (-opQuadraticCoupling P A C) ^ 2 := by rw [hJ2]
      _ = opQuadraticCoupling P A C ^ 2 := by noncomm_ring
  have hJ8 : opAxial P A C ^ 8 = opQuadraticCoupling P A C ^ 4 := by
    calc
      opAxial P A C ^ 8 = (opAxial P A C ^ 4) ^ 2 := by noncomm_ring
      _ = (opQuadraticCoupling P A C ^ 2) ^ 2 := by rw [hJ4]
      _ = opQuadraticCoupling P A C ^ 4 := by noncomm_ring
  have hMain :
      opCyclotomicPhi24 (opAxial P A C) =
        opQuadraticCoupling P A C ^ 4 - opQuadraticCoupling P A C ^ 2 + 1 := by
    dsimp [opCyclotomicPhi24]
    rw [hJ8, hJ4]
  exact ⟨hMain, hMain⟩

/-- Because `(opSpinDipole P A C)² = V²` (`Σ² = V²`), the 12th cyclotomic polynomial
`Φ₁₂(X) = X⁴ - X² + 1` evaluated on the spin-dipole vortex `opSpinDipole P A C` equals
`V⁴ - V² + 1 = opCyclotomicPhi12 (opQuadraticCoupling P A C)` (and hence coincides with
`opCyclotomicPhi24 (opAxial P A C)`!). -/
theorem cyclotomic_phi12_on_spin_dipole (A C : B) :
    opCyclotomicPhi12 (opSpinDipole P A C) =
      opQuadraticCoupling P A C ^ 4 - opQuadraticCoupling P A C ^ 2 + 1 ∧
    opCyclotomicPhi12 (opSpinDipole P A C) =
      opCyclotomicPhi12 (opQuadraticCoupling P A C) ∧
    opCyclotomicPhi12 (opSpinDipole P A C) =
      opCyclotomicPhi24 (opAxial P A C) := by
  have hSigSq :
      opSpinDipole P A C * opSpinDipole P A C =
        opQuadraticCoupling P A C * opQuadraticCoupling P A C := by
    change genSig P A C * genSig P A C = genV P A C * genV P A C
    peirce_nf hP
  have hSig2 : opSpinDipole P A C ^ 2 = opQuadraticCoupling P A C ^ 2 := by
    rw [sq, sq, hSigSq]
  have hSig4 : opSpinDipole P A C ^ 4 = opQuadraticCoupling P A C ^ 4 := by
    calc
      opSpinDipole P A C ^ 4 = (opSpinDipole P A C ^ 2) ^ 2 := by noncomm_ring
      _ = (opQuadraticCoupling P A C ^ 2) ^ 2 := by rw [hSig2]
      _ = opQuadraticCoupling P A C ^ 4 := by noncomm_ring
  have hMain :
      opCyclotomicPhi12 (opSpinDipole P A C) =
        opQuadraticCoupling P A C ^ 4 - opQuadraticCoupling P A C ^ 2 + 1 := by
    dsimp [opCyclotomicPhi12]
    rw [hSig4, hSig2]
  exact ⟨hMain, hMain, hMain.trans (cyclotomic_phi24_on_axial hP A C).1.symm⟩

/-- Because `(opSpinDipole P A C)² = V²`, the 24th cyclotomic polynomial
`Φ₂₄(X) = X⁸ - X⁴ + 1` evaluated on the spin-dipole vortex `opSpinDipole P A C` equals
`V⁸ - V⁴ + 1 = opCyclotomicPhi24 (opQuadraticCoupling P A C)`. -/
theorem cyclotomic_phi24_on_spin_dipole (A C : B) :
    opCyclotomicPhi24 (opSpinDipole P A C) =
      opQuadraticCoupling P A C ^ 8 - opQuadraticCoupling P A C ^ 4 + 1 ∧
    opCyclotomicPhi24 (opSpinDipole P A C) =
      opCyclotomicPhi24 (opQuadraticCoupling P A C) := by
  have hSigSq :
      opSpinDipole P A C * opSpinDipole P A C =
        opQuadraticCoupling P A C * opQuadraticCoupling P A C := by
    change genSig P A C * genSig P A C = genV P A C * genV P A C
    peirce_nf hP
  have hSig2 : opSpinDipole P A C ^ 2 = opQuadraticCoupling P A C ^ 2 := by
    rw [sq, sq, hSigSq]
  have hSig4 : opSpinDipole P A C ^ 4 = opQuadraticCoupling P A C ^ 4 := by
    calc
      opSpinDipole P A C ^ 4 = (opSpinDipole P A C ^ 2) ^ 2 := by noncomm_ring
      _ = (opQuadraticCoupling P A C ^ 2) ^ 2 := by rw [hSig2]
      _ = opQuadraticCoupling P A C ^ 4 := by noncomm_ring
  have hSig8 : opSpinDipole P A C ^ 8 = opQuadraticCoupling P A C ^ 8 := by
    calc
      opSpinDipole P A C ^ 8 = (opSpinDipole P A C ^ 4) ^ 2 := by noncomm_ring
      _ = (opQuadraticCoupling P A C ^ 4) ^ 2 := by rw [hSig4]
      _ = opQuadraticCoupling P A C ^ 8 := by noncomm_ring
  have hMain :
      opCyclotomicPhi24 (opSpinDipole P A C) =
        opQuadraticCoupling P A C ^ 8 - opQuadraticCoupling P A C ^ 4 + 1 := by
    dsimp [opCyclotomicPhi24]
    rw [hSig8, hSig4]
  exact ⟨hMain, hMain⟩

/-- **Stage `YM₅` Theorem (`cyclotomic_vortex_locking_and_unipotent_braid_equivariance`)**:
1. **Cross-Sector Cyclotomic Bridge (`Φ₁₂(Σ) = Φ₂₄(J₅) = Φ₁₂(V)`)**:
   `opCyclotomicPhi12 (opSpinDipole P A C) = opCyclotomicPhi24 (opAxial P A C)` and both equal
   `opCyclotomicPhi12 (opQuadraticCoupling P A C)`,
2. **Exact Equivariance under Ordered Möbius–Bruhat Vortex Conjugation & Steinberg Braids**:
   For any `X : B`,
   - `opCyclotomicPhi12 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) (opCyclotomicPhi12 X)`,
   - `opCyclotomicPhi24 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) (opCyclotomicPhi24 X)`,
   - `opCyclotomicPhi12 (symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) X) = symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) (opCyclotomicPhi12 X)`,
   - `opCyclotomicPhi24 (symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) X) = symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) (opCyclotomicPhi24 X)`,
3. **Cyclotomic Root Locking (`W₁₂` and `W₂₄`)**:
   - `opCyclotomicPhi12 X = 0 → X ^ 6 = -1 ∧ X ^ 12 = 1 ∧ opCyclotomicPhi12 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = 0`,
   - `opCyclotomicPhi24 X = 0 → X ^ 12 = -1 ∧ X ^ 24 = 1 ∧ opCyclotomicPhi24 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = 0`. -/
theorem cyclotomic_vortex_locking_and_unipotent_braid_equivariance (A C X : B) :
    opCyclotomicPhi12 (opSpinDipole P A C) = opCyclotomicPhi24 (opAxial P A C) ∧
    opCyclotomicPhi12 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) =
      symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) (opCyclotomicPhi12 X) ∧
    opCyclotomicPhi24 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) =
      symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) (opCyclotomicPhi24 X) ∧
    opCyclotomicPhi12 (symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) X) =
      symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) (opCyclotomicPhi12 X) ∧
    opCyclotomicPhi24 (symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) X) =
      symmetrySandwich (steinbergBraid P A C) (steinbergBraidInv P A C) (opCyclotomicPhi24 X) ∧
    (opCyclotomicPhi12 X = 0 →
      X ^ 6 = -1 ∧ X ^ 12 = 1 ∧
      opCyclotomicPhi12 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = 0) ∧
    (opCyclotomicPhi24 X = 0 →
      X ^ 12 = -1 ∧ X ^ 24 = 1 ∧
      opCyclotomicPhi24 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = 0) := by
  have hMB := fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance hP A C
  have hMB_GG : opMoebiusBruhatVortex P A C * opMoebiusBruhatVortexInv P A C = 1 := hMB.2.2.2.2.1
  have hMB_GiG : opMoebiusBruhatVortexInv P A C * opMoebiusBruhatVortex P A C = 1 := hMB.2.2.2.2.2.1
  have hSB := steinbergBraid_mul_inv hP A C
  have hCycMB :=
    w12_w24_cyclotomic_operator_galois_conjugates_and_symmetry_invariance hMB_GG hMB_GiG X
  have hCycSB :=
    w12_w24_cyclotomic_operator_galois_conjugates_and_symmetry_invariance hSB.1 hSB.2 X
  refine ⟨(cyclotomic_phi12_on_spin_dipole hP A C).2.2,
    hCycMB.1 X, hCycMB.2.1 X, hCycSB.1 X, hCycSB.2.1 X, ?_, ?_⟩
  · intro h12
    have hLock := hCycMB.2.2.1 h12
    exact ⟨hLock.1, hLock.2.1, hLock.2.2.2.2.2.1⟩
  · intro h24
    have hLock := hCycMB.2.2.2 h24
    exact ⟨hLock.1, hLock.2.1, hLock.2.2.2.2.2.2.2.2.2.1⟩

end RingIdentities

/-! ## 6. Stage `YM₆`: Functorial `StarRingHom` Transport, Inductive Colimit Vortex Mass Lift, & Multi-Channel Decoupling -/

section ColimitAndMultiChannel

/-- **Stage `YM₆.1` (`starRingHom_intertwines_unipotent_condensate_and_vortex_mass`)**:
Every unital ring homomorphism `φ : B₁ →+* B₂` between operator rings strictly intertwines
`opUnipotentPlus`, `opUnipotentMinus`, `opMoebiusBruhatVortex`, `opCondensateDisplacement`,
`opCondensateDisplacementDual`, `opVortexMassSq`, `opCyclotomicPhi12`, and `opCyclotomicPhi24`. -/
theorem ringHom_intertwines_unipotent_condensate_and_vortex_mass
    {B₁ B₂ : Type*} [Ring B₁] [Ring B₂]
    (φ : B₁ →+* B₂) (P A C X : B₁) :
    φ (opUnipotentPlus P A) = opUnipotentPlus (φ P) (φ A) ∧
    φ (opUnipotentMinus P C) = opUnipotentMinus (φ P) (φ C) ∧
    φ (opMoebiusBruhatVortex P A C) = opMoebiusBruhatVortex (φ P) (φ A) (φ C) ∧
    φ (opCondensateDisplacement P A C) = opCondensateDisplacement (φ P) (φ A) (φ C) ∧
    φ (opCondensateDisplacementDual P A C) = opCondensateDisplacementDual (φ P) (φ A) (φ C) ∧
    φ (opVortexMassSq P A C) = opVortexMassSq (φ P) (φ A) (φ C) ∧
    φ (opCyclotomicPhi12 X) = opCyclotomicPhi12 (φ X) ∧
    φ (opCyclotomicPhi24 X) = opCyclotomicPhi24 (φ X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [opUnipotentPlus, conePlus, map_add, map_one, map_mul, map_sub]
  · simp only [opUnipotentMinus, coneMinus, map_sub, map_one, map_mul]
  · simp only [opMoebiusBruhatVortex, opUnipotentPlus, opUnipotentMinus,
      conePlus, coneMinus, map_mul, map_add, map_sub, map_one]
  · simp only [opCondensateDisplacement, opUnipotentPlus, opUnipotentMinus,
      conePlus, coneMinus, map_sub, map_mul, map_add, map_one]
  · simp only [opCondensateDisplacementDual, opUnipotentPlus, opUnipotentMinus,
      conePlus, coneMinus, map_sub, map_mul, map_add, map_one]
  · simp only [opVortexMassSq, opQuadraticCoupling, genV, anticomm,
      conePlus, coneMinus, map_zsmul, map_add, map_mul, map_sub, map_one]
  · simp only [opCyclotomicPhi12, map_add, map_sub, map_pow, map_one]
  · simp only [opCyclotomicPhi24, map_add, map_sub, map_pow, map_one]

/-- **Stage `YM₆.2` (`colimit_condensate_vortex_mass_renormalization_invariance`)**:
In any `InductiveStarColimitCone A A_inf`, the unipotent condensate displacement
`opCondensateDisplacement`, the vortex mass squared `opVortexMassSq`, and the Mexican-hat
vortex mass eigenvalue equations on `opAxial` and `opSpinDipole` are strictly scale-invariant
across `m` renormalization steps (`k → k + m → ∞`). -/
theorem colimit_condensate_vortex_mass_renormalization_invariance
    {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, StarRing (A k)]
    {A_inf : Type*} [Ring A_inf] [StarRing A_inf]
    (Cone : InductiveStarColimitCone A A_inf)
    (k m : ℕ) (P_k A_k C_k : A k) (hP_k : P_k * P_k = P_k) :
    let ψ_m := (stepHomIter Cone k m).toRingHom
    let ι_km := (Cone.toColimit (k + m)).toRingHom
    let ι_k := (Cone.toColimit k).toRingHom
    let P_inf := ι_k P_k
    let A_inf := ι_k A_k
    let C_inf := ι_k C_k
    ι_km (opCondensateDisplacement (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
      opCondensateDisplacement P_inf A_inf C_inf ∧
    ι_km (opVortexMassSq (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
      opVortexMassSq P_inf A_inf C_inf ∧
    opHiggsMassOperator P_inf A_inf C_inf (opAxial P_inf A_inf C_inf) =
      -(opVortexMassSq P_inf A_inf C_inf * opAxial P_inf A_inf C_inf) ∧
    opHiggsMassOperator P_inf A_inf C_inf (opSpinDipole P_inf A_inf C_inf) =
      -(opVortexMassSq P_inf A_inf C_inf * opSpinDipole P_inf A_inf C_inf) := by
  intro ψ_m ι_km ι_k P_inf A_inf C_inf
  have hP_inf : P_inf * P_inf = P_inf := by
    dsimp [P_inf, ι_k]; rw [← map_mul, hP_k]
  have hCocycle := (colimit_renormalization_scale_invariance Cone k m P_k A_k C_k 0).1
  have hHom_m := ringHom_intertwines_unipotent_condensate_and_vortex_mass ψ_m P_k A_k C_k 0
  have hHom_k := ringHom_intertwines_unipotent_condensate_and_vortex_mass ι_k P_k A_k C_k 0
  have hLift := mexican_hat_ihhs_coupling_to_mass_lift hP_inf A_inf C_inf 0 0 1
  refine ⟨?_, ?_, hLift.2.2.1, hLift.2.2.2.1⟩
  · calc
      ι_km (opCondensateDisplacement (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
          ι_km (ψ_m (opCondensateDisplacement P_k A_k C_k)) :=
        congr_arg ι_km hHom_m.2.2.2.1.symm
      _ = ι_k (opCondensateDisplacement P_k A_k C_k) := hCocycle _
      _ = opCondensateDisplacement P_inf A_inf C_inf := hHom_k.2.2.2.1
  · calc
      ι_km (opVortexMassSq (ψ_m P_k) (ψ_m A_k) (ψ_m C_k)) =
          ι_km (ψ_m (opVortexMassSq P_k A_k C_k)) :=
        congr_arg ι_km hHom_m.2.2.2.2.2.1.symm
      _ = ι_k (opVortexMassSq P_k A_k C_k) := hCocycle _
      _ = opVortexMassSq P_inf A_inf C_inf := hHom_k.2.2.2.2.2.1

/-- **Stage `YM₆.3` (`multi_channel_orthogonal_vortex_mass_additivity_and_decoupling`)**:
For mutually orthogonal two-sheet channels `(A₁, C₁)` and `(A₂, C₂)` over an idempotent `P`:
1. The vortex mass squared is strictly additive across channels:
   `opVortexMassSq P (A₁ + A₂) (C₁ + C₂) = opVortexMassSq P A₁ C₁ + opVortexMassSq P A₂ C₂`,
2. The channel vortex mass operators mutually annihilate:
   `opVortexMassSq P A₁ C₁ * opVortexMassSq P A₂ C₂ = 0` and
   `opVortexMassSq P A₂ C₂ * opVortexMassSq P A₁ C₁ = 0`. -/
theorem multi_channel_orthogonal_vortex_mass_additivity_and_decoupling
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A₁ C₁ A₂ C₂ : B)
    (h12 : opZig P A₁ * opZag P C₂ = 0)
    (h21 : opZig P A₂ * opZag P C₁ = 0)
    (h12' : opZag P C₁ * opZig P A₂ = 0)
    (h21' : opZag P C₂ * opZig P A₁ = 0) :
    opVortexMassSq P (A₁ + A₂) (C₁ + C₂) =
      opVortexMassSq P A₁ C₁ + opVortexMassSq P A₂ C₂ ∧
    opVortexMassSq P A₁ C₁ * opVortexMassSq P A₂ C₂ = 0 ∧
    opVortexMassSq P A₂ C₂ * opVortexMassSq P A₁ C₁ = 0 := by
  have hZigAdd : opZig P (A₁ + A₂) = opZig P A₁ + opZig P A₂ := by
    unfold opZig conePlus; simp only [mul_add, add_mul]
  have hZagAdd : opZag P (C₁ + C₂) = opZag P C₁ + opZag P C₂ := by
    unfold opZag coneMinus; simp only [mul_add, add_mul]
  have hZigZag : ∀ X Y : B, opZig P X * (opZig P Y * opZag P C₂) = 0 ∧
      opZig P X * (opZig P Y * opZag P C₁) = 0 ∧
      opZag P X * (opZag P Y * opZig P A₂) = 0 ∧
      opZag P X * (opZag P Y * opZig P A₁) = 0 := by
    intro X Y
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold opZig opZag; peirce_nf hP)
  have hVAdd :
      opQuadraticCoupling P (A₁ + A₂) (C₁ + C₂) =
        opQuadraticCoupling P A₁ C₁ + opQuadraticCoupling P A₂ C₂ := by
    change anticomm (opZig P (A₁ + A₂)) (opZag P (C₁ + C₂)) =
      anticomm (opZig P A₁) (opZag P C₁) + anticomm (opZig P A₂) (opZag P C₂)
    unfold anticomm
    rw [hZigAdd, hZagAdd]
    simp only [add_mul, mul_add, h12, h21, h12', h21']
    abel
  have hV12 : opQuadraticCoupling P A₁ C₁ * opQuadraticCoupling P A₂ C₂ = 0 := by
    change (opZig P A₁ * opZag P C₁ + opZag P C₁ * opZig P A₁) *
      (opZig P A₂ * opZag P C₂ + opZag P C₂ * opZig P A₂) = 0
    have hZ := hZigZag A₁ A₂
    have hZ' := hZigZag C₁ C₂
    have h12a : opZig P A₁ * (opZag P C₂ * opZig P A₂) = 0 := by
      rw [← mul_assoc, h12, zero_mul]
    have h12'a : opZag P C₁ * (opZig P A₂ * opZag P C₂) = 0 := by
      rw [← mul_assoc, h12', zero_mul]
    simp only [add_mul, mul_add, mul_assoc, hZ.1, hZ'.2.2.1, h12a, h12'a,
      mul_zero, add_zero]
  have hV21 : opQuadraticCoupling P A₂ C₂ * opQuadraticCoupling P A₁ C₁ = 0 := by
    change (opZig P A₂ * opZag P C₂ + opZag P C₂ * opZig P A₂) *
      (opZig P A₁ * opZag P C₁ + opZag P C₁ * opZig P A₁) = 0
    have hZ := hZigZag A₂ A₁
    have hZ' := hZigZag C₂ C₁
    have h21a : opZig P A₂ * (opZag P C₁ * opZig P A₁) = 0 := by
      rw [← mul_assoc, h21, zero_mul]
    have h21'a : opZag P C₂ * (opZig P A₁ * opZag P C₁) = 0 := by
      rw [← mul_assoc, h21', zero_mul]
    simp only [add_mul, mul_add, mul_assoc, hZ.2.1, hZ'.2.2.2, h21a, h21'a,
      mul_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [opVortexMassSq]
    rw [hVAdd, smul_add]
  · dsimp [opVortexMassSq]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hV12, smul_zero]
  · dsimp [opVortexMassSq]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hV21, smul_zero]

end ColimitAndMultiChannel

/-! ## 7. Stage `YM₇`: Concrete `2 × 2` Non-Commutative Matrix Vortex Witness (`T16` / `T17`) & Master Synthesis -/

/-- Concrete `2 × 2` integer projector `P = E₀₀ = !![1, 0; 0, 0]`. -/
def ymMatrixP : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Concrete `2 × 2` upper-corner nilpotent generator `A = E₀₁ = !![0, 1; 0, 0]`. -/
def ymMatrixA : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- Concrete `2 × 2` lower-corner nilpotent generator `C = E₁₀ = !![0, 0; 1, 0]`. -/
def ymMatrixC : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- **Concrete `2 × 2` Non-Commutative Matrix Vortex Witness (`ym_matrix_vortex_noncomm_and_nonzero_mass_witness`)**:
Certifies in `Matrix (Fin 2) (Fin 2) ℤ` that:
1. `ymMatrixP * ymMatrixP = ymMatrixP` (idempotent cut),
2. `ymMatrixA * ymMatrixC ≠ ymMatrixC * ymMatrixA` (non-commutativity `T16`),
3. `comm (opUnipotentPlus ymMatrixP ymMatrixA) (opUnipotentMinus ymMatrixP ymMatrixC) ≠ 0`
   (non-commuting unipotent vortex holonomy),
4. `opCondensateDisplacement ymMatrixP ymMatrixA ymMatrixC ≠ 0` (non-vanishing condensate displacement),
5. `opVortexMassSq ymMatrixP ymMatrixA ymMatrixC = !![4, 0; 0, 4]` and
   `opVortexMassSq ymMatrixP ymMatrixA ymMatrixC ≠ 0` (non-vanishing vortex mass squared `m² = 4V`),
6. `opHiggsMassOperator ymMatrixP ymMatrixA ymMatrixC (opAxial ymMatrixP ymMatrixA ymMatrixC) ≠ 0`
   and `opHiggsMassOperator ymMatrixP ymMatrixA ymMatrixC (opSpinDipole ymMatrixP ymMatrixA ymMatrixC) ≠ 0`
   (non-vanishing axial and spin-dipole vortex mass action `T17`). -/
theorem ym_matrix_vortex_noncomm_and_nonzero_mass_witness :
    ymMatrixP * ymMatrixP = ymMatrixP ∧
    ymMatrixA * ymMatrixC ≠ ymMatrixC * ymMatrixA ∧
    comm (opUnipotentPlus ymMatrixP ymMatrixA) (opUnipotentMinus ymMatrixP ymMatrixC) ≠ 0 ∧
    opCondensateDisplacement ymMatrixP ymMatrixA ymMatrixC ≠ 0 ∧
    opVortexMassSq ymMatrixP ymMatrixA ymMatrixC = !![(4 : ℤ), 0; 0, 4] ∧
    opVortexMassSq ymMatrixP ymMatrixA ymMatrixC ≠ 0 ∧
    opHiggsMassOperator ymMatrixP ymMatrixA ymMatrixC
      (opAxial ymMatrixP ymMatrixA ymMatrixC) ≠ 0 ∧
    opHiggsMassOperator ymMatrixP ymMatrixA ymMatrixC
      (opSpinDipole ymMatrixP ymMatrixA ymMatrixC) ≠ 0 := by
  decide

/-- **Stage `YM₇` Master Synthesis (`two_sheeted_nilpotent_condensate_vortex_mass_master_synthesis`)**:
Coagulates the complete 7-stage Acyclic Causal Poset
`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇` over any non-commutative ring `[Ring B]` with
idempotent `P * P = P`:
1. **Strict 7-Stage Causal Chain (`YM₁ ≺ YM₂ ≺ YM₃ ≺ YM₄ ≺ YM₅ ≺ YM₆ ≺ YM₇`)**,
2. **Nilpotent-to-Unipotent Exponential Condensation (`YM₁`)**:
   `opUnipotentPlus P A₁ * opUnipotentPlus P A₂ = opUnipotentPlus P (A₁ + A₂)` and
   `opUnipotentMinus P C₁ * opUnipotentMinus P C₂ = opUnipotentMinus P (C₁ + C₂)`,
3. **Fourfold Ordered Möbius–Bruhat Vortex Anatomy & Metric Invariance (`YM₂`)**:
   `opCondensateDisplacement P A C + opCondensateDisplacementDual P A C = (2 : ℤ) • genJ P A C - genV P A C`,
   `comm (opUnipotentPlus P A) (opUnipotentMinus P C) = -genSig P A C`,
   `opMoebiusBruhatVortex P A C * opMoebiusBruhatVortexInv P A C = 1`, and
   `opMoebiusBruhatVortex P A C * genV P A C * opMoebiusBruhatVortexInv P A C = genV P A C`,
4. **Steinberg 3-Factor Braid Vortices & Maurer–Cartan Self-Dual Yang–Mills (`YM₃`)**:
   `steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C`,
   `peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C`, and
   `peirceCovariantDeriv P A C (genV P A C) = 0`,
5. **Mexican-Hat / IHHS Vortex Mass Generation `m² = 4V` (`YM₄`)**:
   `opHiggsMassOperator P A C (opHiggsField P A C) = 0`,
   `opHiggsMassOperator P A C (opHiggsVEVSq P A C) = 0`,
   `opHiggsMassOperator P A C (opAxial P A C) = -(opVortexMassSq P A C * opAxial P A C)`, and
   `opHiggsMassOperator P A C (opSpinDipole P A C) = -(opVortexMassSq P A C * opSpinDipole P A C)`,
6. **Cyclotomic `Φ₁₂`/`Φ₂₄` Vortex Locking & Möbius–Bruhat Equivariance (`YM₅`)**:
   `opCyclotomicPhi12 (opAxial P A C) = opQuadraticCoupling P A C ^ 2 + opQuadraticCoupling P A C + 1`,
   `opCyclotomicPhi12 (opSpinDipole P A C) = opCyclotomicPhi24 (opAxial P A C)`, and
   `opCyclotomicPhi12 (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) = symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) (opCyclotomicPhi12 X)`,
7. **Non-Commutative `2 × 2` Matrix Vortex Witness (`YM₇`)**:
   `comm (opUnipotentPlus ymMatrixP ymMatrixA) (opUnipotentMinus ymMatrixP ymMatrixC) ≠ 0` and
   `opVortexMassSq ymMatrixP ymMatrixA ymMatrixC ≠ 0`. -/
theorem two_sheeted_nilpotent_condensate_vortex_mass_master_synthesis
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A A₁ A₂ C C₁ C₂ X : B) :
    (TwoSheetedCondensateVortexStage.causalEdge
       .ym1_nilpotentToUnipotentCut .ym2_fourfoldMoebiusBruhatVortexAnatomy ∧
     TwoSheetedCondensateVortexStage.causalEdge
       .ym2_fourfoldMoebiusBruhatVortexAnatomy .ym3_steinbergBraidAndMaurerCartanSelfDual ∧
     TwoSheetedCondensateVortexStage.causalEdge
       .ym3_steinbergBraidAndMaurerCartanSelfDual .ym4_mexicanHatIhhsVortexMassGeneration ∧
     TwoSheetedCondensateVortexStage.causalEdge
       .ym4_mexicanHatIhhsVortexMassGeneration .ym5_cyclotomicVortexLockingAndEquivariance ∧
     TwoSheetedCondensateVortexStage.causalEdge
       .ym5_cyclotomicVortexLockingAndEquivariance .ym6_inductiveColimitAndMultiChannelVortexDescent ∧
     TwoSheetedCondensateVortexStage.causalEdge
       .ym6_inductiveColimitAndMultiChannelVortexDescent .ym7_masterCondensateVortexSynthesisAndMatrixWitness) ∧
    (opUnipotentPlus P A₁ * opUnipotentPlus P A₂ = opUnipotentPlus P (A₁ + A₂) ∧
     opUnipotentMinus P C₁ * opUnipotentMinus P C₂ = opUnipotentMinus P (C₁ + C₂)) ∧
    (opCondensateDisplacement P A C + opCondensateDisplacementDual P A C =
       (2 : ℤ) • genJ P A C - genV P A C ∧
     comm (opUnipotentPlus P A) (opUnipotentMinus P C) = -genSig P A C ∧
     opMoebiusBruhatVortex P A C * opMoebiusBruhatVortexInv P A C = 1 ∧
     opMoebiusBruhatVortex P A C * genV P A C * opMoebiusBruhatVortexInv P A C = genV P A C) ∧
    (steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C ∧
     peirceMaurerCartanCurvature P A C = genJ P A C + genV P A C ∧
     peirceCovariantDeriv P A C (genV P A C) = 0) ∧
    (opHiggsMassOperator P A C (opHiggsField P A C) = 0 ∧
     opHiggsMassOperator P A C (opHiggsVEVSq P A C) = 0 ∧
     opHiggsMassOperator P A C (opAxial P A C) = -(opVortexMassSq P A C * opAxial P A C) ∧
     opHiggsMassOperator P A C (opSpinDipole P A C) = -(opVortexMassSq P A C * opSpinDipole P A C)) ∧
    (opCyclotomicPhi12 (opAxial P A C) =
       opQuadraticCoupling P A C ^ 2 + opQuadraticCoupling P A C + 1 ∧
     opCyclotomicPhi12 (opSpinDipole P A C) = opCyclotomicPhi24 (opAxial P A C) ∧
     opCyclotomicPhi12
         (symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C) X) =
       symmetrySandwich (opMoebiusBruhatVortex P A C) (opMoebiusBruhatVortexInv P A C)
         (opCyclotomicPhi12 X)) ∧
    (comm (opUnipotentPlus ymMatrixP ymMatrixA) (opUnipotentMinus ymMatrixP ymMatrixC) ≠ 0 ∧
     opVortexMassSq ymMatrixP ymMatrixA ymMatrixC ≠ 0) := by
  have hYM1 := nilpotent_to_unipotent_exponential_group_laws hP A A₁ A₂ C C₁ C₂
  have hYM2 := fourfold_moebius_bruhat_vortex_anatomy_and_metric_invariance hP A C
  have hYM3 := steinberg_braid_vortices_and_maurer_cartan_self_dual_bianchi hP A C
  have hYM4 := mexican_hat_ihhs_coupling_to_mass_lift hP A C 0 0 1
  have hYM5 := cyclotomic_vortex_locking_and_unipotent_braid_equivariance hP A C X
  have hYM7 := ym_matrix_vortex_noncomm_and_nonzero_mass_witness
  exact ⟨TwoSheetedCondensateVortexStage.poset_chain_and_acyclicity.1,
    ⟨hYM1.2.2.1, hYM1.2.2.2.1⟩,
    ⟨hYM2.2.2.1, hYM2.2.2.2.1, hYM2.2.2.2.2.1, hYM2.2.2.2.2.2.2.2⟩,
    ⟨hYM3.2.2.1, hYM3.2.2.2.2.2.2.1, hYM3.2.2.2.2.2.2.2.2.2⟩,
    ⟨hYM4.1, hYM4.2.1, hYM4.2.2.1, hYM4.2.2.2.1⟩,
    ⟨cyclotomic_phi12_on_axial hP A C, hYM5.1, hYM5.2.1⟩,
    ⟨hYM7.2.2.1, hYM7.2.2.2.2.2.1⟩⟩

end InfoGeometry.Canonical.TwoSheetedNilpotentCondensateVortexMass
