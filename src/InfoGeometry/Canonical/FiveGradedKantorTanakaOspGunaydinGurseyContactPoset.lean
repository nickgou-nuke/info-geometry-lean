/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import InfoGeometry.OperatorAlgebra.PeirceSpine.ParaKahlerBregmanModularNoetherPoset
import InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset

/-!
# The 6-Stage 5-Graded Kantor–Tanaka Contact Super-Tower, `𝔬𝔰𝔭(1|2)` Superconformal Closure, & Günaydin–Gürsey `𝔤𝔩₁(R)_H ⊕ 𝔰𝔩₃(R)_color` Poset (`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ ⋯ ≺ 𝔎𝔗₆`)

This canonical module formalizes the epistemic compilation (`solve et coagula`) of the
**5-Graded Kantor–Tanaka Contact Super-Tower, `𝔬𝔰𝔭(1|2)` Superconformal Closure, and
Günaydin–Gürsey `𝔤𝔩₁(R)_H ⊕ 𝔰𝔩₃(R)_color` Split-Octonion Color Decomposition**
(`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`), together with its bridge to the
**6-Stage Metriplectic Zorn Three-Channel Product & Volume Duality Poset**
(`𝔐ℨ₁ ≺ 𝔐ℨ₂ ≺ {𝔐ℨ₃, 𝔐ℨ₄} ≺ 𝔐ℨ₅ ≺ 𝔐ℨ₆`):

1. **Rung 0 & Stage `𝔎𝔗₁` (`stage_KT1_derivation_eigenvalue_doubling_and_peirce_cubic_aporia`)**:
   - **Eigenvalue Doubling under Derivations**:
     For any ring `B` and derivation `D : B →+ B` (`∀ x y, D (x * y) = D x * y + x * D y`),
     if `D Q_{+1} = Q_{+1}` and `D Q_{-1} = -Q_{-1}`, then their symmetric anticommutators
     jump to eigenvalue `±2`:
     $$D(\{Q_{+1}, Q_{+1}\}) = 2\,\{Q_{+1}, Q_{+1}\}, \qquad
       D(\{Q_{-1}, Q_{-1}\}) = -2\,\{Q_{-1}, Q_{-1}\}, \qquad
       D(\{Q_{+1}, Q_{-1}\}) = 0.$$
   - **The Socratic Aporia of 3-Graded Peirce Tripotency**:
     The 3-graded Peirce operator $\mathcal{D}_3(D) := D^3 - D$ annihilates Grades $-1, 0, +1$,
     but on the Grade-$\pm 2$ contact shell (`D E_{±2} = ±2 • E_{±2}`) it evaluates to:
     $$(D^3 - D)(E_{+2}) = 6 \bullet E_{+2}, \qquad
       (D^3 - D)(E_{-2}) = -6 \bullet E_{-2}, \qquad
       D\big((D^3 - D)(E_{\pm 2})\big) = 12 \bullet E_{\pm 2}.$$

2. **Stage `𝔎𝔗₂` (`stage_KT2_factored_quintic_contact_law`)**:
   - Multiplying the 3-graded Peirce operator $\mathcal{D}_3(D) = D^3 - D$ by the contact-shell
     annihilator $D^2 - 4I$ yields the **Factored 5-Graded Quintic Contact Law**:
     $$(D^2 - 4I)(D^3 - D) = D^5 - 5 D^3 + 4 D = 0$$
     on every 5-graded sum $X = X_{-2} + X_{-1} + X_0 + X_{+1} + X_{+2}$, on $M_3(R)$ under
     $\mathrm{ad}_H$, and on `cornerOperatorSum P A C` under `charge P`.

3. **Stage `𝔎𝔗₃` (`stage_KT3_orthogonal_quartic_lagrange_projectors`)**:
   - The three integer-scaled quartic Lagrange shell projectors:
     $$\widetilde{\Pi}_0(D) = 12I - 15 D^2 + 3 D^4, \quad
       \widetilde{\Pi}_{\pm 1}(D) = 16 D^2 - 4 D^4, \quad
       \widetilde{\Pi}_{\pm 2}(D) = D^4 - D^2 = D(D^3 - D)$$
     satisfy $\widetilde{\Pi}_0 + \widetilde{\Pi}_{\pm 1} + \widetilde{\Pi}_{\pm 2} = 12 I$
     universally, isolate $(12 X_0, 12(X_{-1} + X_{+1}), 12(X_{-2} + X_{+2}))$, and satisfy
     scaled idempotency and mutual orthogonality, while the signed projectors isolate each of
     the five individual grades $\mathfrak{g}_{-2}, \mathfrak{g}_{-1}, \mathfrak{g}_0,
     \mathfrak{g}_{+1}, \mathfrak{g}_{+2}$.

4. **Stage `𝔎𝔗₄` (`stage_KT4_osp12_superconformal_contact_and_graded_jacobi_closure`)**:
   - Universal associative odd-odd-odd super-Jacobi identity
     $[Q_1, \{Q_2, Q_3\}] + [Q_2, \{Q_3, Q_1\}] + [Q_3, \{Q_1, Q_2\}] = 0$ and its explicit
     $\mathfrak{osp}(1|2)$ contact balance:
     $$2\,[Q_{+1}, \{Q_{+1}, Q_{-1}\}] + [Q_{-1}, \{Q_{+1}, Q_{+1}\}] =
       -2\,Q_{+1} + 2\,Q_{+1} = 0.$$

5. **Stage `𝔎𝔗₅` (`stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition`)**:
   - Exact orthogonal direct-sum decomposition of $\mathfrak{gl}_3(R) = M_3(R)$ into the
     1D baryon/contact grading line $\mathfrak{gl}_1(R)_H$ (`gl1BaryonScaledProj`) and the
     8D traceless color gluon algebra $\mathfrak{sl}_3(R)_{\text{color}}$ (`sl3ColorScaledProj`),
     with $[\mathfrak{gl}_3, \mathfrak{gl}_3] \subseteq \mathfrak{sl}_3$ and
     $[\mathfrak{gl}_1, \mathfrak{sl}_3] = 0$.

6. **Stage `𝔎𝔗₆` (`stage_KT6_bilateral_kantor_sandwich_and_five_graded_extraction`)**:
   - In any associative ring `B` with idempotent `P * P = P`, the Grade-$0$ Kantor cross-sandwich
     `kantorG0(X) = N_+ X N_- + N_- X N_+` and the Grade-$\pm 2$ extremal sandwiches
     `kantorGp2(X) = N_+ X N_+`, `kantorGm2(X) = N_- X N_-` satisfy the **Bilateral Kantor
     Sandwich Closure Identities**:
     $$\mathrm{kantorG0}^2(X) - \{\mathrm{kantorGp2}, \mathrm{kantorGm2}\}(X) = \Sigma\,X\,\Sigma,$$
     $$\mathrm{kantorG0}^2(X) + \{\mathrm{kantorGp2}, \mathrm{kantorGm2}\}(X) = V\,X\,V.$$
-/

namespace InfoGeometry.Canonical.FiveGradedKantorTanakaOspGunaydinGurseyContactPoset

open scoped Matrix BigOperators
open InfoGeometry.OperatorAlgebra.OntologyRing
open InfoGeometry.Meta
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.SuperGrassmannian.FiveGradedLieSuperalgebra
open InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
open InfoGeometry.Canonical.SplitOctonionIsotropicCircularAmariBaryonNambuPoset

/-- Unambiguous alias for `ZornNambuDeRhamDiracKahlerPoset.Vec3`. -/
abbrev ZornVec3 := InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.Vec3

/-! ===========================================================================
    Section 1: The 6-Stage Acyclic Causal Poset (`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ ⋯ ≺ 𝔎𝔗₆`)
    =========================================================================== -/

/-- The 6 stages of the **5-Graded Kantor–Tanaka Contact Super-Tower, `𝔬𝔰𝔭(1|2)` Superconformal
Closure, & Günaydin–Gürsey `𝔤𝔩₁ ⊕ 𝔰𝔩₃` Color Poset**
(`𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`). -/
inductive KantorTanakaContactColorStage : Type
  /-- `𝔎𝔗₁`: 3-Graded Peirce Operator `ad_H³ - ad_H` & Grade-`±2` Super-Bracket Eruption `(ad_H³ - ad_H)(E_{±2}) = ±6 E_{±2}`. -/
  | KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption
  /-- `𝔎𝔗₂`: Factored 5-Graded Quintic Contact Law `(ad_H² - 4I)(ad_H³ - ad_H) = ad_H⁵ - 5 ad_H³ + 4 ad_H = 0`. -/
  | KT2_FactoredFiveGradedQuinticContactLaw
  /-- `𝔎𝔗₃`: Orthogonal Quartic Lagrange Projectors `Π₀, Π_{±1}, Π_{±2}` (`Π_{±2} = (1/12) ad_H (ad_H³ - ad_H)`). -/
  | KT3_OrthogonalQuarticLagrangeProjectors
  /-- `𝔎𝔗₄`: Orthosymplectic `𝔬𝔰𝔭(1|2)` Superconformal Contact & Graded Jacobi Closure. -/
  | KT4_OrthosymplecticOsp12SuperconformalContactClosure
  /-- `𝔎𝔗₅`: Günaydin–Gürsey `𝔤𝔩₁(R)_H ⊕ 𝔰𝔩₃(R)_color` Split-Octonion Color Decomposition. -/
  | KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition
  /-- `𝔎𝔗₆`: Bilateral Kantor Sandwich Closure `kantorG0²(X) - {kantorGp2, kantorGm2}(X) = Σ X Σ` & 5-Graded Extraction. -/
  | KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich
  deriving DecidableEq, Repr, Inhabited

namespace KantorTanakaContactColorStage

/-- Topological rank `0 .. 5` of the 6 Kantor–Tanaka Contact & Color stages. -/
def rank : KantorTanakaContactColorStage → ℕ
  | .KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption => 0
  | .KT2_FactoredFiveGradedQuinticContactLaw => 1
  | .KT3_OrthogonalQuarticLagrangeProjectors => 2
  | .KT4_OrthosymplecticOsp12SuperconformalContactClosure => 3
  | .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition => 4
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder KantorTanakaContactColorStage :=
  LinearOrder.lift' rank rank_injective

instance : Fintype KantorTanakaContactColorStage where
  elems := {
    .KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption,
    .KT2_FactoredFiveGradedQuinticContactLaw,
    .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT4_OrthosymplecticOsp12SuperconformalContactClosure,
    .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card KantorTanakaContactColorStage = 6 := rfl

/-- Directed diamond causal edges `𝔎𝔗₁ ≺ 𝔎𝔗₂ ≺ 𝔎𝔗₃ ≺ {𝔎𝔗₄, 𝔎𝔗₅} ≺ 𝔎𝔗₆`. -/
def causalEdge : KantorTanakaContactColorStage → KantorTanakaContactColorStage → Prop
  | .KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption,
    .KT2_FactoredFiveGradedQuinticContactLaw => True
  | .KT2_FactoredFiveGradedQuinticContactLaw,
    .KT3_OrthogonalQuarticLagrangeProjectors => True
  | .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT4_OrthosymplecticOsp12SuperconformalContactClosure => True
  | .KT3_OrthogonalQuarticLagrangeProjectors,
    .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition => True
  | .KT4_OrthosymplecticOsp12SuperconformalContactClosure,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => True
  | .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition,
    .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_rank_lt {a b : KantorTanakaContactColorStage} (h : causalEdge a b) :
    rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_causalEdge_rank_lt {a b : KantorTanakaContactColorStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_rank_lt hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_rank_lt hbc)

/-- **DAG Acyclicity Theorem (`KantorTanakaContactColorStage.causalEdge_acyclic`)**:
No stage in `𝔎𝔗₁..𝔎𝔗₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (s : KantorTanakaContactColorStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl _ (transGen_causalEdge_rank_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : KantorTanakaContactColorStage → RepDepth
  | .KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption => .operator
  | .KT2_FactoredFiveGradedQuinticContactLaw => .operator
  | .KT3_OrthogonalQuarticLagrangeProjectors => .transport
  | .KT4_OrthosymplecticOsp12SuperconformalContactClosure => .transport
  | .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition => .thermo
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => .thermo

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : KantorTanakaContactColorStage → OntologyMetaLevel
  | .KT1_ThreeGradedPeirceDefectAndContactSuperBracketEruption => .M1_ProjectorClabject
  | .KT2_FactoredFiveGradedQuinticContactLaw => .M1_ProjectorClabject
  | .KT3_OrthogonalQuarticLagrangeProjectors => .M2_GrassmannianPowertypeOrbit
  | .KT4_OrthosymplecticOsp12SuperconformalContactClosure => .M2_GrassmannianPowertypeOrbit
  | .KT5_GunaydinGurseyGl1PlusSl3SplitOctonionColorDecomposition => .M3_ErlangenCasimirMetaLaw
  | .KT6_FiveGradedMaurerCartanFlatnessAndBilateralKantorSandwich => .M3_ErlangenCasimirMetaLaw

theorem toRepDepth_monotone {a b : KantorTanakaContactColorStage} (h : a ≤ b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> unfold toRepDepth RepDepth.toNat <;> decide

theorem toOntologyMetaLevel_monotone {a b : KantorTanakaContactColorStage} (h : a ≤ b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  change rank a ≤ rank b at h
  cases a <;> cases b <;> revert h <;> unfold toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end KantorTanakaContactColorStage

/-! ===========================================================================
    Section 2: Rung 0 & Stage `𝔎𝔗₁` — Eigenvalue Doubling under Derivations &
    The Socratic Aporia of 3-Graded Peirce Tripotency on the `±2` Contact Shell
    =========================================================================== -/

section StageKT1EigenvalueDoublingAndPeirceCubicAporia

variable {A : Type*} [AddCommGroup A]
variable {B : Type*} [Ring B]

/-- `n`-fold iterate of an operator `D : A → A`. -/
def iterOp {α : Type*} (D : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => D (iterOp D n x)

/-- The 3-Graded Peirce Tripotency Defect Operator `peirceCubicDefect D x := D³(x) - D(x)`. -/
def peirceCubicDefect (D : A → A) (x : A) : A :=
  D (D (D x)) - D x

/-- The Contact-Shell Annihilator Operator `contactShellAnnihilator D x := D²(x) - 4 • x`. -/
def contactShellAnnihilator (D : A → A) (x : A) : A :=
  D (D x) - (4 : ℤ) • x

/-- The 5-Graded Kantor–Tanaka Quintic Contact Operator
`kantorQuinticOp D x := D⁵(x) - 5 • D³(x) + 4 • D(x)`. -/
def kantorQuinticOp (D : A → A) (x : A) : A :=
  D (D (D (D (D x)))) - (5 : ℤ) • D (D (D x)) + (4 : ℤ) • D x

-- theorem-class: constructive endpoint
/-- **Rung 0 & Stage `𝔎𝔗₁` Theorem
(`stage_KT1_derivation_eigenvalue_doubling_and_peirce_cubic_aporia`)**:
1. **Derivation Eigenvalue Doubling from `±1` to `±2` (`[Ring B]`)**:
   For any additive homomorphism `D : B →+ B` satisfying the Leibniz derivation law
   `∀ x y, D (x * y) = D x * y + x * D y`, if `D Qp = Qp` (Grade `+1`) and
   `D Qm = -Qm` (Grade `-1`):
   * `D (Qp * Qp) = (2 : ℤ) • (Qp * Qp)` and `D (anticomm Qp Qp) = (2 : ℤ) • anticomm Qp Qp`,
   * `D (Qm * Qm) = -((2 : ℤ) • (Qm * Qm))` and `D (anticomm Qm Qm) = -((2 : ℤ) • anticomm Qm Qm)`,
   * `D (anticomm Qp Qm) = 0` and `D (comm Qp Qm) = 0`.
2. **Socratic Aporia: 3-Graded Peirce Tripotency Vanishes on `{0, ±1}` but Evaluates to `±6` on `±2`**:
   For any additive homomorphism `D : A →+ A` and eigenvectors
   `D X0 = 0`, `D X1 = X1`, `D Xm1 = -Xm1`, `D E2 = (2 : ℤ) • E2`, `D Em2 = -((2 : ℤ) • Em2)`:
   * `peirceCubicDefect D X0 = 0`, `peirceCubicDefect D X1 = 0`, `peirceCubicDefect D Xm1 = 0`,
   * `peirceCubicDefect D E2 = (6 : ℤ) • E2` and `D (peirceCubicDefect D E2) = (12 : ℤ) • E2`,
   * `peirceCubicDefect D Em2 = -((6 : ℤ) • Em2)` and `D (peirceCubicDefect D Em2) = (12 : ℤ) • Em2`. -/
theorem stage_KT1_derivation_eigenvalue_doubling_and_peirce_cubic_aporia
    (D_ring : B →+ B) (hLeib : ∀ x y : B, D_ring (x * y) = D_ring x * y + x * D_ring y)
    {Qp Qm : B} (hQp : D_ring Qp = Qp) (hQm : D_ring Qm = -Qm)
    (D : A →+ A) {Xm2 Xm1 X0 X1 E2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hE2 : D E2 = (2 : ℤ) • E2) :
    -- (1) Eigenvalue doubling of squares and super-brackets on ±1
    (D_ring (Qp * Qp) = (2 : ℤ) • (Qp * Qp) ∧
      D_ring (anticomm Qp Qp) = (2 : ℤ) • anticomm Qp Qp ∧
      D_ring (Qm * Qm) = -((2 : ℤ) • (Qm * Qm)) ∧
      D_ring (anticomm Qm Qm) = -((2 : ℤ) • anticomm Qm Qm) ∧
      D_ring (anticomm Qp Qm) = 0 ∧
      D_ring (OperatorAlgebra.PeirceSpine.comm Qp Qm) = 0) ∧
    -- (2) Inner 3-graded Peirce core {0, ±1} vs. outer ±2 contact shell aporia
    (peirceCubicDefect D X0 = 0 ∧
      peirceCubicDefect D X1 = 0 ∧
      peirceCubicDefect D Xm1 = 0 ∧
      peirceCubicDefect D E2 = (6 : ℤ) • E2 ∧
      D (peirceCubicDefect D E2) = (12 : ℤ) • E2 ∧
      peirceCubicDefect D Xm2 = -((6 : ℤ) • Xm2) ∧
      D (peirceCubicDefect D Xm2) = (12 : ℤ) • Xm2) := by
  have hQpSq : D_ring (Qp * Qp) = (2 : ℤ) • (Qp * Qp) := by
    rw [hLeib Qp Qp, hQp]
    abel
  have hQmSq : D_ring (Qm * Qm) = -((2 : ℤ) • (Qm * Qm)) := by
    rw [hLeib Qm Qm, hQm]
    simp only [neg_mul, mul_neg]
    abel
  have hQpQm : D_ring (Qp * Qm) = 0 := by
    rw [hLeib Qp Qm, hQp, hQm, mul_neg, add_neg_cancel]
  have hQmQp : D_ring (Qm * Qp) = 0 := by
    rw [hLeib Qm Qp, hQm, hQp, neg_mul, neg_add_cancel]
  have hDefE2 : peirceCubicDefect D E2 = (6 : ℤ) • E2 := by
    dsimp [peirceCubicDefect]
    rw [hE2, map_zsmul, hE2, map_zsmul, map_zsmul, hE2]
    abel
  have hDefXm2 : peirceCubicDefect D Xm2 = -((6 : ℤ) • Xm2) := by
    dsimp [peirceCubicDefect]
    simp only [hXm2, map_neg, map_zsmul]
    abel
  refine ⟨⟨hQpSq, ?_, hQmSq, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, hDefE2, ?_, hDefXm2, ?_⟩⟩
  · dsimp [anticomm]
    rw [map_add, hQpSq]
    abel
  · dsimp [anticomm]
    rw [map_add, hQmSq]
    abel
  · dsimp [anticomm]
    rw [map_add, hQpQm, hQmQp, add_zero]
  · dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [map_sub, hQpQm, hQmQp, sub_zero]
  · dsimp [peirceCubicDefect]
    rw [hX0, map_zero, map_zero, sub_self]
  · dsimp [peirceCubicDefect]
    rw [hX1, hX1, hX1, sub_self]
  · dsimp [peirceCubicDefect]
    rw [hXm1, map_neg, hXm1, neg_neg, hXm1, sub_self]
  · rw [hDefE2, map_zsmul, hE2]
    abel
  · rw [hDefXm2, map_neg, map_zsmul, hXm2]
    abel

end StageKT1EigenvalueDoublingAndPeirceCubicAporia

/-! ===========================================================================
    Section 3: Stage `𝔎𝔗₂` — Factored 5-Graded Quintic Contact Law
    (`(ad_H² - 4I)(ad_H³ - ad_H) = ad_H⁵ - 5 ad_H³ + 4 ad_H = 0`)
    =========================================================================== -/

section StageKT2FactoredQuinticContactLaw

variable {R : Type*} [CommRing R]
variable {A : Type*} [AddCommGroup A]
variable {B : Type*} [Ring B]

/-- Scalar polynomial factorization of the 5-graded quintic contact polynomial. -/
theorem quintic_contact_factored_poly (x : R) :
    (x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x := by
  ring

-- theorem-class: constructive endpoint
/-- **Stage `𝔎𝔗₂` Theorem (`stage_KT2_factored_quintic_contact_law`)**:
1. **Polynomial Factorization over `[CommRing R]`**:
   * `(x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x`,
   * `x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x`,
   * `x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x`.
2. **Operator Factorization for Any `D : A →+ A`**:
   * `contactShellAnnihilator D (peirceCubicDefect D x) = kantorQuinticOp D x`,
   * `peirceCubicDefect D (contactShellAnnihilator D x) = kantorQuinticOp D x`.
3. **Exact Annihilation of Any 5-Graded Sum `X = Xm2 + Xm1 + X0 + X1 + X2`**:
   * `peirceCubicDefect D (Xm2 + Xm1 + X0 + X1 + X2) = (6 : ℤ) • (X2 - Xm2)`,
   * `kantorQuinticOp D (Xm2 + Xm1 + X0 + X1 + X2) = 0`.
4. **Concrete `M₃(R)` Cartan Derivation `adH` & Non-Commutative Peirce `cornerOperatorSum`**:
   * `adH (adH (adH (adH (adH M)))) - 5 • adH (adH (adH M)) + 4 • adH M = 0`,
   * `chargeIter P (cornerOperatorSum P A_op C_op) 5 X_op -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A_op C_op) 3 X_op +
        (4 : ℤ) • chargeIter P (cornerOperatorSum P A_op C_op) 1 X_op = 0`. -/
theorem stage_KT2_factored_quintic_contact_law
    (x : R) (M : Matrix (Fin 3) (Fin 3) R)
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2)
    {P : B} (hP : P * P = P) (A_op C_op X_op : B) :
    -- (1) Polynomial factorizations
    ((x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
      x * (x ^ 2 - 1) * (x ^ 2 - 4) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
      x * (x - 1) * (x + 1) * (x - 2) * (x + 2) = x ^ 5 - 5 * x ^ 3 + 4 * x) ∧
    -- (2) Operator factorizations
    (contactShellAnnihilator D (peirceCubicDefect D v) = kantorQuinticOp D v ∧
      peirceCubicDefect D (contactShellAnnihilator D v) = kantorQuinticOp D v) ∧
    -- (3) Action on a general 5-graded decomposition
    (peirceCubicDefect D (Xm2 + Xm1 + X0 + X1 + X2) = (6 : ℤ) • (X2 - Xm2) ∧
      kantorQuinticOp D (Xm2 + Xm1 + X0 + X1 + X2) = 0) ∧
    -- (4) Concrete M_3(R) adH and Peirce cornerOperatorSum realizations
    (adH (adH (adH (adH (adH M)))) - 5 • adH (adH (adH M)) + 4 • adH M = 0 ∧
      chargeIter P (cornerOperatorSum P A_op C_op) 5 X_op -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A_op C_op) 3 X_op +
        (4 : ℤ) • chargeIter P (cornerOperatorSum P A_op C_op) 1 X_op = 0) := by
  have hFact1 : contactShellAnnihilator D (peirceCubicDefect D v) = kantorQuinticOp D v := by
    dsimp [contactShellAnnihilator, peirceCubicDefect, kantorQuinticOp]
    rw [map_sub, map_sub]
    abel
  have hFact2 : peirceCubicDefect D (contactShellAnnihilator D v) = kantorQuinticOp D v := by
    dsimp [contactShellAnnihilator, peirceCubicDefect, kantorQuinticOp]
    rw [map_sub, map_sub, map_sub, map_zsmul, map_zsmul, map_zsmul]
    abel
  have hCubSum : peirceCubicDefect D (Xm2 + Xm1 + X0 + X1 + X2) = (6 : ℤ) • (X2 - Xm2) := by
    dsimp [peirceCubicDefect]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  have hQuintSum : kantorQuinticOp D (Xm2 + Xm1 + X0 + X1 + X2) = 0 := by
    dsimp [kantorQuinticOp]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  exact ⟨⟨quintic_contact_factored_poly x,
          quintic_polynomial_factorization x,
          five_grade_roots_expansion x⟩,
    ⟨hFact1, hFact2⟩,
    ⟨hCubSum, hQuintSum⟩,
    ⟨adH_quintic_identity M, charge_iter_fifth_annihilator hP A_op C_op X_op⟩⟩

end StageKT2FactoredQuinticContactLaw

/-! ===========================================================================
    Section 4: Stage `𝔎𝔗₃` — Orthogonal Quartic Lagrange Projectors
    (`Π₀, Π_{±1}, Π_{±2}` and Signed Grade Projectors)
    =========================================================================== -/

section StageKT3OrthogonalQuarticLagrangeProjectors

variable {A : Type*} [AddCommGroup A]

/-- Scaled Grade-`0` Quartic Lagrange Projector:
`lagrangeShellProj0 D x := 12 • x - 15 • D²(x) + 3 • D⁴(x) = 3(D² - I)(D² - 4I)(x)`. -/
def lagrangeShellProj0 (D : A → A) (x : A) : A :=
  (12 : ℤ) • x - (15 : ℤ) • D (D x) + (3 : ℤ) • D (D (D (D x)))

/-- Scaled Grade-`±1` Quartic Lagrange Projector:
`lagrangeShellProj1 D x := 16 • D²(x) - 4 • D⁴(x) = -4 D²(D² - 4I)(x)`. -/
def lagrangeShellProj1 (D : A → A) (x : A) : A :=
  (16 : ℤ) • D (D x) - (4 : ℤ) • D (D (D (D x)))

/-- Scaled Grade-`±2` Contact Quartic Lagrange Projector:
`lagrangeShellProj2 D x := D⁴(x) - D²(x) = D(D³ - D)(x)`. -/
def lagrangeShellProj2 (D : A → A) (x : A) : A :=
  D (D (D (D x))) - D (D x)

/-- Signed Grade-`+1` Projector (scaled by `6`):
`(4 D² - D⁴) + (4 D - D³)`. -/
def lagrangeSignedProjPlus1 (D : A → A) (x : A) : A :=
  ((4 : ℤ) • D (D x) - D (D (D (D x)))) + ((4 : ℤ) • D x - D (D (D x)))

/-- Signed Grade-`-1` Projector (scaled by `6`):
`(4 D² - D⁴) - (4 D - D³)`. -/
def lagrangeSignedProjMinus1 (D : A → A) (x : A) : A :=
  ((4 : ℤ) • D (D x) - D (D (D (D x)))) - ((4 : ℤ) • D x - D (D (D x)))

/-- Signed Grade-`+2` Contact Projector (scaled by `24`):
`(D⁴ - D²) + 2(D³ - D)`. -/
def lagrangeSignedProjPlus2 (D : A → A) (x : A) : A :=
  (D (D (D (D x))) - D (D x)) + (2 : ℤ) • (D (D (D x)) - D x)

/-- Signed Grade-`-2` Contact Projector (scaled by `24`):
`(D⁴ - D²) - 2(D³ - D)`. -/
def lagrangeSignedProjMinus2 (D : A → A) (x : A) : A :=
  (D (D (D (D x))) - D (D x)) - (2 : ℤ) • (D (D (D x)) - D x)

-- theorem-class: constructive endpoint
/-- **Stage `𝔎𝔗₃` Theorem (`stage_KT3_orthogonal_quartic_lagrange_projectors`)**:
1. **Universal Resolution of the Identity (for ANY `D : A → A` and `x : A`)**:
   `lagrangeShellProj0 D x + lagrangeShellProj1 D x + lagrangeShellProj2 D x = (12 : ℤ) • x`.
2. **Contact Projector Equals Scaled Peirce Defect (`D : A →+ A`)**:
   `lagrangeShellProj2 D x = D (peirceCubicDefect D x)`.
3. **Exact Shell & Signed Grade Isolation on `X = Xm2 + Xm1 + X0 + X1 + X2`**:
   * `lagrangeShellProj0 D X = (12 : ℤ) • X0`,
   * `lagrangeShellProj1 D X = (12 : ℤ) • (Xm1 + X1)`,
   * `lagrangeShellProj2 D X = (12 : ℤ) • (Xm2 + X2)`,
   * `lagrangeSignedProjPlus1 D X = (6 : ℤ) • X1`,
   * `lagrangeSignedProjMinus1 D X = (6 : ℤ) • Xm1`,
   * `lagrangeSignedProjPlus2 D X = (24 : ℤ) • X2`,
   * `lagrangeSignedProjMinus2 D X = (24 : ℤ) • Xm2`.
4. **Scaled Idempotency & Mutual Orthogonality on `X`**:
   * `lagrangeShellProj0 D (lagrangeShellProj0 D X) = (12 : ℤ) • lagrangeShellProj0 D X`,
   * `lagrangeShellProj1 D (lagrangeShellProj1 D X) = (12 : ℤ) • lagrangeShellProj1 D X`,
   * `lagrangeShellProj2 D (lagrangeShellProj2 D X) = (12 : ℤ) • lagrangeShellProj2 D X`,
   * `lagrangeShellProj0 D (lagrangeShellProj1 D X) = 0`,
   * `lagrangeShellProj0 D (lagrangeShellProj2 D X) = 0`,
   * `lagrangeShellProj1 D (lagrangeShellProj2 D X) = 0`. -/
theorem stage_KT3_orthogonal_quartic_lagrange_projectors
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2) :
    let X := Xm2 + Xm1 + X0 + X1 + X2
    -- (1) Universal resolution of the identity & contact projector = D(D³ - D)
    (lagrangeShellProj0 D v + lagrangeShellProj1 D v + lagrangeShellProj2 D v = (12 : ℤ) • v ∧
      lagrangeShellProj2 D v = D (peirceCubicDefect D v)) ∧
    -- (2) Shell isolation on X
    (lagrangeShellProj0 D X = (12 : ℤ) • X0 ∧
      lagrangeShellProj1 D X = (12 : ℤ) • (Xm1 + X1) ∧
      lagrangeShellProj2 D X = (12 : ℤ) • (Xm2 + X2)) ∧
    -- (3) Signed grade isolation on X
    (lagrangeSignedProjPlus1 D X = (6 : ℤ) • X1 ∧
      lagrangeSignedProjMinus1 D X = (6 : ℤ) • Xm1 ∧
      lagrangeSignedProjPlus2 D X = (24 : ℤ) • X2 ∧
      lagrangeSignedProjMinus2 D X = (24 : ℤ) • Xm2) ∧
    -- (4) Scaled idempotency and mutual orthogonality
    (lagrangeShellProj0 D (lagrangeShellProj0 D X) = (12 : ℤ) • lagrangeShellProj0 D X ∧
      lagrangeShellProj1 D (lagrangeShellProj1 D X) = (12 : ℤ) • lagrangeShellProj1 D X ∧
      lagrangeShellProj2 D (lagrangeShellProj2 D X) = (12 : ℤ) • lagrangeShellProj2 D X ∧
      lagrangeShellProj0 D (lagrangeShellProj1 D X) = 0 ∧
      lagrangeShellProj0 D (lagrangeShellProj2 D X) = 0 ∧
      lagrangeShellProj1 D (lagrangeShellProj2 D X) = 0) := by
  intro X
  have hP0 : lagrangeShellProj0 D X = (12 : ℤ) • X0 := by
    dsimp [X, lagrangeShellProj0]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  have hP1 : lagrangeShellProj1 D X = (12 : ℤ) • (Xm1 + X1) := by
    dsimp [X, lagrangeShellProj1]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  have hP2 : lagrangeShellProj2 D X = (12 : ℤ) • (Xm2 + X2) := by
    dsimp [X, lagrangeShellProj2]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  refine ⟨⟨by dsimp [lagrangeShellProj0, lagrangeShellProj1, lagrangeShellProj2]; abel,
           by dsimp [lagrangeShellProj2, peirceCubicDefect]; rw [map_sub]⟩,
    ⟨hP0, hP1, hP2⟩,
    ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · dsimp [X, lagrangeSignedProjPlus1]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  · dsimp [X, lagrangeSignedProjMinus1]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  · dsimp [X, lagrangeSignedProjPlus2]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  · dsimp [X, lagrangeSignedProjMinus2]
    simp only [map_add, hXm2, hXm1, hX0, hX1, hX2, map_neg, map_zsmul, map_zero]
    abel
  · rw [hP0]
    dsimp [lagrangeShellProj0]
    simp only [map_zsmul, hX0, map_zero, smul_zero, sub_zero, add_zero]
  · rw [hP1]
    dsimp [lagrangeShellProj1]
    simp only [map_zsmul, map_add, hXm1, hX1, map_neg, neg_neg]
    abel
  · rw [hP2]
    dsimp [lagrangeShellProj2]
    simp only [map_zsmul, map_add, hXm2, hX2, map_neg]
    abel
  · rw [hP1]
    dsimp [lagrangeShellProj0]
    simp only [map_zsmul, map_add, hXm1, hX1, map_neg, neg_neg]
    abel
  · rw [hP2]
    dsimp [lagrangeShellProj0]
    simp only [map_zsmul, map_add, hXm2, hX2, map_neg]
    abel
  · rw [hP2]
    dsimp [lagrangeShellProj1]
    simp only [map_zsmul, map_add, hXm2, hX2, map_neg]
    abel

end StageKT3OrthogonalQuarticLagrangeProjectors

/-! ===========================================================================
    Section 5: Stage `𝔎𝔗₄` — Orthosymplectic `𝔬𝔰𝔭(1|2)` Superconformal Contact &
    Graded Jacobi Closure
    =========================================================================== -/

section StageKT4Osp12SuperconformalContactAndGradedJacobiClosure

variable {B : Type*} [Ring B]
variable {R : Type*} [CommRing R]

/-- The Cartan grading generator `H = E₀₀ - E₂₂ = diag(1, 0, -1)` in `M₃(R)`. -/
def H_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  SuperGrassmannian.KantorTanakaSuperGrassmannian.E 0 0 -
    SuperGrassmannian.KantorTanakaSuperGrassmannian.E 2 2

/-- The Grade-`+2` upper contact generator `E = E₀₂` in `M₃(R)`. -/
def E_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  SuperGrassmannian.KantorTanakaSuperGrassmannian.E 0 2

/-- The Grade-`-2` lower contact generator `F = E₂₀` in `M₃(R)`. -/
def F_gen (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  SuperGrassmannian.KantorTanakaSuperGrassmannian.E 2 0

/-- The Grade-`+1` positive odd supercharge `Q_+ = E₀₁ + E₁₂` in `M₃(R)`. -/
def Q_plus (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  SuperGrassmannian.KantorTanakaSuperGrassmannian.E 0 1 +
    SuperGrassmannian.KantorTanakaSuperGrassmannian.E 1 2

/-- The Grade-`-1` negative odd supercharge `Q_- = E₁₀ - E₂₁` in `M₃(R)`. -/
def Q_minus (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  SuperGrassmannian.KantorTanakaSuperGrassmannian.E 1 0 -
    SuperGrassmannian.KantorTanakaSuperGrassmannian.E 2 1

/-- Matrix commutator `[A, B] = A * B - B * A` in `M₃(R)`. -/
def commutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B - B * A

/-- Matrix anticommutator `{A, B} = A * B + B * A` in `M₃(R)`. -/
def anticommutator (A B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  A * B + B * A

/-- `[H, Q_+] = Q_+`. -/
theorem osp_grad_H_Q_plus : commutator (H_gen R) (Q_plus R) = Q_plus R := by
  unfold commutator H_gen Q_plus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- `[H, Q_-] = -Q_-`. -/
theorem osp_grad_H_Q_minus : commutator (H_gen R) (Q_minus R) = -Q_minus R := by
  unfold commutator H_gen Q_minus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- `[H, E] = 2 • E`. -/
theorem osp_sl2_H_E : commutator (H_gen R) (E_gen R) = 2 • E_gen R := by
  unfold commutator H_gen E_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; (fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]); ring

/-- `[H, F] = -2 • F`. -/
theorem osp_sl2_H_F : commutator (H_gen R) (F_gen R) = -2 • F_gen R := by
  unfold commutator H_gen F_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; (fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]); ring

/-- `{Q_+, Q_-} = H`. -/
theorem osp_anticomm_plus_minus : anticommutator (Q_plus R) (Q_minus R) = H_gen R := by
  unfold anticommutator Q_plus Q_minus H_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply]

/-- `{Q_+, Q_+} = 2 • E`. -/
theorem osp_anticomm_plus_plus : anticommutator (Q_plus R) (Q_plus R) = 2 • E_gen R := by
  unfold anticommutator Q_plus E_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; (fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply]); ring

/-- `{Q_-, Q_-} = -2 • F`. -/
theorem osp_anticomm_minus_minus : anticommutator (Q_minus R) (Q_minus R) = -2 • F_gen R := by
  unfold anticommutator Q_minus F_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; (fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply]); ring

/-- `[E, F] = H`. -/
theorem osp_sl2_E_F : commutator (E_gen R) (F_gen R) = H_gen R := by
  unfold commutator E_gen F_gen H_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- Polymorphic Grade-`+2` contact matrix `matE3 : Matrix (Fin 3) (Fin 3) R`. -/
def matE3 : Matrix (Fin 3) (Fin 3) R := E_gen R

/-- Polymorphic Grade-`-2` contact matrix `matF3 : Matrix (Fin 3) (Fin 3) R`. -/
def matF3 : Matrix (Fin 3) (Fin 3) R := F_gen R

/-- Non-commutativity witness for the extremal contact generators over any nontrivial ring `R`:
`matE3 * matF3 ≠ matF3 * matE3`. -/
theorem osp_E_F_noncomm [Nontrivial R] :
    (matE3 : Matrix (Fin 3) (Fin 3) R) * (matF3 : Matrix (Fin 3) (Fin 3) R) ≠
      (matF3 : Matrix (Fin 3) (Fin 3) R) * (matE3 : Matrix (Fin 3) (Fin 3) R) := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  unfold matE3 matF3 E_gen F_gen SuperGrassmannian.KantorTanakaSuperGrassmannian.E at h00
  simp [Matrix.mul_apply] at h00

/-- `[E, Q_-] = -Q_+`. -/
theorem osp_ladder_E_Q_minus : commutator (E_gen R) (Q_minus R) = -Q_plus R := by
  unfold commutator E_gen Q_minus Q_plus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

/-- `[F, Q_+] = -Q_-`. -/
theorem osp_ladder_F_Q_plus : commutator (F_gen R) (Q_plus R) = -Q_minus R := by
  unfold commutator F_gen Q_plus Q_minus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply]

-- theorem-class: constructive endpoint
/-- **Stage `𝔎𝔗₄` Theorem (`stage_KT4_osp12_superconformal_contact_and_graded_jacobi_closure`)**:
1. **Universal Odd-Odd-Odd Super-Jacobi Identity in Any Associative Ring `B`**:
   * `comm Q₁ (anticomm Q₂ Q₃) + comm Q₂ (anticomm Q₃ Q₁) + comm Q₃ (anticomm Q₁ Q₂) = 0`.
2. **Concrete `𝔬𝔰𝔭(1|2)` Contact & Super-Jacobi Balance in `M₃(R)`**:
   * `[H, Q_+] = Q_+`, `[H, Q_-] = -Q_-`, `[H, E_{+2}] = 2 E_{+2}`, `[H, F_{-2}] = -2 F_{-2}`,
   * `{Q_+, Q_-} = H`, `{Q_+, Q_+} = 2 E_{+2}`, `{Q_-, Q_-} = -2 F_{-2}`, `[E_{+2}, F_{-2}] = H`,
   * `[E_{+2}, Q_-] = -Q_+`, `[F_{-2}, Q_+] = -Q_-`, `[E_{+2}, Q_+] = 0`, `[F_{-2}, Q_-] = 0`,
   * **Odd-Odd-Odd Super-Jacobi Contact Balance**:
     The Grade-`0` contribution `2 [Q_+, {Q_+, Q_-}] = -2 • Q_+` and the Grade-`+2` contact
     contribution `[Q_-, {Q_+, Q_+}] = +2 • Q_+` are individually non-zero and cancel
     identically:
     `commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
        commutator (Q_plus R) (anticommutator (Q_minus R) (Q_plus R)) = -(2 • Q_plus R)`,
     `commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) = 2 • Q_plus R`, and
     their sum is `0`. -/
theorem stage_KT4_osp12_superconformal_contact_and_graded_jacobi_closure
    (Q₁ Q₂ Q₃ : B) :
    -- (1) Universal odd-odd-odd super-Jacobi identity in any associative ring B
    (OperatorAlgebra.PeirceSpine.comm Q₁ (anticomm Q₂ Q₃) +
      OperatorAlgebra.PeirceSpine.comm Q₂ (anticomm Q₃ Q₁) +
      OperatorAlgebra.PeirceSpine.comm Q₃ (anticomm Q₁ Q₂) = 0) ∧
    -- (2) Concrete osp(1|2) grading, brackets, and super-Jacobi contact balance in M_3(R)
    (commutator (H_gen R) (Q_plus R) = Q_plus R ∧
      commutator (H_gen R) (Q_minus R) = -Q_minus R ∧
      commutator (H_gen R) (E_gen R) = 2 • E_gen R ∧
      commutator (H_gen R) (F_gen R) = -2 • F_gen R ∧
      anticommutator (Q_plus R) (Q_minus R) = H_gen R ∧
      anticommutator (Q_plus R) (Q_plus R) = 2 • E_gen R ∧
      anticommutator (Q_minus R) (Q_minus R) = -2 • F_gen R ∧
      commutator (E_gen R) (F_gen R) = H_gen R ∧
      commutator (E_gen R) (Q_minus R) = -Q_plus R ∧
      commutator (F_gen R) (Q_plus R) = -Q_minus R ∧
      commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
          commutator (Q_plus R) (anticommutator (Q_minus R) (Q_plus R)) =
        -(2 • Q_plus R) ∧
      commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) =
        2 • Q_plus R ∧
      commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
          commutator (Q_plus R) (anticommutator (Q_minus R) (Q_plus R)) +
          commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) = 0) := by
  have hGrade0Term :
      commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
        commutator (Q_plus R) (anticommutator (Q_minus R) (Q_plus R)) =
        -(2 • Q_plus R) := by
    unfold commutator anticommutator Q_plus Q_minus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply] <;> ring
  have hGrade2Term :
      commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) =
        2 • Q_plus R := by
    unfold commutator anticommutator Q_plus Q_minus SuperGrassmannian.KantorTanakaSuperGrassmannian.E
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply] <;> ring
  exact ⟨by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
    ⟨osp_grad_H_Q_plus,
     osp_grad_H_Q_minus,
     osp_sl2_H_E,
     osp_sl2_H_F,
     osp_anticomm_plus_minus,
     osp_anticomm_plus_plus,
     osp_anticomm_minus_minus,
     osp_sl2_E_F,
     osp_ladder_E_Q_minus,
     osp_ladder_F_Q_plus,
     hGrade0Term,
     hGrade2Term,
     by rw [hGrade0Term, hGrade2Term, neg_add_cancel]⟩⟩

end StageKT4Osp12SuperconformalContactAndGradedJacobiClosure

/-! ===========================================================================
    Section 6: Stage `𝔎𝔗₅` — Günaydin–Gürsey `𝔤𝔩₁(R)_H ⊕ 𝔰𝔩₃(R)_color`
    Split-Octonion Color Decomposition
    =========================================================================== -/

section StageKT5GunaydinGurseyGl1Sl3ColorDecomposition

variable {R : Type*} [CommRing R]

/-- Scaled `𝔤𝔩₁(R)_H` baryon/contact trace projection on `M₃(R)`:
`gl1BaryonScaledProj X := Tr(X) • I₃ = 3 𝒫_{𝔤𝔩₁}(X)`. -/
def gl1BaryonScaledProj (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.trace X • (1 : Matrix (Fin 3) (Fin 3) R)

/-- Scaled `𝔰𝔩₃(R)_color` traceless gluon projection on `M₃(R)`:
`sl3ColorScaledProj X := 3 • X - Tr(X) • I₃ = 3 𝒫_{𝔰𝔩₃}(X)`. -/
def sl3ColorScaledProj (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  (3 : R) • X - Matrix.trace X • (1 : Matrix (Fin 3) (Fin 3) R)

/-- Quark–antiquark outer product `u ⊗ vᵀ` in `M₃(R)` for `u, v : ZornVec3 R`. -/
def quarkAntiquarkMat3 (u v : ZornVec3 R) : Matrix (Fin 3) (Fin 3) R :=
  !![u.x * v.x, u.x * v.y, u.x * v.z;
     u.y * v.x, u.y * v.y, u.y * v.z;
     u.z * v.x, u.z * v.y, u.z * v.z]

-- theorem-class: constructive endpoint
/-- **Stage `𝔎𝔗₅` Theorem (`stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition`)**:
In the Grade-`0` endomorphism algebra `𝔤𝔩₃(R) = Matrix (Fin 3) (Fin 3) R`:
1. **Orthogonal Direct Sum Decomposition (`𝔤𝔩₃ = 𝔤𝔩₁_H ⊕ 𝔰𝔩₃_color`)**:
   * `gl1BaryonScaledProj X + sl3ColorScaledProj X = (3 : R) • X`,
   * `Matrix.trace (gl1BaryonScaledProj X) = 3 * Matrix.trace X`,
   * `Matrix.trace (sl3ColorScaledProj X) = 0` (traceless color algebra!),
   * `gl1BaryonScaledProj (gl1BaryonScaledProj X) = (3 : R) • gl1BaryonScaledProj X`,
   * `sl3ColorScaledProj (sl3ColorScaledProj X) = (3 : R) • sl3ColorScaledProj X`,
   * `gl1BaryonScaledProj (sl3ColorScaledProj X) = 0`,
   * `sl3ColorScaledProj (gl1BaryonScaledProj X) = 0`.
2. **Exact Lie Ideal & Centralizer Closure (`[𝔤𝔩₃, 𝔤𝔩₃] ⊆ 𝔰𝔩₃`, `[𝔤𝔩₁, 𝔰𝔩₃] = 0`)**:
   * `Matrix.trace (X * Y - Y * X) = 0`,
   * `sl3ColorScaledProj (X * Y - Y * X) = (3 : R) • (X * Y - Y * X)`,
   * `gl1BaryonScaledProj (X * Y - Y * X) = 0`,
   * `gl1BaryonScaledProj X * sl3ColorScaledProj Y -
        sl3ColorScaledProj Y * gl1BaryonScaledProj X = 0`.
3. **Quark–Antiquark `[𝔤_{+1}, 𝔤_{-1}]` Outer Product Decomposition**:
   * `Matrix.trace (quarkAntiquarkMat3 u v) = ZornVec3.dot u v`,
   * `(3 : R) • quarkAntiquarkMat3 u v =
        (ZornVec3.dot u v) • (1 : Matrix (Fin 3) (Fin 3) R) +
          sl3ColorScaledProj (quarkAntiquarkMat3 u v)`. -/
theorem stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition
    (X Y : Matrix (Fin 3) (Fin 3) R) (u v : ZornVec3 R) :
    -- (1) Orthogonal direct sum decomposition
    (gl1BaryonScaledProj X + sl3ColorScaledProj X = (3 : R) • X ∧
      Matrix.trace (gl1BaryonScaledProj X) = 3 * Matrix.trace X ∧
      Matrix.trace (sl3ColorScaledProj X) = 0 ∧
      gl1BaryonScaledProj (gl1BaryonScaledProj X) = (3 : R) • gl1BaryonScaledProj X ∧
      sl3ColorScaledProj (sl3ColorScaledProj X) = (3 : R) • sl3ColorScaledProj X ∧
      gl1BaryonScaledProj (sl3ColorScaledProj X) = 0 ∧
      sl3ColorScaledProj (gl1BaryonScaledProj X) = 0) ∧
    -- (2) Lie ideal and centralizer closure
    (Matrix.trace (X * Y - Y * X) = 0 ∧
      sl3ColorScaledProj (X * Y - Y * X) = (3 : R) • (X * Y - Y * X) ∧
      gl1BaryonScaledProj (X * Y - Y * X) = 0 ∧
      gl1BaryonScaledProj X * sl3ColorScaledProj Y -
          sl3ColorScaledProj Y * gl1BaryonScaledProj X = 0) ∧
    -- (3) Quark-antiquark outer product trace & color decomposition
    (Matrix.trace (quarkAntiquarkMat3 u v) =
        ZornNambuDeRhamDiracKahlerPoset.Vec3.dot u v ∧
      (3 : R) • quarkAntiquarkMat3 u v =
        (ZornNambuDeRhamDiracKahlerPoset.Vec3.dot u v) •
            (1 : Matrix (Fin 3) (Fin 3) R) +
          sl3ColorScaledProj (quarkAntiquarkMat3 u v)) := by
  have hTr1 : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) R) = 3 := by
    simp [Matrix.trace]
  have hTrGl1 : Matrix.trace (gl1BaryonScaledProj X) = 3 * Matrix.trace X := by
    dsimp [gl1BaryonScaledProj]
    rw [Matrix.trace_smul, hTr1, smul_eq_mul, mul_comm]
  have hTrSl3 : Matrix.trace (sl3ColorScaledProj X) = 0 := by
    dsimp [sl3ColorScaledProj]
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, hTr1, smul_eq_mul, smul_eq_mul]
    ring
  have hTrComm : Matrix.trace (X * Y - Y * X) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self]
  have hTrQA :
      Matrix.trace (quarkAntiquarkMat3 u v) =
        ZornNambuDeRhamDiracKahlerPoset.Vec3.dot u v := by
    dsimp [quarkAntiquarkMat3, ZornNambuDeRhamDiracKahlerPoset.Vec3.dot, Matrix.trace]
    simp [Fin.sum_univ_three]
  refine ⟨⟨by dsimp [gl1BaryonScaledProj, sl3ColorScaledProj]; abel,
           hTrGl1,
           hTrSl3,
           by dsimp [gl1BaryonScaledProj]; rw [Matrix.trace_smul, hTr1, smul_smul]; ring_nf,
           by
             calc
               sl3ColorScaledProj (sl3ColorScaledProj X)
                   = (3 : R) • sl3ColorScaledProj X -
                       Matrix.trace (sl3ColorScaledProj X) • (1 : Matrix (Fin 3) (Fin 3) R) := rfl
               _ = (3 : R) • sl3ColorScaledProj X := by rw [hTrSl3, zero_smul, sub_zero],
           by dsimp [gl1BaryonScaledProj]; rw [hTrSl3, zero_smul],
           by
             dsimp [sl3ColorScaledProj]
             rw [hTrGl1]
             dsimp [gl1BaryonScaledProj]
             rw [smul_smul, sub_self]⟩,
    ⟨hTrComm,
     by dsimp [sl3ColorScaledProj]; rw [hTrComm, zero_smul, sub_zero],
     by dsimp [gl1BaryonScaledProj]; rw [hTrComm, zero_smul],
     by
       dsimp [gl1BaryonScaledProj]
       rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, sub_self]⟩,
    ⟨hTrQA,
     by
       rw [← hTrQA]
       dsimp [sl3ColorScaledProj]
       abel⟩⟩

end StageKT5GunaydinGurseyGl1Sl3ColorDecomposition

/-! ===========================================================================
    Section 7: Stage `𝔎𝔗₆` — Bilateral Kantor Sandwich Closure
    (`kantorG0²(X) - {kantorGp2, kantorGm2}(X) = Σ X Σ`) & 5-Graded Extraction
    =========================================================================== -/

section StageKT6BilateralKantorSandwichClosure

variable {B : Type*} [Ring B]

/-- Grade-`0` Kantor cross-corner sandwich `kantorG0 P A C X := N_+ X N_- + N_- X N_+`. -/
def kantorG0 (P A C X : B) : B :=
  sandwichCross P A C X

/-- Grade-`+2` Kantor upper contact sandwich `kantorGp2 P A X := N_+ X N_+`. -/
def kantorGp2 (P A X : B) : B :=
  sandwich (conePlus P A) (conePlus P A) X

/-- Grade-`-2` Kantor lower contact sandwich `kantorGm2 P C X := N_- X N_-`. -/
def kantorGm2 (P C X : B) : B :=
  sandwich (coneMinus P C) (coneMinus P C) X

-- theorem-class: constructive endpoint
/-- **Stage `𝔎𝔗₆` Theorem (`stage_KT6_bilateral_kantor_sandwich_and_five_graded_extraction`)**:
In any associative ring `B` with idempotent `P * P = P` and seeds `A C X : B`:
1. **Same-Support vs. Crossed-Support Kantor Sandwich Squares**:
   * `kantorG0 P A C (kantorG0 P A C X) =
        qgtPlus P A C * X * qgtPlus P A C + qgtMinus P A C * X * qgtMinus P A C`,
   * `kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X) =
        qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C`.
2. **Bilateral Kantor Sandwich Closure (`Σ X Σ` and `V X V`)**:
   * `kantorG0 P A C (kantorG0 P A C X) -
        (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
          genSig P A C * X * genSig P A C`,
   * `kantorG0 P A C (kantorG0 P A C X) +
        (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
          genV P A C * X * genV P A C`.
3. **5-Graded Peirce Charge Extraction of `kantorG0`, `kantorGp2`, `kantorGm2`**:
   * `chargeIter P (cornerOperatorSum P A C) 4 X -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X +
        (4 : ℤ) • cornerOperatorSum P A C X = (4 : ℤ) • kantorG0 P A C X`,
   * `(chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) +
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) = (24 : ℤ) • kantorGp2 P A X`,
   * `(chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) -
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) = (24 : ℤ) • kantorGm2 P C X`. -/
theorem stage_KT6_bilateral_kantor_sandwich_and_five_graded_extraction
    {P : B} (hP : P * P = P) (A C X : B) :
    -- (1) Same-support vs. crossed-support sandwich compositions
    (kantorG0 P A C (kantorG0 P A C X) =
        qgtPlus P A C * X * qgtPlus P A C + qgtMinus P A C * X * qgtMinus P A C ∧
      kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X) =
        qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C) ∧
    -- (2) Bilateral Kantor sandwich difference (Σ X Σ) and sum (V X V)
    (kantorG0 P A C (kantorG0 P A C X) -
        (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
        genSig P A C * X * genSig P A C ∧
      kantorG0 P A C (kantorG0 P A C X) +
        (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
        genV P A C * X * genV P A C) ∧
    -- (3) 5-graded Peirce charge extraction of kantorG0, kantorGp2, kantorGm2
    (chargeIter P (cornerOperatorSum P A C) 4 X -
        (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 2 X +
        (4 : ℤ) • cornerOperatorSum P A C X = (4 : ℤ) • kantorG0 P A C X ∧
      (chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) +
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) = (24 : ℤ) • kantorGp2 P A X ∧
      (chargeIter P (cornerOperatorSum P A C) 4 X -
        chargeIter P (cornerOperatorSum P A C) 2 X) -
        (2 : ℤ) • (chargeIter P (cornerOperatorSum P A C) 3 X -
        chargeIter P (cornerOperatorSum P A C) 1 X) = (24 : ℤ) • kantorGm2 P C X) := by
  refine ⟨⟨by dsimp [kantorG0, sandwichCross, qgtPlus, qgtMinus]; peirce_nf hP,
           by dsimp [kantorGp2, kantorGm2, sandwich, qgtPlus, qgtMinus]; peirce_nf hP⟩,
    ⟨by dsimp [kantorG0, kantorGp2, kantorGm2, sandwichCross, sandwich]; peirce_nf hP,
     by dsimp [kantorG0, kantorGp2, kantorGm2, sandwichCross, sandwich]; peirce_nf hP⟩,
    ⟨charge_extract_zero hP A C X,
     charge_extract_plus_two hP A C X,
     charge_extract_minus_two hP A C X⟩⟩

end StageKT6BilateralKantorSandwichClosure

/-! ===========================================================================
    Section 8: Master Capstone Synthesis Unifying `𝔎𝔗₁ ≺ … ≺ 𝔎𝔗₆` and
    `𝔐ℨ₁ ≺ … ≺ 𝔐ℨ₆`
    =========================================================================== -/

-- theorem-class: synthesis endpoint
/-- **Master Synthesis Theorem
(`five_graded_kantor_tanaka_osp_gunaydin_gursey_contact_master_poset`)**:
Unifies the 6-stage **5-Graded Kantor–Tanaka Contact Super-Tower, `𝔬𝔰𝔭(1|2)` Superconformal
Closure, & Günaydin–Gürsey `𝔤𝔩₁ ⊕ 𝔰𝔩₃` Color Poset** (`𝔎𝔗₁ ≺ ⋯ ≺ 𝔎𝔗₆`) with the 6-stage
**Metriplectic Zorn Three-Channel Product & Volume Duality Poset** (`𝔐ℨ₁ ≺ ⋯ ≺ 𝔐ℨ₆`). -/
theorem five_graded_kantor_tanaka_osp_gunaydin_gursey_contact_master_poset
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A_op C_op X_op : B)
    {R : Type*} [CommRing R] (x : R) (M : Matrix (Fin 3) (Fin 3) R)
    (u₁ v₁ u₂ v₂ u₃ v₃ : ZornVec3 R) :
    let t₁ := zornTangent u₁ v₁
    let t₂ := zornTangent u₂ v₂
    let t₃ := zornTangent u₃ v₃
    -- (1) Poset acyclicity across 𝔎𝔗₁..𝔎𝔗₆ and 𝔐ℨ₁..𝔐ℨ₆
    ((∀ s : KantorTanakaContactColorStage,
        ¬ Relation.TransGen KantorTanakaContactColorStage.causalEdge s s) ∧
      (∀ s : MetriplecticZornStage,
        ¬ Relation.TransGen MetriplecticZornStage.causalEdge s s)) ∧
    -- (2) Stages 𝔎𝔗₁–𝔎𝔗₃: Quintic contact factorization & quartic Lagrange resolution
    ((x ^ 2 - 4) * (x ^ 3 - x) = x ^ 5 - 5 * x ^ 3 + 4 * x ∧
      adH (adH (adH (adH (adH M)))) - 5 • adH (adH (adH M)) + 4 • adH M = 0 ∧
      lagrangeShellProj0 (adH (R := R)) M +
        lagrangeShellProj1 (adH (R := R)) M +
        lagrangeShellProj2 (adH (R := R)) M = (12 : ℤ) • M) ∧
    -- (3) Stages 𝔎𝔗₄–𝔎𝔗₆: osp(1|2) super-Jacobi balance, gl₁ ⊕ sl₃ color split & Kantor sandwich
    (commutator (Q_plus R) (anticommutator (Q_plus R) (Q_minus R)) +
        commutator (Q_plus R) (anticommutator (Q_minus R) (Q_plus R)) +
        commutator (Q_minus R) (anticommutator (Q_plus R) (Q_plus R)) = 0 ∧
      gl1BaryonScaledProj M + sl3ColorScaledProj M = (3 : R) • M ∧
      Matrix.trace (sl3ColorScaledProj M) = 0 ∧
      kantorG0 P A_op C_op (kantorG0 P A_op C_op X_op) -
        (kantorGp2 P A_op (kantorGm2 P C_op X_op) +
          kantorGm2 P C_op (kantorGp2 P A_op X_op)) =
        genSig P A_op C_op * X_op * genSig P A_op C_op) ∧
    -- (4) Stages 𝔐ℨ₁–𝔐ℨ₆: Metriplectic 3-term product, 3-term Pythagorean law & dual cubic volumes
    (t₁ * t₂ + t₁ * t₂ =
        scalarZorn (zornFisherMetric t₁ t₂) +
          scalarZorn (zornSymplecticForm t₁ t₂) * zornIPara +
          (zornHodgeCross t₁ t₂ + zornHodgeCross t₁ t₂) ∧
      4 * zornMatrixDet (t₁ * t₂) =
        zornFisherMetric t₁ t₂ * zornFisherMetric t₁ t₂ -
          zornSymplecticForm t₁ t₂ * zornSymplecticForm t₁ t₂ +
          4 * zornMatrixDet (zornHodgeCross t₁ t₂) ∧
      (zornHodgeCross t₁ t₂) * t₃ + t₃ * (zornHodgeCross t₁ t₂) =
        zornMatrixScalar (zornVec3Det u₁ u₂ u₃ - zornVec3Det v₁ v₂ v₃) ∧
      zornDiagPart (zornAssoc t₁ t₂ t₃) =
        -(zornMatrixScalar (zornVec3Det u₁ u₂ u₃ + zornVec3Det v₁ v₂ v₃) * zornIPara)) := by
  intro t₁ t₂ t₃
  have hKT4 := stage_KT4_osp12_superconformal_contact_and_graded_jacobi_closure (R := R) P P P
  have hKT5 := stage_KT5_gunaydin_gursey_gl1_sl3_color_decomposition M M u₁ v₁
  have hKT6 := stage_KT6_bilateral_kantor_sandwich_and_five_graded_extraction hP A_op C_op X_op
  have hMZ :=
    metriplectic_zorn_three_channel_pythagorean_volume_master_poset
      t₁ t₂ u₁ u₁ v₁ u₂ v₂ u₃ v₃
  exact ⟨⟨KantorTanakaContactColorStage.causalEdge_acyclic,
          MetriplecticZornStage.causalEdge_acyclic⟩,
    ⟨quintic_contact_factored_poly x,
     adH_quintic_identity M,
     by dsimp [lagrangeShellProj0, lagrangeShellProj1, lagrangeShellProj2]; abel⟩,
    ⟨hKT4.2.2.2.2.2.2.2.2.2.2.2.2.2,
     hKT5.1.1,
     hKT5.1.2.2.1,
     hKT6.2.1.1⟩,
    ⟨hMZ.2.1.2.1,
     hMZ.2.2.1.1,
     hMZ.2.2.2.1,
     hMZ.2.2.2.2.1⟩⟩

/-! ===========================================================================
    Section 9: The 6-Stage Universal Case-Free Chiral Super-Adjoint (`sad_Q`),
    Alternating Commutator–Anticommutator Cancellation (`sad_Q²(X) = [Q², X]`),
    Super-Sandwich Defect, Division-Free `24 = 4!` Integer 5-Graded Projectors,
    & The 24-Cyclotomic Modular Clock / Octonion–Color Composition Poset
    (`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`)
    =========================================================================== -/

/-- The 6 stages of the **Universal Case-Free Chiral Super-Adjoint, Division-Free
`24 = 4!` Integer 5-Graded Projector Resolution, & 24-Cyclotomic Modular Clock Poset**
(`𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`). -/
inductive SuperAdjointCyclotomic24Stage : Type
  | sa1_case_free_chiral_super_adjoint_operator
  | sa2_parity_alternating_bracket_and_super_adjoint_square_law
  | sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split
  | sa4_division_free_24_factorial_integer_five_graded_projectors
  | sa5_cyclotomic_24_modular_clock_and_octonion_color_composition
  | sa6_exponent_two_galois_cube_and_mod_24_involution_lock
  deriving DecidableEq, Repr, Inhabited

namespace SuperAdjointCyclotomic24Stage

/-- Direct causal cover relation for `𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`. -/
def causalEdge : SuperAdjointCyclotomic24Stage → SuperAdjointCyclotomic24Stage → Prop
  | .sa1_case_free_chiral_super_adjoint_operator,
      .sa2_parity_alternating_bracket_and_super_adjoint_square_law => True
  | .sa2_parity_alternating_bracket_and_super_adjoint_square_law,
      .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split => True
  | .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split,
      .sa4_division_free_24_factorial_integer_five_graded_projectors => True
  | .sa4_division_free_24_factorial_integer_five_graded_projectors,
      .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition => True
  | .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition,
      .sa6_exponent_two_galois_cube_and_mod_24_involution_lock => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> simp [causalEdge] <;> infer_instance

/-- Strictly increasing topological rank `0 .. 5`. -/
def toIndex : SuperAdjointCyclotomic24Stage → ℕ
  | .sa1_case_free_chiral_super_adjoint_operator => 0
  | .sa2_parity_alternating_bracket_and_super_adjoint_square_law => 1
  | .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split => 2
  | .sa4_division_free_24_factorial_integer_five_graded_projectors => 3
  | .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition => 4
  | .sa6_exponent_two_galois_cube_and_mod_24_involution_lock => 5

theorem toIndex_injective : Function.Injective toIndex := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder SuperAdjointCyclotomic24Stage :=
  LinearOrder.lift' toIndex toIndex_injective

instance : Fintype SuperAdjointCyclotomic24Stage where
  elems := {
    .sa1_case_free_chiral_super_adjoint_operator,
    .sa2_parity_alternating_bracket_and_super_adjoint_square_law,
    .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split,
    .sa4_division_free_24_factorial_integer_five_graded_projectors,
    .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition,
    .sa6_exponent_two_galois_cube_and_mod_24_involution_lock
  }
  complete x := by cases x <;> simp

theorem card_eq_six : Fintype.card SuperAdjointCyclotomic24Stage = 6 := rfl

theorem causalEdge_lt {a b : SuperAdjointCyclotomic24Stage} (h : causalEdge a b) :
    a.toIndex < b.toIndex := by
  cases a <;> cases b <;> revert h <;> decide

theorem transGen_lt {a b : SuperAdjointCyclotomic24Stage}
    (h : Relation.TransGen causalEdge a b) : a.toIndex < b.toIndex := by
  induction h with
  | single h1 => exact causalEdge_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_lt h2)

/-- **Poset Acyclicity Theorem (`SuperAdjointCyclotomic24Stage.causalEdge_acyclic`)**:
No stage in `𝔖𝔄₁ .. 𝔖𝔄₆` can reach itself along a non-empty directed causal path. -/
theorem causalEdge_acyclic (s : SuperAdjointCyclotomic24Stage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl s.toIndex (transGen_lt h)

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : SuperAdjointCyclotomic24Stage → RepDepth
  | .sa1_case_free_chiral_super_adjoint_operator => .operator
  | .sa2_parity_alternating_bracket_and_super_adjoint_square_law => .operator
  | .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split => .transport
  | .sa4_division_free_24_factorial_integer_five_graded_projectors => .transport
  | .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition => .thermo
  | .sa6_exponent_two_galois_cube_and_mod_24_involution_lock => .thermo

theorem toRepDepth_mono {a b : SuperAdjointCyclotomic24Stage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : SuperAdjointCyclotomic24Stage → OntologyMetaLevel
  | .sa1_case_free_chiral_super_adjoint_operator => .M1_ProjectorClabject
  | .sa2_parity_alternating_bracket_and_super_adjoint_square_law => .M1_ProjectorClabject
  | .sa3_super_sandwich_defect_nilpotent_square_zero_and_higgs_susy_split => .M2_GrassmannianPowertypeOrbit
  | .sa4_division_free_24_factorial_integer_five_graded_projectors => .M2_GrassmannianPowertypeOrbit
  | .sa5_cyclotomic_24_modular_clock_and_octonion_color_composition => .M3_ErlangenCasimirMetaLaw
  | .sa6_exponent_two_galois_cube_and_mod_24_involution_lock => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : SuperAdjointCyclotomic24Stage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end SuperAdjointCyclotomic24Stage

section SuperAdjointCyclotomic24Closure

variable {B : Type*} [Ring B]
variable {A : Type*} [AddCommGroup A]
variable {R : Type*} [CommRing R]

/-- **Universal Case-Free Chiral Super-Adjoint Operator (`superAdjoint S Q X`)**:
In any associative ring `B` with grading involution `S` (`S * S = 1`) and odd generator
`Q` (`S * Q * S = -Q`), `superAdjoint S Q X := Q * X - S * X * S * Q` implements the
Koszul sign `(-1)^{|Q||X|}` across the entire mixed-parity ring `B` without case-splits. -/
def superAdjoint (S Q X : B) : B :=
  Q * X - S * X * S * Q

/-- Helper: If `S * S = 1` and `S * Q * S = -Q`, then `S * Q = -(Q * S)`. -/
theorem odd_generator_anticomm_grading {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) :
    S * Q = -(Q * S) := by
  calc
    S * Q = S * Q * 1 := by rw [mul_one]
    _ = S * Q * (S * S) := by rw [hS]
    _ = (S * Q * S) * S := by noncomm_ring
    _ = (-Q) * S := by rw [hQ]
    _ = -(Q * S) := by noncomm_ring

/-- Helper: Conjugating `superAdjoint S Q X` by `S` flips parity and reverses the ordering:
`S * superAdjoint S Q X * S = -(Q * (S * X * S)) + X * Q`. -/
theorem conj_superAdjoint {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    S * superAdjoint S Q X * S = -(Q * (S * X * S)) + X * Q := by
  have hSQ : S * Q = -(Q * S) := odd_generator_anticomm_grading hS hQ
  dsimp [superAdjoint]
  have h1 : S * (Q * X) * S = -(Q * (S * X * S)) := by
    calc
      S * (Q * X) * S = (S * Q) * X * S := by noncomm_ring
      _ = (-(Q * S)) * X * S := by rw [hSQ]
      _ = -(Q * (S * X * S)) := by noncomm_ring
  have h2 : S * (S * X * S * Q) * S = -(X * Q) := by
    calc
      S * (S * X * S * Q) * S = (S * S) * X * (S * Q * S) := by noncomm_ring
      _ = 1 * X * (-Q) := by rw [hS, hQ]
      _ = -(X * Q) := by noncomm_ring
  calc
    S * (Q * X - S * X * S * Q) * S
        = S * (Q * X) * S - S * (S * X * S * Q) * S := by noncomm_ring
    _ = -(Q * (S * X * S)) - (-(X * Q)) := by rw [h1, h2]
    _ = -(Q * (S * X * S)) + X * Q := by noncomm_ring

/-- **Universal Super-Adjoint Square Theorem (`superAdjoint_sq_eq_comm_sq`)**:
For ANY `S Q X : B` with `S * S = 1` and `S * Q * S = -Q`, the bilateral sandwich
`Q * (S * X * S) * Q` cancels identically in the second application:
`superAdjoint S Q (superAdjoint S Q X) = [Q², X]`. -/
theorem superAdjoint_sq_eq_comm_sq {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    superAdjoint S Q (superAdjoint S Q X) = OperatorAlgebra.PeirceSpine.comm (Q * Q) X := by
  have hConj := conj_superAdjoint hS hQ X
  calc
    superAdjoint S Q (superAdjoint S Q X)
        = Q * superAdjoint S Q X - (S * superAdjoint S Q X * S) * Q := rfl
    _ = Q * (Q * X - S * X * S * Q) - (-(Q * (S * X * S)) + X * Q) * Q := by
          rw [hConj]; rfl
    _ = OperatorAlgebra.PeirceSpine.comm (Q * Q) X := by
          dsimp [OperatorAlgebra.PeirceSpine.comm]
          noncomm_ring

-- theorem-class: constructive endpoint
/-- **Rung 0 & Stages `𝔖𝔄₁, 𝔖𝔄₂, 𝔖𝔄₃` Theorem
(`stage_SA1_SA2_SA3_universal_super_adjoint_square_and_higgs_susy_split`)**:
In any associative ring `B`:
1. **Rung 0 & Stage `𝔖𝔄₁` (Case-Free Chiral Super-Adjoint & Parity-Alternating Brackets)**:
   For any `S Q E O X : B` with `S * S = 1`, `S * Q * S = -Q`, `S * E * S = E` (even),
   and `S * O * S = -O` (odd):
   * `superAdjoint S Q E = comm Q E` (`sad_Q(E) = [Q, E]` on `𝔨`),
   * `superAdjoint S Q O = anticomm Q O` (`sad_Q(O) = {Q, O}` on `𝔭`),
   * **Alternating Commutator–Anticommutator Cancellation**:
     `anticomm Q (comm Q X) = comm (Q * Q) X` (`{Q, [Q, X]} = [Q², X]`),
     `comm Q (anticomm Q X) = comm (Q * Q) X` (`[Q, {Q, X}] = [Q², X]`).
2. **Stage `𝔖𝔄₂` (Universal Case-Free Square Law & Sum/Difference Comparison with `ad_Q²`)**:
   * `superAdjoint S Q (superAdjoint S Q X) = comm (Q * Q) X` (`sad_Q²(X) = [Q², X]` for ALL `X`!),
   * `comm Q (comm Q X) + superAdjoint S Q (superAdjoint S Q X) =
        (2 : ℤ) • (Q * comm Q X)` (`ad_Q²(X) + sad_Q²(X) = 2 Q [Q, X]`),
   * `comm Q (comm Q X) - superAdjoint S Q (superAdjoint S Q X) =
        -((2 : ℤ) • (comm Q X * Q))` (`ad_Q²(X) - sad_Q²(X) = -2 [Q, X] Q`).
3. **Stage `𝔖𝔄₃` (Nilpotent Super-Adjoint Square-Zero Law & Peirce Higgs–SUSY Split)**:
   For any idempotent `P * P = P` and seeds `A_op C_op X : B`, let `SP := invS P`,
   `Np := conePlus P A_op`, `Phi := genPhi P A_op C_op`, `J := genJ P A_op C_op`,
   `V := genV P A_op C_op`:
   * `superAdjoint SP Np (superAdjoint SP Np X) = 0` (`sad_{N_+}²(X) = 0` whereas `ad_{N_+}²(X) = -2 N_+ X N_+`),
   * `superAdjoint SP Phi (superAdjoint SP Phi X) = comm V X` (`sad_Φ²(X) = [V, X]`),
   * `superAdjoint SP Phi (superAdjoint SP Phi J) = 0` (`sad_Φ²(J) = [V, J] = 0`, exact SUSY zero mode!),
   * `comm Phi (comm Phi J) = (4 : ℤ) • (V * J)` (`ad_Φ²(J) = 4 V J`, non-vanishing Higgs/Bohm mass!),
   * `comm Phi (comm Phi J) - superAdjoint SP Phi (superAdjoint SP Phi J) =
        -((4 : ℤ) • (Phi * J * Phi))` (`ad_Φ²(J) - sad_Φ²(J) = -4 Φ J Φ = 4 V J`). -/
theorem stage_SA1_SA2_SA3_universal_super_adjoint_square_and_higgs_susy_split
    {S Q E O : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hE : S * E * S = E) (hO : S * O * S = -O)
    {P : B} (hP : P * P = P) (A_op C_op X : B) :
    let SP := invS P
    let Np := conePlus P A_op
    let Phi := genPhi P A_op C_op
    let J := genJ P A_op C_op
    let V := genV P A_op C_op
    -- (1) Stage 𝔖𝔄₁: Case-free chiral super-adjoint & alternating bracket cancellation
    (superAdjoint S Q E = OperatorAlgebra.PeirceSpine.comm Q E ∧
      superAdjoint S Q O = anticomm Q O ∧
      anticomm Q (OperatorAlgebra.PeirceSpine.comm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      OperatorAlgebra.PeirceSpine.comm Q (anticomm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X) ∧
    -- (2) Stage 𝔖𝔄₂: Universal square sad_Q²(X) = [Q², X] and sum/difference with ad_Q²(X)
    (superAdjoint S Q (superAdjoint S Q X) = OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) +
          superAdjoint S Q (superAdjoint S Q X) =
        (2 : ℤ) • (Q * OperatorAlgebra.PeirceSpine.comm Q X) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q))) ∧
    -- (3) Stage 𝔖𝔄₃: Nilpotent sad_{N_+}² = 0 and Peirce Higgs-SUSY split (sad_Φ²(J) = 0 vs. ad_Φ²(J) = 4VJ)
    (superAdjoint SP Np (superAdjoint SP Np X) = 0 ∧
      superAdjoint SP Phi (superAdjoint SP Phi X) = OperatorAlgebra.PeirceSpine.comm V X ∧
      superAdjoint SP Phi (superAdjoint SP Phi J) = 0 ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi J) =
        (4 : ℤ) • (V * J) ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi J) -
          superAdjoint SP Phi (superAdjoint SP Phi J) =
        -((4 : ℤ) • (Phi * J * Phi))) := by
  intro SP Np Phi J V
  have hSq := superAdjoint_sq_eq_comm_sq hS hQ X
  refine ⟨⟨by dsimp [superAdjoint, OperatorAlgebra.PeirceSpine.comm]; rw [hE],
           by dsimp [superAdjoint, anticomm]; rw [hO]; noncomm_ring,
           by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
           by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring⟩,
    ⟨hSq,
     by
       rw [hSq, two_zsmul]
       dsimp [OperatorAlgebra.PeirceSpine.comm]
       noncomm_ring,
     by
       rw [hSq, two_zsmul]
       dsimp [OperatorAlgebra.PeirceSpine.comm]
       noncomm_ring⟩,
    ⟨by dsimp [SP, Np, superAdjoint]; peirce_nf hP,
     by dsimp [SP, Phi, V, superAdjoint]; peirce_nf hP,
     by dsimp [SP, Phi, J, superAdjoint]; peirce_nf hP,
     by dsimp [Phi, J, V]; peirce_nf hP,
     by dsimp [SP, Phi, J, superAdjoint]; peirce_nf hP⟩⟩

/-- `24 = 4!`-scaled Grade-`0` integer projector:
`proj24Grade0 D x := 24 • x - 30 • D²(x) + 6 • D⁴(x) = 6(D² - I)(D² - 4I)(x)`. -/
def proj24Grade0 (D : A → A) (x : A) : A :=
  (2 : ℤ) • lagrangeShellProj0 D x

/-- `24 = 4!`-scaled Grade-`+1` integer projector:
`proj24GradePlus1 D x := 4 • lagrangeSignedProjPlus1 D x = -4 D(D + I)(D² - 4I)(x)`. -/
def proj24GradePlus1 (D : A → A) (x : A) : A :=
  (4 : ℤ) • lagrangeSignedProjPlus1 D x

/-- `24 = 4!`-scaled Grade-`-1` integer projector:
`proj24GradeMinus1 D x := 4 • lagrangeSignedProjMinus1 D x = -4 D(D - I)(D² - 4I)(x)`. -/
def proj24GradeMinus1 (D : A → A) (x : A) : A :=
  (4 : ℤ) • lagrangeSignedProjMinus1 D x

/-- `24 = 4!`-scaled Grade-`+2` contact integer projector:
`proj24GradePlus2 D x := lagrangeSignedProjPlus2 D x = D(D² - I)(D + 2I)(x)`. -/
def proj24GradePlus2 (D : A → A) (x : A) : A :=
  lagrangeSignedProjPlus2 D x

/-- `24 = 4!`-scaled Grade-`-2` contact integer projector:
`proj24GradeMinus2 D x := lagrangeSignedProjMinus2 D x = D(D² - I)(D - 2I)(x)`. -/
def proj24GradeMinus2 (D : A → A) (x : A) : A :=
  lagrangeSignedProjMinus2 D x

-- theorem-class: constructive endpoint
/-- **Stage `𝔖𝔄₄` Theorem (`stage_SA4_division_free_24_factorial_integer_five_graded_projectors`)**:
1. **Combinatorial Origin of `24 = 4!` at the Contact Roots `λ = ±2`**:
   * `5 * (2 : ℤ) ^ 4 - 15 * (2 : ℤ) ^ 2 + 4 = 24`,
   * `5 * (-2 : ℤ) ^ 4 - 15 * (-2 : ℤ) ^ 2 + 4 = 24`,
   * `(3 : ℕ) * 8 = 24`.
2. **Universal Partition of `24 • v` in `ℤ[D]` (for ANY `D : A → A` and `v : A`)**:
   `proj24GradeMinus2 D v + proj24GradeMinus1 D v + proj24Grade0 D v +
      proj24GradePlus1 D v + proj24GradePlus2 D v = (24 : ℤ) • v`.
3. **Uniform `24 • X_k` Isolation Across All Five Grades of `X = Xm2 + Xm1 + X0 + X1 + X2`**:
   * `proj24GradeMinus2 D X = (24 : ℤ) • Xm2`,
   * `proj24GradeMinus1 D X = (24 : ℤ) • Xm1`,
   * `proj24Grade0 D X = (24 : ℤ) • X0`,
   * `proj24GradePlus1 D X = (24 : ℤ) • X1`,
   * `proj24GradePlus2 D X = (24 : ℤ) • X2`.
4. **Division-Free `24`-Scaled Idempotency & Orthogonality**:
   * `proj24Grade0 D (proj24Grade0 D X) = (24 : ℤ) • proj24Grade0 D X`,
   * `proj24GradePlus1 D (proj24GradePlus1 D X) = (24 : ℤ) • proj24GradePlus1 D X`,
   * `proj24GradeMinus1 D (proj24GradeMinus1 D X) = (24 : ℤ) • proj24GradeMinus1 D X`,
   * `proj24GradePlus2 D (proj24GradePlus2 D X) = (24 : ℤ) • proj24GradePlus2 D X`,
   * `proj24GradeMinus2 D (proj24GradeMinus2 D X) = (24 : ℤ) • proj24GradeMinus2 D X`,
   * `proj24GradePlus1 D (proj24GradeMinus1 D X) = 0`,
   * `proj24GradePlus2 D (proj24GradeMinus2 D X) = 0`,
   * `proj24GradePlus2 D (proj24GradePlus1 D X) = 0`. -/
theorem stage_SA4_division_free_24_factorial_integer_five_graded_projectors
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2) :
    let X := Xm2 + Xm1 + X0 + X1 + X2
    -- (1) Combinatorial derivative P'(±2) = 24 = 3 × 8
    (5 * (2 : ℤ) ^ 4 - 15 * (2 : ℤ) ^ 2 + 4 = 24 ∧
      5 * (-2 : ℤ) ^ 4 - 15 * (-2 : ℤ) ^ 2 + 4 = 24 ∧
      (3 : ℕ) * 8 = 24) ∧
    -- (2) Universal partition of 24 • v
    (proj24GradeMinus2 D v + proj24GradeMinus1 D v + proj24Grade0 D v +
        proj24GradePlus1 D v + proj24GradePlus2 D v = (24 : ℤ) • v) ∧
    -- (3) Uniform 24 • X_k isolation across all five grades
    (proj24GradeMinus2 D X = (24 : ℤ) • Xm2 ∧
      proj24GradeMinus1 D X = (24 : ℤ) • Xm1 ∧
      proj24Grade0 D X = (24 : ℤ) • X0 ∧
      proj24GradePlus1 D X = (24 : ℤ) • X1 ∧
      proj24GradePlus2 D X = (24 : ℤ) • X2) ∧
    -- (4) Division-free 24-scaled idempotency and orthogonality
    (proj24Grade0 D (proj24Grade0 D X) = (24 : ℤ) • proj24Grade0 D X ∧
      proj24GradePlus1 D (proj24GradePlus1 D X) = (24 : ℤ) • proj24GradePlus1 D X ∧
      proj24GradeMinus1 D (proj24GradeMinus1 D X) = (24 : ℤ) • proj24GradeMinus1 D X ∧
      proj24GradePlus2 D (proj24GradePlus2 D X) = (24 : ℤ) • proj24GradePlus2 D X ∧
      proj24GradeMinus2 D (proj24GradeMinus2 D X) = (24 : ℤ) • proj24GradeMinus2 D X ∧
      proj24GradePlus1 D (proj24GradeMinus1 D X) = 0 ∧
      proj24GradePlus2 D (proj24GradeMinus2 D X) = 0 ∧
      proj24GradePlus2 D (proj24GradePlus1 D X) = 0) := by
  intro X
  have hKT3 := stage_KT3_orthogonal_quartic_lagrange_projectors D v hXm2 hXm1 hX0 hX1 hX2
  have hPm2 : proj24GradeMinus2 D X = (24 : ℤ) • Xm2 := hKT3.2.2.1.2.2.2
  have hPm1 : proj24GradeMinus1 D X = (24 : ℤ) • Xm1 := by
    dsimp [proj24GradeMinus1]
    rw [hKT3.2.2.1.2.1, smul_smul]
    rfl
  have hP0 : proj24Grade0 D X = (24 : ℤ) • X0 := by
    dsimp [proj24Grade0]
    rw [hKT3.2.1.1, smul_smul]
    rfl
  have hPp1 : proj24GradePlus1 D X = (24 : ℤ) • X1 := by
    dsimp [proj24GradePlus1]
    rw [hKT3.2.2.1.1, smul_smul]
    rfl
  have hPp2 : proj24GradePlus2 D X = (24 : ℤ) • X2 := hKT3.2.2.1.2.2.1
  refine ⟨⟨by decide, by decide, rfl⟩,
    by
      dsimp [proj24GradeMinus2, proj24GradeMinus1, proj24Grade0,
        proj24GradePlus1, proj24GradePlus2,
        lagrangeShellProj0, lagrangeSignedProjPlus1, lagrangeSignedProjMinus1,
        lagrangeSignedProjPlus2, lagrangeSignedProjMinus2]
      abel,
    ⟨hPm2, hPm1, hP0, hPp1, hPp2⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hP0]
    dsimp [proj24Grade0, lagrangeShellProj0]
    simp only [map_zsmul, hX0, map_zero, smul_zero, sub_zero, add_zero]
    abel
  · rw [hPp1]
    dsimp [proj24GradePlus1, lagrangeSignedProjPlus1]
    simp only [map_zsmul, hX1]
    abel
  · rw [hPm1]
    dsimp [proj24GradeMinus1, lagrangeSignedProjMinus1]
    simp only [map_zsmul, hXm1, map_neg, neg_neg]
    abel
  · rw [hPp2]
    dsimp [proj24GradePlus2, lagrangeSignedProjPlus2]
    simp only [map_zsmul, hX2]
    abel
  · rw [hPm2]
    dsimp [proj24GradeMinus2, lagrangeSignedProjMinus2]
    simp only [map_zsmul, hXm2, map_neg]
    abel
  · rw [hPm1]
    dsimp [proj24GradePlus1, lagrangeSignedProjPlus1]
    simp only [map_zsmul, hXm1, map_neg]
    abel
  · rw [hPm2]
    dsimp [proj24GradePlus2, lagrangeSignedProjPlus2]
    simp only [map_zsmul, hXm2, map_neg]
    abel
  · rw [hPp1]
    dsimp [proj24GradePlus2, lagrangeSignedProjPlus2]
    simp only [map_zsmul, hX1]
    abel

/-- Cyclotomic polynomial `Φ₁(x) = x - 1`. -/
def cycPoly1 (x : R) : R := x - 1
/-- Cyclotomic polynomial `Φ₂(x) = x + 1`. -/
def cycPoly2 (x : R) : R := x + 1
/-- Cyclotomic polynomial `Φ₃(x) = x² + x + 1` (ℤ₃ color triality). -/
def cycPoly3 (x : R) : R := x ^ 2 + x + 1
/-- Cyclotomic polynomial `Φ₄(x) = x² + 1` (complex structure). -/
def cycPoly4 (x : R) : R := x ^ 2 + 1
/-- Cyclotomic polynomial `Φ₆(x) = x² - x + 1`. -/
def cycPoly6 (x : R) : R := x ^ 2 - x + 1
/-- Cyclotomic polynomial `Φ₈(x) = x⁴ + 1`. -/
def cycPoly8 (x : R) : R := x ^ 4 + 1
/-- Cyclotomic polynomial `Φ₁₂(x) = x⁴ - x² + 1`. -/
def cycPoly12 (x : R) : R := x ^ 4 - x ^ 2 + 1
/-- Primitive 24th cyclotomic polynomial `Φ₂₄(x) = x⁸ - x⁴ + 1` (`deg = φ(24) = 8 = dim 𝕆_s`). -/
def cycPoly24 (x : R) : R := x ^ 8 - x ^ 4 + 1

/-- Explicit 8-element unit group `{1, 5, 7, 11, 13, 17, 19, 23}` of residues in `1 .. 24`
coprime to `24`. -/
def unitsMod24Finset : Finset ℤ :=
  {1, 5, 7, 11, 13, 17, 19, 23}

-- theorem-class: constructive endpoint
/-- **Stages `𝔖𝔄₅, 𝔖𝔄₆` Theorem
(`stage_SA5_SA6_cyclotomic_24_octonion_color_composition_and_galois_involution_lock`)**:
1. **Stage `𝔖𝔄₅` (The 24-Cyclotomic Modular Clock & Octonion–Color Composition over `[CommRing R]`)**:
   * **Complete 8-Divisor Factorization of `x²⁴ - 1`**:
     `cycPoly1 x * cycPoly2 x * cycPoly3 x * cycPoly4 x *
        cycPoly6 x * cycPoly8 x * cycPoly12 x * cycPoly24 x = x ^ 24 - 1`,
   * **12-Subclock & Antiperiodic Half-Turn Factorizations**:
     `cycPoly1 x * cycPoly2 x * cycPoly3 x * cycPoly4 x * cycPoly6 x * cycPoly12 x = x ^ 12 - 1`,
     `cycPoly8 x * cycPoly24 x = x ^ 12 + 1`,
     `(x ^ 12 - 1) * (x ^ 12 + 1) = x ^ 24 - 1`,
   * **Octonion–Color Composition Law (`Φ₂₄(x) = Φ₃(-x⁴) = Φ₆(x⁴)`)**:
     `cycPoly24 x = cycPoly3 (-(x ^ 4))`,
     `cycPoly24 x = cycPoly6 (x ^ 4)`.
2. **Stage `𝔖𝔄₆` (Universal Exponent-2 Galois Cube `(ℤ/24ℤ)^×` & `24 ∣ (k² - 1)` Lock)**:
   * **Exact Polynomial Multiples of `24` Across All 4 Coprime Residue Families `12q ± 1, 12q ± 5`**:
     `(12 * q + 1) ^ 2 - 1 = 24 * (6 * q ^ 2 + q)`,
     `(12 * q - 1) ^ 2 - 1 = 24 * (6 * q ^ 2 - q)`,
     `(12 * q + 5) ^ 2 - 1 = 24 * (6 * q ^ 2 + 5 * q + 1)`,
     `(12 * q - 5) ^ 2 - 1 = 24 * (6 * q ^ 2 - 5 * q + 1)`,
   * **Finite 8-Element Galois Unit Cube `unitsMod24Finset` (`φ(24) = 8 = dim 𝕆_s`)**:
     `unitsMod24Finset.card = 8`, and
     `∀ k ∈ unitsMod24Finset, Int.gcd k 24 = 1 ∧ (24 : ℤ) ∣ (k ^ 2 - 1)`. -/
theorem stage_SA5_SA6_cyclotomic_24_octonion_color_composition_and_galois_involution_lock
    (x q : R) :
    -- (1) Stage 𝔖𝔄₅: Complete 24-cyclotomic factorization & Φ₂₄(x) = Φ₃(-x⁴) = Φ₆(x⁴)
    (cycPoly1 x * cycPoly2 x * cycPoly3 x * cycPoly4 x *
        cycPoly6 x * cycPoly8 x * cycPoly12 x * cycPoly24 x = x ^ 24 - 1 ∧
      cycPoly1 x * cycPoly2 x * cycPoly3 x * cycPoly4 x *
          cycPoly6 x * cycPoly12 x = x ^ 12 - 1 ∧
      cycPoly8 x * cycPoly24 x = x ^ 12 + 1 ∧
      (x ^ 12 - 1) * (x ^ 12 + 1) = x ^ 24 - 1 ∧
      cycPoly24 x = cycPoly3 (-(x ^ 4)) ∧
      cycPoly24 x = cycPoly6 (x ^ 4)) ∧
    -- (2) Stage 𝔖𝔄₆: Universal 24-divisibility on 12q ± 1, 12q ± 5 and 8-unit Galois cube
    ((12 * q + 1) ^ 2 - 1 = 24 * (6 * q ^ 2 + q) ∧
      (12 * q - 1) ^ 2 - 1 = 24 * (6 * q ^ 2 - q) ∧
      (12 * q + 5) ^ 2 - 1 = 24 * (6 * q ^ 2 + 5 * q + 1) ∧
      (12 * q - 5) ^ 2 - 1 = 24 * (6 * q ^ 2 - 5 * q + 1) ∧
      unitsMod24Finset.card = 8 ∧
      (∀ k ∈ unitsMod24Finset, Int.gcd k 24 = 1 ∧ (24 : ℤ) ∣ (k ^ 2 - 1))) := by
  refine ⟨⟨by dsimp [cycPoly1, cycPoly2, cycPoly3, cycPoly4, cycPoly6, cycPoly8, cycPoly12, cycPoly24]; ring,
           by dsimp [cycPoly1, cycPoly2, cycPoly3, cycPoly4, cycPoly6, cycPoly12]; ring,
           by dsimp [cycPoly8, cycPoly24]; ring,
           by ring,
           by dsimp [cycPoly24, cycPoly3]; ring,
           by dsimp [cycPoly24, cycPoly6]; ring⟩,
    ⟨by ring, by ring, by ring, by ring, by decide, by decide⟩⟩

-- theorem-class: capstone consumer theorem
/-- **Master Super-Adjoint & 24-Cyclotomic Modular Clock Theorem
(`super_adjoint_and_cyclotomic_24_master_poset`)**:
Unifies the 6-stage poset `𝔖𝔄₁ ≺ 𝔖𝔄₂ ≺ 𝔖𝔄₃ ≺ 𝔖𝔄₄ ≺ 𝔖𝔄₅ ≺ 𝔖𝔄₆`. -/
theorem super_adjoint_and_cyclotomic_24_master_poset
    {S Q E O : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hE : S * E * S = E) (hO : S * O * S = -O)
    {P : B} (hP : P * P = P) (A_op C_op X : B)
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2)
    (x q : R) :
    let SP := invS P
    let Np := conePlus P A_op
    let Phi := genPhi P A_op C_op
    let J := genJ P A_op C_op
    let V := genV P A_op C_op
    let X_sum := Xm2 + Xm1 + X0 + X1 + X2
    -- (1) Poset acyclicity of 𝔖𝔄₁ ≺ ⋯ ≺ 𝔖𝔄₆
    (∀ st : SuperAdjointCyclotomic24Stage,
      ¬ Relation.TransGen SuperAdjointCyclotomic24Stage.causalEdge st st) ∧
    -- (2) Stages 𝔖𝔄₁–𝔖𝔄₃: Case-free super-adjoint square sad_Q²(X) = [Q², X] & Higgs-SUSY split
    (superAdjoint S Q (superAdjoint S Q X) = OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      superAdjoint SP Np (superAdjoint SP Np X) = 0 ∧
      superAdjoint SP Phi (superAdjoint SP Phi J) = 0 ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi J) =
        (4 : ℤ) • (V * J)) ∧
    -- (3) Stage 𝔖𝔄₄: Division-free 24 = 4! integer 5-graded projectors
    (proj24GradeMinus2 D v + proj24GradeMinus1 D v + proj24Grade0 D v +
        proj24GradePlus1 D v + proj24GradePlus2 D v = (24 : ℤ) • v ∧
      proj24GradeMinus2 D X_sum = (24 : ℤ) • Xm2 ∧
      proj24GradeMinus1 D X_sum = (24 : ℤ) • Xm1 ∧
      proj24Grade0 D X_sum = (24 : ℤ) • X0 ∧
      proj24GradePlus1 D X_sum = (24 : ℤ) • X1 ∧
      proj24GradePlus2 D X_sum = (24 : ℤ) • X2) ∧
    -- (4) Stages 𝔖𝔄₅–𝔖𝔄₆: 24-cyclotomic factorization, Φ₂₄(x) = Φ₃(-x⁴) & Galois unit cube
    (cycPoly1 x * cycPoly2 x * cycPoly3 x * cycPoly4 x *
        cycPoly6 x * cycPoly8 x * cycPoly12 x * cycPoly24 x = x ^ 24 - 1 ∧
      cycPoly24 x = cycPoly3 (-(x ^ 4)) ∧
      (12 * q + 1) ^ 2 - 1 = 24 * (6 * q ^ 2 + q) ∧
      (12 * q + 5) ^ 2 - 1 = 24 * (6 * q ^ 2 + 5 * q + 1) ∧
      unitsMod24Finset.card = 8 ∧
      (∀ k ∈ unitsMod24Finset, Int.gcd k 24 = 1 ∧ (24 : ℤ) ∣ (k ^ 2 - 1))) := by
  intro SP Np Phi J V X_sum
  have hSA13 :=
    stage_SA1_SA2_SA3_universal_super_adjoint_square_and_higgs_susy_split
      hS hQ hE hO hP A_op C_op X
  have hSA4 :=
    stage_SA4_division_free_24_factorial_integer_five_graded_projectors
      D v hXm2 hXm1 hX0 hX1 hX2
  have hSA56 :=
    stage_SA5_SA6_cyclotomic_24_octonion_color_composition_and_galois_involution_lock x q
  exact ⟨SuperAdjointCyclotomic24Stage.causalEdge_acyclic,
    ⟨hSA13.2.1.1, hSA13.2.2.1, hSA13.2.2.2.2.1, hSA13.2.2.2.2.2.1⟩,
    ⟨hSA4.2.1, hSA4.2.2.1⟩,
    ⟨hSA56.1.1, hSA56.1.2.2.2.2.1, hSA56.2.1, hSA56.2.2.2.1,
     hSA56.2.2.2.2.2.1, hSA56.2.2.2.2.2.2⟩⟩

end SuperAdjointCyclotomic24Closure

/-! ===========================================================================
    Section 10: The 6-Stage Four-Way Super-Bracket Diamond (`{--, ++, -+, +-}`),
    Asymmetric Super-Adjoint Defect (`ad_Q²(X) - sad_Q²(X) = -2 [Q, X] Q`) vs.
    Symmetric Bilateral Sandwich (`ad_Q²(X) - ac_Q²(X) = -4 Q X Q`), Goldstone
    Zero-Mode Protection (`X = Φ`), & The 24-Isogeny Glue Exact Sequence Poset
    (`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`)
    =========================================================================== -/

/-- The 6 stages of the **Four-Way Super-Bracket Diamond (`{--, ++, -+, +-}`), Asymmetric
Super-Adjoint Defect vs. Symmetric Bilateral Sandwich, Goldstone Zero-Mode Protection, &
The 24-Isogeny Glue Exact Sequence Poset**
(`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`). -/
inductive FourWaySuperBracketGlueStage : Type
  /-- `𝔇𝔐₁`: Four-Way Second-Order Super-Bracket Seed (`(--): [Q,[Q,X]]`, `(++): {Q,{Q,X}}`, `(-+): [Q,{Q,X}]`, `(+-): {Q,[Q,X]}`). -/
  | dm1_four_way_second_order_super_bracket_seed
  /-- `𝔇𝔐₂`: Opposite-Parity Cancellation `[Q, {Q, X}] = {Q, [Q, X]} = [Q², X]` (Bilateral Sandwich `Q X Q` Cancels!). -/
  | dm2_opposite_parity_cancellation_comm_sq
  /-- `𝔇𝔐₃`: Like-Parity Sandwich Split `[Q, [Q, X]] = {Q², X} - 2 Q X Q` and `{Q, {Q, X}} = {Q², X} + 2 Q X Q` (Sandwich Doubles!). -/
  | dm3_like_parity_sandwich_split_anticomm_sq
  /-- `𝔇𝔐₄`: Exact Asymmetric Super-Adjoint Defect `ad_Q²(X) - sad_Q²(X) = -2 [Q, X] Q` vs. Symmetric Sandwich `ad_Q²(X) - ac_Q²(X) = -4 Q X Q`. -/
  | dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich
  /-- `𝔇𝔐₅`: Goldstone Zero-Mode Protection at `X = Q = Φ` (`0 ≠ -4 V Φ`) & Anticommuting `{Q, X} = 0` Coincidence (`-2 [Q, X] Q = -4 Q X Q = 4 Q² X`). -/
  | dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation
  /-- `𝔇𝔐₆`: Division-Free 24-Isogeny Glue Exact Sequence `Σ₂₄ ∘ Ψ₂₄ = 24 id_M`, `Ψ₂₄ ∘ Σ₂₄ = 24 id`, & `24`-Torsion Cokernel Annihilation. -/
  | dm6_twenty_four_isogeny_glue_exact_sequence
  deriving DecidableEq, Repr

namespace FourWaySuperBracketGlueStage

/-- Numerical index `0 .. 5` of `FourWaySuperBracketGlueStage`. -/
def toIndex : FourWaySuperBracketGlueStage → ℕ
  | .dm1_four_way_second_order_super_bracket_seed => 0
  | .dm2_opposite_parity_cancellation_comm_sq => 1
  | .dm3_like_parity_sandwich_split_anticomm_sq => 2
  | .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich => 3
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation => 4
  | .dm6_twenty_four_isogeny_glue_exact_sequence => 5

instance : LinearOrder FourWaySuperBracketGlueStage :=
  LinearOrder.lift' toIndex (by
    intro a b h
    cases a <;> cases b <;> cases h <;> rfl)

instance : Fintype FourWaySuperBracketGlueStage where
  elems := {
    .dm1_four_way_second_order_super_bracket_seed,
    .dm2_opposite_parity_cancellation_comm_sq,
    .dm3_like_parity_sandwich_split_anticomm_sq,
    .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich,
    .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation,
    .dm6_twenty_four_isogeny_glue_exact_sequence
  }
  complete := by intro x; cases x <;> decide

/-- Direct covering relation of the diamond causal poset
`𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`. -/
def causalEdge : FourWaySuperBracketGlueStage → FourWaySuperBracketGlueStage → Prop
  | .dm1_four_way_second_order_super_bracket_seed,
    .dm2_opposite_parity_cancellation_comm_sq => True
  | .dm1_four_way_second_order_super_bracket_seed,
    .dm3_like_parity_sandwich_split_anticomm_sq => True
  | .dm2_opposite_parity_cancellation_comm_sq,
    .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich => True
  | .dm3_like_parity_sandwich_split_anticomm_sq,
    .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich => True
  | .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich,
    .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation => True
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation,
    .dm6_twenty_four_isogeny_glue_exact_sequence => True
  | _, _ => False

instance : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

/-- Every causal edge strictly increases `toIndex`. -/
theorem causalEdge_lt {a b : FourWaySuperBracketGlueStage} (h : causalEdge a b) :
    a.toIndex < b.toIndex := by
  cases a <;> cases b <;> revert h <;> decide

/-- Transitive paths strictly increase `toIndex`. -/
theorem transGen_lt {a b : FourWaySuperBracketGlueStage}
    (h : Relation.TransGen causalEdge a b) :
    a.toIndex < b.toIndex := by
  induction h with
  | single hab => exact causalEdge_lt hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_lt hbc)

/-- Strict acyclicity of `FourWaySuperBracketGlueStage.causalEdge`. -/
theorem causalEdge_acyclic (s : FourWaySuperBracketGlueStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl s.toIndex (transGen_lt h)

private theorem causalEdge_ge_three_of_ge_one {a b : FourWaySuperBracketGlueStage}
    (h : causalEdge a b) (ha : 1 ≤ a.toIndex) :
    3 ≤ b.toIndex := by
  cases a <;> cases b <;> revert h ha <;> decide

private theorem transGen_ge_three_of_ge_one {a b : FourWaySuperBracketGlueStage}
    (h : Relation.TransGen causalEdge a b) (ha : 1 ≤ a.toIndex) :
    3 ≤ b.toIndex := by
  induction h with
  | single hab => exact causalEdge_ge_three_of_ge_one hab ha
  | tail _ hbc ih =>
      exact causalEdge_ge_three_of_ge_one hbc (le_trans (by decide : 1 ≤ 3) ih)

/-- Parallel diamond branches `𝔇𝔐₂` (opposite-parity cancellation) and `𝔇𝔐₃`
(like-parity sandwich split) are causally incomparable prior to their synthesis in `𝔇𝔐₄`. -/
theorem incomparable_DM2_DM3 :
    ¬ Relation.TransGen causalEdge
        .dm2_opposite_parity_cancellation_comm_sq
        .dm3_like_parity_sandwich_split_anticomm_sq ∧
    ¬ Relation.TransGen causalEdge
        .dm3_like_parity_sandwich_split_anticomm_sq
        .dm2_opposite_parity_cancellation_comm_sq := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 := transGen_ge_three_of_ge_one h (by decide)
    revert h3
    decide
  · have h3 := transGen_ge_three_of_ge_one h (by decide)
    revert h3
    decide

/-- Monotone embedding into `RepDepth`. -/
def toRepDepth : FourWaySuperBracketGlueStage → RepDepth
  | .dm1_four_way_second_order_super_bracket_seed => .operator
  | .dm2_opposite_parity_cancellation_comm_sq => .operator
  | .dm3_like_parity_sandwich_split_anticomm_sq => .operator
  | .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich => .transport
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation => .transport
  | .dm6_twenty_four_isogeny_glue_exact_sequence => .thermo

theorem toRepDepth_mono {a b : FourWaySuperBracketGlueStage} (h : causalEdge a b) :
    (toRepDepth a).toNat ≤ (toRepDepth b).toNat := by
  cases a <;> cases b <;> revert h <;> unfold causalEdge toRepDepth RepDepth.toNat <;> decide

/-- Monotone embedding into `OntologyMetaLevel`. -/
def toOntologyMetaLevel : FourWaySuperBracketGlueStage → OntologyMetaLevel
  | .dm1_four_way_second_order_super_bracket_seed => .M1_ProjectorClabject
  | .dm2_opposite_parity_cancellation_comm_sq => .M1_ProjectorClabject
  | .dm3_like_parity_sandwich_split_anticomm_sq => .M1_ProjectorClabject
  | .dm4_asymmetric_super_adjoint_defect_vs_symmetric_sandwich => .M2_GrassmannianPowertypeOrbit
  | .dm5_goldstone_zero_mode_protection_and_anticommuting_reconciliation => .M2_GrassmannianPowertypeOrbit
  | .dm6_twenty_four_isogeny_glue_exact_sequence => .M3_ErlangenCasimirMetaLaw

theorem toOntologyMetaLevel_mono {a b : FourWaySuperBracketGlueStage} (h : causalEdge a b) :
    (toOntologyMetaLevel a).rank ≤ (toOntologyMetaLevel b).rank := by
  cases a <;> cases b <;> revert h <;>
    unfold causalEdge toOntologyMetaLevel OntologyMetaLevel.rank <;> decide

end FourWaySuperBracketGlueStage

section FourWaySuperBracketGlueClosure

variable {B : Type*} [Ring B]
variable {A : Type*} [AddCommGroup A]

/-- Choice-free expansion of `(4 : ℤ) • x` as `x + x + x + x` in any additive group. -/
theorem four_zsmul_eq_add4 {G : Type*} [AddCommGroup G] (x : G) :
    (4 : ℤ) • x = x + x + x + x := by
  have h4 : (4 : ℤ) = 2 + 2 := rfl
  rw [h4, add_zsmul, two_zsmul]
  abel

-- theorem-class: constructive endpoint
/-- **Stages `𝔇𝔐₁, 𝔇𝔐₂, 𝔇𝔐₃, 𝔇𝔐₄` Theorem
(`stage_DM1_DM2_DM3_DM4_four_way_super_bracket_diamond_and_asymmetric_defect`)**:
In any associative ring `B`, for any grading involution `S` (`S * S = 1`), odd generator
`Q` (`S * Q * S = -Q`), and element `X : B`:
1. **Stage `𝔇𝔐₂` (Opposite-Parity Cancellation `(-+)` and `(+-)`)**:
   * `comm Q (anticomm Q X) = comm (Q * Q) X` (`[Q, {Q, X}] = [Q², X]`),
   * `anticomm Q (comm Q X) = comm (Q * Q) X` (`{Q, [Q, X]} = [Q², X]`),
   * `comm Q (anticomm Q X) = anticomm Q (comm Q X)`.
2. **Stage `𝔇𝔐₃` (Like-Parity Sandwich Split `(--)` and `(++)`)**:
   * `comm Q (comm Q X) = anticomm (Q * Q) X - (2 : ℤ) • (Q * X * Q)`
     (`[Q, [Q, X]] = {Q², X} - 2 Q X Q`),
   * `anticomm Q (anticomm Q X) = anticomm (Q * Q) X + (2 : ℤ) • (Q * X * Q)`
     (`{Q, {Q, X}} = {Q², X} + 2 Q X Q`).
3. **Stage `𝔇𝔐₄` (Exact Asymmetric Super-Adjoint Defect vs. Symmetric Bilateral Sandwich)**:
   * `comm Q (comm Q X) - comm (Q * Q) X = (2 : ℤ) • (X * (Q * Q) - Q * X * Q)`,
   * `comm Q (comm Q X) - comm (Q * Q) X = -((2 : ℤ) • (comm Q X * Q))`
     (`[Q, [Q, X]] - [Q², X] = -2 [Q, X] Q`),
   * `comm Q (comm Q X) - superAdjoint S Q (superAdjoint S Q X) = -((2 : ℤ) • (comm Q X * Q))`
     (`ad_Q²(X) - sad_Q²(X) = -2 [Q, X] Q`),
   * `comm Q (comm Q X) - anticomm Q (anticomm Q X) = -((4 : ℤ) • (Q * X * Q))`
     (`ad_Q²(X) - ac_Q²(X) = -4 Q X Q`),
   * `comm Q (comm Q X) + anticomm Q (anticomm Q X) = (2 : ℤ) • anticomm (Q * Q) X`
     (`ad_Q²(X) + ac_Q²(X) = 2 {Q², X}`). -/
theorem stage_DM1_DM2_DM3_DM4_four_way_super_bracket_diamond_and_asymmetric_defect
    {S Q : B} (hS : S * S = 1) (hQ : S * Q * S = -Q) (X : B) :
    -- (1) Stage 𝔇𝔐₂: Opposite-parity cancellation (-+) and (+-)
    (OperatorAlgebra.PeirceSpine.comm Q (anticomm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      anticomm Q (OperatorAlgebra.PeirceSpine.comm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      OperatorAlgebra.PeirceSpine.comm Q (anticomm Q X) =
        anticomm Q (OperatorAlgebra.PeirceSpine.comm Q X)) ∧
    -- (2) Stage 𝔇𝔐₃: Like-parity sandwich split (--) and (++)
    (OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) =
        anticomm (Q * Q) X - (2 : ℤ) • (Q * X * Q) ∧
      anticomm Q (anticomm Q X) =
        anticomm (Q * Q) X + (2 : ℤ) • (Q * X * Q)) ∧
    -- (3) Stage 𝔇𝔐₄: Exact asymmetric defect ad_Q² - sad_Q² = -2[Q,X]Q vs. symmetric ad_Q² - ac_Q² = -4QXQ
    (OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          OperatorAlgebra.PeirceSpine.comm (Q * Q) X =
        (2 : ℤ) • (X * (Q * Q) - Q * X * Q) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          OperatorAlgebra.PeirceSpine.comm (Q * Q) X =
        -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          anticomm Q (anticomm Q X) =
        -((4 : ℤ) • (Q * X * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) +
          anticomm Q (anticomm Q X) =
        (2 : ℤ) • anticomm (Q * Q) X) := by
  have hSq := superAdjoint_sq_eq_comm_sq hS hQ X
  refine ⟨⟨by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
           by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
           by dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring⟩,
    ⟨by rw [two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
     by rw [two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring⟩,
    ⟨by rw [two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring,
     by rw [two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring,
     by rw [hSq, two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring,
     by rw [four_zsmul_eq_add4]; dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
     by rw [two_zsmul]; dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring⟩⟩

-- theorem-class: constructive endpoint
/-- **Rung 0 & Stage `𝔇𝔐₅` Theorem
(`stage_DM5_goldstone_zero_mode_protection_and_anticommuting_reconciliation`)**:
In any associative ring `B`:
1. **Rung 0 Socratic Refutation & Goldstone Zero-Mode Protection (`X = Q` and `X = Q = Φ`)**:
   * On the longitudinal Goldstone mode `X = Q`, `[Q, Q] = 0`, so the true asymmetric
     super-adjoint defect vanishes identically:
     `comm Q (comm Q Q) - superAdjoint S Q (superAdjoint S Q Q) = 0`,
     whereas the symmetric bilateral sandwich difference evaluates to `-4 Q³`:
     `comm Q (comm Q Q) - anticomm Q (anticomm Q Q) = -((4 : ℤ) • (Q * Q * Q))`.
   * Instantiated on `Phi := genPhi P A_op C_op`, `V := genV P A_op C_op`, `SP := invS P`
     (`P * P = P`):
     `comm Phi (comm Phi Phi) - superAdjoint SP Phi (superAdjoint SP Phi Phi) = 0`,
     while the symmetric bilateral sandwich yields the non-zero cubic Casimir
     `comm Phi (comm Phi Phi) - anticomm Phi (anticomm Phi Phi) = -((4 : ℤ) • (V * Phi))` and
     `-((4 : ℤ) • (Phi * Phi * Phi)) = -((4 : ℤ) • (V * Phi))`!
2. **Anticommuting `{Q, X} = 0` Coincidence & Transverse `X = J` Instantiation**:
   * Whenever `anticomm Q X = 0` (`Q * X + X * Q = 0`):
     - `comm Q X = (2 : ℤ) • (Q * X)`,
     - `-((2 : ℤ) • (comm Q X * Q)) = -((4 : ℤ) • (Q * X * Q))`,
     - `-((4 : ℤ) • (Q * X * Q)) = (4 : ℤ) • ((Q * Q) * X)`,
     - `comm Q (comm Q X) - superAdjoint S Q (superAdjoint S Q X) = -((4 : ℤ) • (Q * X * Q))`,
     - `comm Q (comm Q X) - superAdjoint S Q (superAdjoint S Q X) = (4 : ℤ) • ((Q * Q) * X)`.
   * On the transverse Peirce current `J := genJ P A_op C_op`, `anticomm Phi J = 0` holds
     automatically, so the asymmetric defect and symmetric sandwich coincide:
     `-((2 : ℤ) • (comm Phi J * Phi)) = -((4 : ℤ) • (Phi * J * Phi))` and
     `-((4 : ℤ) • (Phi * J * Phi)) = (4 : ℤ) • (V * J)`. -/
theorem stage_DM5_goldstone_zero_mode_protection_and_anticommuting_reconciliation
    {S Q X : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hAnti : anticomm Q X = 0)
    {P : B} (hP : P * P = P) (A_op C_op : B) :
    let SP := invS P
    let Phi := genPhi P A_op C_op
    let J := genJ P A_op C_op
    let V := genV P A_op C_op
    -- (1) Rung 0 & Goldstone zero-mode protection at X = Q and X = Q = Phi
    (OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q Q) -
        superAdjoint S Q (superAdjoint S Q Q) = 0 ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q Q) -
          anticomm Q (anticomm Q Q) =
        -((4 : ℤ) • (Q * Q * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi Phi) -
          superAdjoint SP Phi (superAdjoint SP Phi Phi) = 0 ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi Phi) -
          anticomm Phi (anticomm Phi Phi) =
        -((4 : ℤ) • (V * Phi)) ∧
      -((4 : ℤ) • (Phi * Phi * Phi)) = -((4 : ℤ) • (V * Phi))) ∧
    -- (2) Anticommuting {Q, X} = 0 coincidence and Peirce (Phi, J) instantiation
    (OperatorAlgebra.PeirceSpine.comm Q X = (2 : ℤ) • (Q * X) ∧
      -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) =
        -((4 : ℤ) • (Q * X * Q)) ∧
      -((4 : ℤ) • (Q * X * Q)) = (4 : ℤ) • ((Q * Q) * X) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        -((4 : ℤ) • (Q * X * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        (4 : ℤ) • ((Q * Q) * X) ∧
      anticomm Phi J = 0 ∧
      -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Phi J * Phi)) =
        -((4 : ℤ) • (Phi * J * Phi)) ∧
      -((4 : ℤ) • (Phi * J * Phi)) = (4 : ℤ) • (V * J)) := by
  intro SP Phi J V
  have hSqQ := superAdjoint_sq_eq_comm_sq hS hQ Q
  have hSqX := superAdjoint_sq_eq_comm_sq hS hQ X
  have hXQ : X * Q = -(Q * X) := by
    have h0 : Q * X + X * Q = 0 := hAnti
    calc
      X * Q = (Q * X + X * Q) - Q * X := by noncomm_ring
      _ = 0 - Q * X := by rw [h0]
      _ = -(Q * X) := by noncomm_ring
  have hCommQX : OperatorAlgebra.PeirceSpine.comm Q X = (2 : ℤ) • (Q * X) := by
    rw [two_zsmul]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    rw [hXQ]
    noncomm_ring
  have hAsymSym :
      -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) =
        -((4 : ℤ) • (Q * X * Q)) := by
    rw [two_zsmul, four_zsmul_eq_add4]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    have hXQ_Q : X * Q * Q = -(Q * X * Q) := by
      calc
        X * Q * Q = (X * Q) * Q := by noncomm_ring
        _ = (-(Q * X)) * Q := by rw [hXQ]
        _ = -(Q * X * Q) := by noncomm_ring
    calc
      -((Q * X - X * Q) * Q + (Q * X - X * Q) * Q)
          = -(Q * X * Q - X * Q * Q + (Q * X * Q - X * Q * Q)) := by noncomm_ring
      _ = -(Q * X * Q - (-(Q * X * Q)) + (Q * X * Q - (-(Q * X * Q)))) := by rw [hXQ_Q]
      _ = -(Q * X * Q + Q * X * Q + Q * X * Q + Q * X * Q) := by noncomm_ring
  have hSymCas :
      -((4 : ℤ) • (Q * X * Q)) = (4 : ℤ) • ((Q * Q) * X) := by
    rw [four_zsmul_eq_add4, four_zsmul_eq_add4]
    have hQXQ : Q * X * Q = -((Q * Q) * X) := by
      calc
        Q * X * Q = Q * (X * Q) := by noncomm_ring
        _ = Q * (-(Q * X)) := by rw [hXQ]
        _ = -((Q * Q) * X) := by noncomm_ring
    rw [hQXQ]
    noncomm_ring
  have hDefAsym :
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) := by
    rw [hSqX, two_zsmul]
    dsimp [OperatorAlgebra.PeirceSpine.comm]
    noncomm_ring
  refine ⟨⟨by rw [hSqQ]; dsimp [OperatorAlgebra.PeirceSpine.comm]; noncomm_ring,
           by rw [four_zsmul_eq_add4]; dsimp [OperatorAlgebra.PeirceSpine.comm, anticomm]; noncomm_ring,
           by dsimp [SP, Phi, superAdjoint]; peirce_nf hP,
           by dsimp [Phi, V, anticomm]; peirce_nf hP,
           by dsimp [Phi, V]; peirce_nf hP⟩,
    ⟨hCommQX,
     hAsymSym,
     hSymCas,
     hDefAsym.trans hAsymSym,
     (hDefAsym.trans hAsymSym).trans hSymCas,
     by dsimp [Phi, J, anticomm]; peirce_nf hP,
     by dsimp [Phi, J]; peirce_nf hP,
     by dsimp [Phi, J, V]; peirce_nf hP⟩⟩

/-- **The 5-Tuple 24-Isogeny Analysis Map (`psi24Isogeny D v`)**:
Sends any `v : A` to its 5-tuple of `24 = 4!`-scaled integer Lagrange projections
`(P_{-2}^{(24)}(v), P_{-1}^{(24)}(v), P_0^{(24)}(v), P_{+1}^{(24)}(v), P_{+2}^{(24)}(v))`. -/
def psi24Isogeny (D : A → A) (v : A) : A × A × A × A × A :=
  (proj24GradeMinus2 D v,
   proj24GradeMinus1 D v,
   proj24Grade0 D v,
   proj24GradePlus1 D v,
   proj24GradePlus2 D v)

/-- **The 5-Tuple Synthesis Summation Map (`sigma24Sum t`)**:
Sums a 5-tuple `t = (t_{-2}, t_{-1}, t_0, t_{+1}, t_{+2})` back into `A`. -/
def sigma24Sum (t : A × A × A × A × A) : A :=
  t.1 + t.2.1 + t.2.2.1 + t.2.2.2.1 + t.2.2.2.2

-- theorem-class: constructive endpoint
/-- **Stage `𝔇𝔐₆` Theorem (`stage_DM6_twenty_four_isogeny_glue_exact_sequence`)**:
For any additive group `A`, additive endomorphism `D : A →+ A`, arbitrary `v : A`, and
5-graded eigenvectors `Xm2 Xm1 X0 X1 X2 : A` (`D Xm2 = -((2 : ℤ) • Xm2)`, `D Xm1 = -Xm1`,
`D X0 = 0`, `D X1 = X1`, `D X2 = (2 : ℤ) • X2`):
1. **Universal Left 24-Isogeny Identity (`Σ₂₄ ∘ Ψ₂₄ = 24 id_A` on ALL `v : A`)**:
   `sigma24Sum (psi24Isogeny D v) = (24 : ℤ) • v`.
2. **Right 24-Isogeny Identity on 5-Graded Eigen-Tuples (`Ψ₂₄ ∘ Σ₂₄ = 24 id`)**:
   `psi24Isogeny D (sigma24Sum (Xm2, Xm1, X0, X1, X2)) =
      ((24 : ℤ) • Xm2, (24 : ℤ) • Xm1, (24 : ℤ) • X0, (24 : ℤ) • X1, (24 : ℤ) • X2)`.
3. **24-Scaled Idempotency of `Σ₂₄ ∘ Ψ₂₄` & 24-Torsion Annihilation of the Cokernel Glue**:
   * `sigma24Sum (psi24Isogeny D (sigma24Sum (psi24Isogeny D v))) =
        (24 : ℤ) • sigma24Sum (psi24Isogeny D v)`,
   * `∀ u : A, (24 : ℤ) • u ∈ Set.range (fun w => sigma24Sum (psi24Isogeny D w))`
     (every `24 • u` lies in the image of `Σ₂₄ ∘ Ψ₂₄`, so the cokernel glue group
     `A / im(Σ₂₄ ∘ Ψ₂₄)` is killed by multiplication by `24 = 2³ · 3`). -/
theorem stage_DM6_twenty_four_isogeny_glue_exact_sequence
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2) :
    -- (1) Universal left 24-isogeny Σ₂₄ ∘ Ψ₂₄ = 24 id_A
    sigma24Sum (psi24Isogeny D v) = (24 : ℤ) • v ∧
    -- (2) Right 24-isogeny Ψ₂₄ ∘ Σ₂₄ = 24 id on 5-graded eigen-tuples
    psi24Isogeny D (sigma24Sum (Xm2, Xm1, X0, X1, X2)) =
      ((24 : ℤ) • Xm2, (24 : ℤ) • Xm1, (24 : ℤ) • X0, (24 : ℤ) • X1, (24 : ℤ) • X2) ∧
    -- (3) 24-scaled idempotency and 24-torsion annihilation of the cokernel glue
    sigma24Sum (psi24Isogeny D (sigma24Sum (psi24Isogeny D v))) =
      (24 : ℤ) • sigma24Sum (psi24Isogeny D v) ∧
    (∀ u : A, (24 : ℤ) • u ∈ Set.range (fun w => sigma24Sum (psi24Isogeny D w))) := by
  have hSA4 :=
    stage_SA4_division_free_24_factorial_integer_five_graded_projectors
      D v hXm2 hXm1 hX0 hX1 hX2
  have hLeft : ∀ u : A, sigma24Sum (psi24Isogeny D u) = (24 : ℤ) • u := by
    intro u
    dsimp [sigma24Sum, psi24Isogeny, proj24GradeMinus2, proj24GradeMinus1, proj24Grade0,
      proj24GradePlus1, proj24GradePlus2,
      lagrangeShellProj0, lagrangeSignedProjPlus1, lagrangeSignedProjMinus1,
      lagrangeSignedProjPlus2, lagrangeSignedProjMinus2]
    abel
  refine ⟨hLeft v, ?_, hLeft (sigma24Sum (psi24Isogeny D v)), fun u => ⟨u, hLeft u⟩⟩
  dsimp [psi24Isogeny, sigma24Sum]
  rw [hSA4.2.2.1.1, hSA4.2.2.1.2.1, hSA4.2.2.1.2.2.1, hSA4.2.2.1.2.2.2.1, hSA4.2.2.1.2.2.2.2]

-- theorem-class: capstone consumer theorem
/-- **Master Four-Way Super-Bracket Diamond & 24-Isogeny Glue Theorem
(`four_way_super_bracket_and_24_isogeny_glue_master_poset`)**:
Unifies the 6-stage diamond poset `𝔇𝔐₁ ≺ {𝔇𝔐₂, 𝔇𝔐₃} ≺ 𝔇𝔐₄ ≺ 𝔇𝔐₅ ≺ 𝔇𝔐₆`. -/
theorem four_way_super_bracket_and_24_isogeny_glue_master_poset
    {S Q X : B} (hS : S * S = 1) (hQ : S * Q * S = -Q)
    (hAnti : anticomm Q X = 0)
    {P : B} (hP : P * P = P) (A_op C_op : B)
    (D : A →+ A) (v : A)
    {Xm2 Xm1 X0 X1 X2 : A}
    (hXm2 : D Xm2 = -((2 : ℤ) • Xm2))
    (hXm1 : D Xm1 = -Xm1)
    (hX0 : D X0 = 0)
    (hX1 : D X1 = X1)
    (hX2 : D X2 = (2 : ℤ) • X2) :
    let SP := invS P
    let Phi := genPhi P A_op C_op
    let J := genJ P A_op C_op
    let V := genV P A_op C_op
    -- (1) Poset acyclicity and diamond incomparability of 𝔇𝔐₂ and 𝔇𝔐₃
    ((∀ st : FourWaySuperBracketGlueStage,
        ¬ Relation.TransGen FourWaySuperBracketGlueStage.causalEdge st st) ∧
      ¬ Relation.TransGen FourWaySuperBracketGlueStage.causalEdge
          .dm2_opposite_parity_cancellation_comm_sq
          .dm3_like_parity_sandwich_split_anticomm_sq ∧
      ¬ Relation.TransGen FourWaySuperBracketGlueStage.causalEdge
          .dm3_like_parity_sandwich_split_anticomm_sq
          .dm2_opposite_parity_cancellation_comm_sq) ∧
    -- (2) Stages 𝔇𝔐₁–𝔇𝔐₄: Four-way super-bracket diamond and asymmetric vs. symmetric defect
    (OperatorAlgebra.PeirceSpine.comm Q (anticomm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      anticomm Q (OperatorAlgebra.PeirceSpine.comm Q X) =
        OperatorAlgebra.PeirceSpine.comm (Q * Q) X ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Q X * Q)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          anticomm Q (anticomm Q X) =
        -((4 : ℤ) • (Q * X * Q))) ∧
    -- (3) Stage 𝔇𝔐₅: Goldstone zero-mode protection (X = Phi) and anticommuting reconciliation
    (OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi Phi) -
        superAdjoint SP Phi (superAdjoint SP Phi Phi) = 0 ∧
      OperatorAlgebra.PeirceSpine.comm Phi (OperatorAlgebra.PeirceSpine.comm Phi Phi) -
          anticomm Phi (anticomm Phi Phi) =
        -((4 : ℤ) • (V * Phi)) ∧
      OperatorAlgebra.PeirceSpine.comm Q (OperatorAlgebra.PeirceSpine.comm Q X) -
          superAdjoint S Q (superAdjoint S Q X) =
        (4 : ℤ) • ((Q * Q) * X) ∧
      -((2 : ℤ) • (OperatorAlgebra.PeirceSpine.comm Phi J * Phi)) = (4 : ℤ) • (V * J)) ∧
    -- (4) Stage 𝔇𝔐₆: 24-isogeny glue exact sequence Σ₂₄ ∘ Ψ₂₄ = 24 id and Ψ₂₄ ∘ Σ₂₄ = 24 id
    (sigma24Sum (psi24Isogeny D v) = (24 : ℤ) • v ∧
      psi24Isogeny D (sigma24Sum (Xm2, Xm1, X0, X1, X2)) =
        ((24 : ℤ) • Xm2, (24 : ℤ) • Xm1, (24 : ℤ) • X0, (24 : ℤ) • X1, (24 : ℤ) • X2) ∧
      (∀ u : A, (24 : ℤ) • u ∈ Set.range (fun w => sigma24Sum (psi24Isogeny D w)))) := by
  intro SP Phi J V
  have hDM14 :=
    stage_DM1_DM2_DM3_DM4_four_way_super_bracket_diamond_and_asymmetric_defect hS hQ X
  have hDM5 :=
    stage_DM5_goldstone_zero_mode_protection_and_anticommuting_reconciliation
      hS hQ hAnti hP A_op C_op
  have hDM6 :=
    stage_DM6_twenty_four_isogeny_glue_exact_sequence D v hXm2 hXm1 hX0 hX1 hX2
  exact ⟨⟨FourWaySuperBracketGlueStage.causalEdge_acyclic,
          FourWaySuperBracketGlueStage.incomparable_DM2_DM3.1,
          FourWaySuperBracketGlueStage.incomparable_DM2_DM3.2⟩,
    ⟨hDM14.1.1, hDM14.1.2.1, hDM14.2.2.2.2.1, hDM14.2.2.2.2.2.1⟩,
    ⟨hDM5.1.2.2.1, hDM5.1.2.2.2.1, hDM5.2.2.2.2.2.1,
     hDM5.2.2.2.2.2.2.2.1.trans hDM5.2.2.2.2.2.2.2.2⟩,
    ⟨hDM6.1, hDM6.2.1, hDM6.2.2.2⟩⟩

end FourWaySuperBracketGlueClosure

end InfoGeometry.Canonical.FiveGradedKantorTanakaOspGunaydinGurseyContactPoset
