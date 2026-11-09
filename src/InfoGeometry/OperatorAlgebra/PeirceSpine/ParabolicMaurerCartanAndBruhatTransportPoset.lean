/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Parabolic Maurer–Cartan Calculus, Complete 5-Graded Bracket Table, Internal Odd-Vielbein
# Bichiral Hodge Calculus, and Covariant Bruhat Lax Transport (`𝔐𝔅₁ < ⋯ < 𝔐𝔅₆`)

This module formalizes the complete intermediate coagulation welds (Orders 1, 3, 4, 5, and 6)
of the noncommutative Souriau–Parabolic–Amari–Bruhat operator spine over an arbitrary
associative (noncommutative) ring `B` (`[Ring B]`):

* `MB1` (`node1_units_gauge_maurer_cartan_cocycle_and_inner_gauge_closure`):
  Non-abelian unit gauge covariance `∇^spin_{ω'}(g ψ) = g ∇^spin_ω(ψ)` and
  `∇^ad_{ω'}(g e g⁻¹) = g ∇^ad_ω(e) g⁻¹` for `g : Bˣ`, left Maurer–Cartan 1-cocycle
  `θ_L(g h) = h⁻¹ θ_L(g) h + θ_L(h)`, structural equation `D(θ_L(g)) + θ_L(g)² = g⁻¹ D²(g)`,
  and closure of the fixed locus of a subgroup of inner conjugations by units
  (`metriplecticFlow_innerGaugeInvariant`). This is an inner-gauge action, not Galois data.
* `MB2` (`node2_parabolic_five_graded_complete_bracket_table`):
  Exhaustive 5-graded decomposition `X = X_{-2} + X_{-1} + X_0 + X_{+1} + X_{+2}` and the
  complete 15 unordered grade-pair Lie bracket cases on `ParabolicOp B`.
* `MB3` (`node3_third_order_internal_parabolic_coagulation_welds`):
  Internal DeWitt chiral involution `S_par = 2 weylH² - 1` and unconditional MacDowell–Mansouri
  reflection, internal contact rotating-ball equilibrium, unipotent Maurer–Cartan Weyl dressing
  `g_inv * weylH * g = weylH + θ_W` with flat contact BRST cocycle `d_Q θ_Q + θ_Q² = 0`, and
  five `Poly24` maps with a `24`-scaled decomposition/idempotence law and pairwise cross-zero
  identities. Over arbitrary rings these are scaled projector maps, not literal idempotents.
* `MB4` (`node4_fourth_order_odd_vielbein_horizon_waist_and_quartic_parity`):
  Horizon–waist factorization `Ψ_out(X) + Ψ_in(X) = oddProj X ∈ G_{-1} ⊕ G_{+1}`, full
  4-parameter odd-vielbein rotating-ball equilibrium, bichiral exterior calculus and Hodge
  Laplacian `{d_out, d_in}(Z) = [V, Z]` on `ParabolicOp B`, and the quartic Weyl derivation
  bridge `3(S_par X S_par) = 3X - 8 D²(X) + 2 D⁴(X)`.
* `MB5` (`node5_fifth_order_amari_bundle_flatness_and_bruhat_lax_transport`):
  Algebraic Amari dual connections on `B` (`OpDerivation B`) and exact sum/difference and
  conjugation identities; flatness yields doubled curvature constraints (not cancellation of 2), exponential-family
  para-Kähler section lifts `Γ^{(±1)} = S_P + 2 N_±`, covariant Bruhat Lax transport
  `dP̂_± = [𝒜_G^(e/m), P̂_±]`, Euler vs. modular/Weyl ray specialization of `𝒜^(e) ± 𝒜^(m)`,
  and symmetric single-resolvent Hua–Bergman–Dikin differential sum/difference.
* `MB6` (`node6_sixth_order_three_horizon_super_grassmannian_welds`):
  Dual Weyl (`N_{±1}`) and Para-Kähler (`Ψ_out/in`) partition of the 4-block odd vielbein
  `Φ_odd`, fundamental metric bridge `V_PK = V₁ + N_{+1}² + N_{-1}²` with `ad_H²(V_PK) = 4(N_{+2} + N_{-2})`,
  three-horizon rotating-ball and `Cl(1,1)` Weitzenböck calculus, and three-horizon exterior
  Bruhat projector renormalization `2 P̂_hor,+ = 2 Ψ₁_hor + d_out(Σ_PK)`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.SouriauMetriplecticParabolicPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.AmariParaKahlerConnectionSumDiffPoset

universe u
variable {B : Type u} [Ring B]

/-! ### Ranked Node Enumeration (`𝔐𝔅₁ < ⋯ < 𝔐𝔅₆`)

The order below is a rank order on labels. It records presentation order, not by itself a
causal-dependency theorem; each algebraic dependency is established by the theorem applications
in the downstream declarations. -/

/-- The six ranked labels of the Parabolic Maurer–Cartan & Bruhat Lax Transport synthesis. -/
inductive ParabolicMaurerCartanBruhatNode : Type
  | MB1_UnitsGaugeMaurerCartanInnerConjugationClosure
  | MB2_ParabolicFiveGradedBracketTable
  | MB3_ThirdOrderInternalParabolicWelds
  | MB4_FourthOrderOddVielbeinBichiralHodge
  | MB5_FifthOrderAmariBundleBruhatLaxTransport
  | MB6_SixthOrderThreeHorizonSuperGrassmannian
  deriving DecidableEq, Repr

instance : Inhabited ParabolicMaurerCartanBruhatNode :=
  ⟨.MB1_UnitsGaugeMaurerCartanInnerConjugationClosure⟩

/-- Monotone rank embedding `𝔐𝔅_k ↦ k`. -/
def ParabolicMaurerCartanBruhatNode.rank : ParabolicMaurerCartanBruhatNode → ℕ
  | .MB1_UnitsGaugeMaurerCartanInnerConjugationClosure => 1
  | .MB2_ParabolicFiveGradedBracketTable => 2
  | .MB3_ThirdOrderInternalParabolicWelds => 3
  | .MB4_FourthOrderOddVielbeinBichiralHodge => 4
  | .MB5_FifthOrderAmariBundleBruhatLaxTransport => 5
  | .MB6_SixthOrderThreeHorizonSuperGrassmannian => 6

instance : PartialOrder ParabolicMaurerCartanBruhatNode where
  le a b := a.rank ≤ b.rank
  lt a b := a.rank < b.rank
  le_refl a := Nat.le_refl a.rank
  le_trans _ _ _ hab hbc := Nat.le_trans hab hbc
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_and_not_ge
  le_antisymm a b hab hba := by
    revert hab hba
    cases a <;> cases b <;> decide

instance : DecidableRel (@LE.le ParabolicMaurerCartanBruhatNode _) :=
  fun a b => Nat.decLe a.rank b.rank

instance : DecidableRel (@LT.lt ParabolicMaurerCartanBruhatNode _) :=
  fun a b => Nat.decLt a.rank b.rank

/-! ### Node `𝔐𝔅₁`: Units Gauge Covariance, Left Maurer–Cartan 1-Cocycle & Inner-Conjugation Closure -/

/-- Spin-frame covariant derivative `∇^spin_ω(ψ) = D(ψ) + ω * ψ`. -/
def spinCovariantDeriv (D : OpDerivation B) (ω ψ : B) : B :=
  D.toFun ψ + ω * ψ

/-- Gauge Covariance of the Spin Frame Derivative: `∇^spin_{ω'}(g * ψ) = g * ∇^spin_ω(ψ)`. -/
theorem spinCovariantDeriv_gauge_covariant (D : OpDerivation B) (g : Bˣ) (ω ψ : B) :
    spinCovariantDeriv D (gaugeTransformConn D g ω) ((g : B) * ψ) =
      (g : B) * spinCovariantDeriv D ω ψ := by
  unfold spinCovariantDeriv gaugeTransformConn
  rw [D.leibniz']
  calc (D.toFun (g : B) * ψ + (g : B) * D.toFun ψ) +
         ((g : B) * ω * (↑g⁻¹ : B) - D.toFun (g : B) * (↑g⁻¹ : B)) * ((g : B) * ψ)
      = (D.toFun (g : B) * ψ + (g : B) * D.toFun ψ) +
        (g : B) * ω * ((↑g⁻¹ : B) * (g : B)) * ψ -
        D.toFun (g : B) * ((↑g⁻¹ : B) * (g : B)) * ψ := by noncomm_ring
    _ = (D.toFun (g : B) * ψ + (g : B) * D.toFun ψ) +
        (g : B) * ω * 1 * ψ - D.toFun (g : B) * 1 * ψ := by rw [Units.inv_mul]
    _ = (g : B) * (D.toFun ψ + ω * ψ) := by noncomm_ring

theorem map_gaugeTransformFrame (D : OpDerivation B) (g : Bˣ) (e : B) :
    D.toFun (gaugeTransformFrame g e) =
      (g : B) * D.toFun e * (↑g⁻¹ : B) +
        D.toFun (g : B) * e * (↑g⁻¹ : B) -
        (g : B) * e * (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
  unfold gaugeTransformFrame
  rw [D.leibniz', D.leibniz', D.map_units_inv g]
  noncomm_ring

theorem comm_gaugeTransform (D : OpDerivation B) (g : Bˣ) (ω e : B) :
    comm (gaugeTransformConn D g ω) (gaugeTransformFrame g e) =
      (g : B) * comm ω e * (↑g⁻¹ : B) -
        D.toFun (g : B) * e * (↑g⁻¹ : B) +
        (g : B) * e * (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
  calc comm (gaugeTransformConn D g ω) (gaugeTransformFrame g e)
      = (g : B) * ω * ((↑g⁻¹ : B) * (g : B)) * e * (↑g⁻¹ : B) -
        D.toFun (g : B) * ((↑g⁻¹ : B) * (g : B)) * e * (↑g⁻¹ : B) -
        (g : B) * e * ((↑g⁻¹ : B) * (g : B)) * ω * (↑g⁻¹ : B) +
        (g : B) * e * (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
          unfold gaugeTransformConn gaugeTransformFrame comm
          noncomm_ring
    _ = (g : B) * ω * 1 * e * (↑g⁻¹ : B) -
        D.toFun (g : B) * 1 * e * (↑g⁻¹ : B) -
        (g : B) * e * 1 * ω * (↑g⁻¹ : B) +
        (g : B) * e * (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
          rw [Units.inv_mul]
    _ = (g : B) * comm ω e * (↑g⁻¹ : B) -
        D.toFun (g : B) * e * (↑g⁻¹ : B) +
        (g : B) * e * (↑g⁻¹ : B) * D.toFun (g : B) * (↑g⁻¹ : B) := by
          unfold comm
          noncomm_ring

/-- Gauge Covariance of Modular Vielbein Transport:
`∇^ad_{ω'}(g * e * g⁻¹) = g * ∇^ad_ω(e) * g⁻¹`. -/
theorem adjointCovariantDeriv_gauge_covariant (D : OpDerivation B) (g : Bˣ) (ω e : B) :
    adjointCovariantDeriv D (gaugeTransformConn D g ω) (gaugeTransformFrame g e) =
      gaugeTransformFrame g (adjointCovariantDeriv D ω e) := by
  unfold adjointCovariantDeriv
  rw [map_gaugeTransformFrame, comm_gaugeTransform]
  unfold gaugeTransformFrame
  noncomm_ring

/-- Left-invariant Maurer–Cartan operator form `θ_L(g) = g⁻¹ * D(g)`. -/
def maurerCartanLeft (D : OpDerivation B) (g : Bˣ) : B :=
  (↑g⁻¹ : B) * D.toFun (g : B)

/-- Noncommutative Chain Rule (1-Cocycle Law) for the Left Maurer–Cartan Form:
`θ_L(g * h) = h⁻¹ * θ_L(g) * h + θ_L(h)`. -/
theorem maurerCartanLeft_mul (D : OpDerivation B) (g h : Bˣ) :
    maurerCartanLeft D (g * h) =
      (↑h⁻¹ : B) * maurerCartanLeft D g * (h : B) + maurerCartanLeft D h := by
  unfold maurerCartanLeft
  rw [mul_inv_rev, Units.val_mul, Units.val_mul, D.leibniz']
  calc ((↑h⁻¹ : B) * (↑g⁻¹ : B)) * (D.toFun (g : B) * (h : B) + (g : B) * D.toFun (h : B))
      = (↑h⁻¹ : B) * ((↑g⁻¹ : B) * D.toFun (g : B)) * (h : B) +
        (↑h⁻¹ : B) * ((↑g⁻¹ : B) * (g : B)) * D.toFun (h : B) := by noncomm_ring
    _ = (↑h⁻¹ : B) * ((↑g⁻¹ : B) * D.toFun (g : B)) * (h : B) +
        (↑h⁻¹ : B) * 1 * D.toFun (h : B) := by rw [Units.inv_mul]
    _ = (↑h⁻¹ : B) * ((↑g⁻¹ : B) * D.toFun (g : B)) * (h : B) +
        (↑h⁻¹ : B) * D.toFun (h : B) := by noncomm_ring

/-- Maurer–Cartan Structural Equation with Second-Order Derivation Aporia:
`D(θ_L(g)) + θ_L(g)² = g⁻¹ * D²(g)`. -/
theorem maurerCartan_structural_eq (D : OpDerivation B) (g : Bˣ) :
    D.toFun (maurerCartanLeft D g) + maurerCartanLeft D g * maurerCartanLeft D g =
      (↑g⁻¹ : B) * D.toFun (D.toFun (g : B)) := by
  unfold maurerCartanLeft
  rw [D.leibniz', D.map_units_inv g]
  noncomm_ring

/-- Classical Flat Maurer–Cartan Equation when `D²(g) = 0`: `D(θ_L(g)) + θ_L(g)² = 0`. -/
theorem maurerCartan_flat (D : OpDerivation B) (g : Bˣ)
    (hD : D.toFun (D.toFun (g : B)) = 0) :
    D.toFun (maurerCartanLeft D g) + maurerCartanLeft D g * maurerCartanLeft D g = 0 := by
  rw [maurerCartan_structural_eq, hD, mul_zero]

/-- Inner conjugation `Ad_g(X) = g * X * g⁻¹` of the unit group `Bˣ` on `B`. -/
def innerGaugeAct (g : Bˣ) (X : B) : B := (g : B) * X * (↑g⁻¹ : B)

theorem innerGaugeAct_one (X : B) : innerGaugeAct 1 X = X := by
  unfold innerGaugeAct
  rw [inv_one, Units.val_one]
  noncomm_ring

theorem innerGaugeAct_mul_group (g h : Bˣ) (X : B) :
    innerGaugeAct (g * h) X = innerGaugeAct g (innerGaugeAct h X) := by
  unfold innerGaugeAct
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  noncomm_ring

theorem innerGaugeAct_add (g : Bˣ) (X Y : B) :
    innerGaugeAct g (X + Y) = innerGaugeAct g X + innerGaugeAct g Y := by
  unfold innerGaugeAct; noncomm_ring

theorem innerGaugeAct_sub (g : Bˣ) (X Y : B) :
    innerGaugeAct g (X - Y) = innerGaugeAct g X - innerGaugeAct g Y := by
  unfold innerGaugeAct; noncomm_ring

theorem innerGaugeAct_mul_op (g : Bˣ) (X Y : B) :
    innerGaugeAct g (X * Y) = innerGaugeAct g X * innerGaugeAct g Y := by
  unfold innerGaugeAct
  symm
  calc ((g : B) * X * (↑g⁻¹ : B)) * ((g : B) * Y * (↑g⁻¹ : B))
      = (g : B) * X * ((↑g⁻¹ : B) * (g : B)) * Y * (↑g⁻¹ : B) := by noncomm_ring
    _ = (g : B) * X * 1 * Y * (↑g⁻¹ : B) := by rw [Units.inv_mul]
    _ = (g : B) * (X * Y) * (↑g⁻¹ : B) := by noncomm_ring

theorem innerGaugeAct_comm (g : Bˣ) (X Y : B) :
    innerGaugeAct g (comm X Y) = comm (innerGaugeAct g X) (innerGaugeAct g Y) := by
  unfold comm
  rw [innerGaugeAct_sub, innerGaugeAct_mul_op, innerGaugeAct_mul_op]

theorem innerGaugeAct_anticomm (g : Bˣ) (X Y : B) :
    innerGaugeAct g (anticomm X Y) = anticomm (innerGaugeAct g X) (innerGaugeAct g Y) := by
  unfold anticomm
  rw [innerGaugeAct_add, innerGaugeAct_mul_op, innerGaugeAct_mul_op]

theorem innerGaugeAct_souriauRotational (g : Bˣ) (Ω ρ : B) :
    innerGaugeAct g (souriauRotational Ω ρ) =
      souriauRotational (innerGaugeAct g Ω) (innerGaugeAct g ρ) :=
  innerGaugeAct_comm g Ω ρ

theorem innerGaugeAct_brockettIrrotational (g : Bˣ) (G ρ : B) :
    innerGaugeAct g (brockettIrrotational G ρ) =
      brockettIrrotational (innerGaugeAct g G) (innerGaugeAct g ρ) := by
  unfold brockettIrrotational
  rw [innerGaugeAct_comm, innerGaugeAct_comm]

theorem innerGaugeAct_metriplecticFlow (g : Bˣ) (Ω G ρ : B) :
    innerGaugeAct g (metriplecticFlow Ω G ρ) =
      metriplecticFlow (innerGaugeAct g Ω) (innerGaugeAct g G) (innerGaugeAct g ρ) := by
  unfold metriplecticFlow
  rw [innerGaugeAct_add, innerGaugeAct_souriauRotational, innerGaugeAct_brockettIrrotational]

/-- An operator `X ∈ B` is fixed by every inner conjugation in the subgroup `H ≤ Bˣ`. -/
def IsInnerGaugeInvariant (H : Subgroup Bˣ) (X : B) : Prop :=
  ∀ g ∈ H, innerGaugeAct g X = X

/-- The fixed locus of an inner-conjugation subgroup is preserved by Souriau–Brockett evolution. -/
theorem metriplecticFlow_innerGaugeInvariant (H : Subgroup Bˣ) {Ω G ρ : B}
    (hΩ : IsInnerGaugeInvariant H Ω) (hG : IsInnerGaugeInvariant H G) (hρ : IsInnerGaugeInvariant H ρ) :
    IsInnerGaugeInvariant H (metriplecticFlow Ω G ρ) := by
  intro g hg
  rw [innerGaugeAct_metriplecticFlow, hΩ g hg, hG g hg, hρ g hg]

/-! ### Node `𝔐𝔅₂`: Complete 15-Case 5-Graded Lie Bracket Table on `ParabolicOp B` -/

namespace ParabolicOp

open SouriauMetriplecticParabolicPoset.ParabolicOp

/-- Anticommutator `{X, Y} = X * Y + Y * X` on `ParabolicOp B`. -/
def pAnticomm (X Y : ParabolicOp B) : ParabolicOp B := X * Y + Y * X

/-- Exhaustive 5-Graded Decomposition of `ParabolicOp B`:
`X = X_{-2} + X_{-1} + X_0 + X_{+1} + X_{+2}`. -/
theorem five_graded_decomposition (X : ParabolicOp B) :
    gradeNeg2 X + gradeNeg1 X + gradeZero X + gradePos1 X + gradePos2 X = X := by
  dsimp only [gradeNeg2, gradeNeg1, gradeZero, gradePos1, gradePos2]
  simp only [add_mk]
  ext <;> dsimp <;> abel

/-- Closure of the Levi Subalgebra `[G_0, G_0] ⊆ G_0`. -/
theorem bracket_gradeZero_gradeZero (X Y : ParabolicOp B) :
    pComm (gradeZero X) (gradeZero Y) = gradeZero (pComm (gradeZero X) (gradeZero Y)) := by
  dsimp only [pComm, gradeZero]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Noncommutative Levi Core Theorem: the diagonal entries of `[G_0, G_0]` are the
noncommutative operator commutators `[X.a00, Y.a00]`, `[X.a11, Y.a11]`, `[X.a22, Y.a22]`. -/
theorem bracket_gradeZero_diag (X Y : ParabolicOp B) :
    (pComm (gradeZero X) (gradeZero Y)).a00 = comm X.a00 Y.a00 ∧
    (pComm (gradeZero X) (gradeZero Y)).a11 = comm X.a11 Y.a11 ∧
    (pComm (gradeZero X) (gradeZero Y)).a22 = comm X.a22 Y.a22 := by
  dsimp only [pComm, gradeZero, comm]; simp only [mul_mk, sub_mk]
  refine ⟨by noncomm_ring, by noncomm_ring, by noncomm_ring⟩

/-- Parabolic Adjoint Action `[G_0, G_{+1}] ⊆ G_{+1}`. -/
theorem bracket_gradeZero_gradePos1 (X Y : ParabolicOp B) :
    pComm (gradeZero X) (gradePos1 Y) = gradePos1 (pComm (gradeZero X) (gradePos1 Y)) := by
  dsimp only [pComm, gradeZero, gradePos1]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Parabolic Adjoint Action `[G_0, G_{-1}] ⊆ G_{-1}`. -/
theorem bracket_gradeZero_gradeNeg1 (X Y : ParabolicOp B) :
    pComm (gradeZero X) (gradeNeg1 Y) = gradeNeg1 (pComm (gradeZero X) (gradeNeg1 Y)) := by
  dsimp only [pComm, gradeZero, gradeNeg1]
  ext <;> dsimp <;> noncomm_ring

/-- Opposing Chiral Step Bracket `[G_{+1}, G_{-1}] ⊆ G_0`. -/
theorem bracket_gradePos1_gradeNeg1 (X Y : ParabolicOp B) :
    pComm (gradePos1 X) (gradeNeg1 Y) = gradeZero (pComm (gradePos1 X) (gradeNeg1 Y)) := by
  dsimp only [pComm, gradePos1, gradeNeg1, gradeZero]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Forward Contact Generation (Parabolic Overflow) `[G_{+1}, G_{+1}] ⊆ G_{+2}`. -/
theorem bracket_gradePos1_gradePos1 (X Y : ParabolicOp B) :
    pComm (gradePos1 X) (gradePos1 Y) = gradePos2 (pComm (gradePos1 X) (gradePos1 Y)) := by
  dsimp only [pComm, gradePos1, gradePos2]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Backward Contact Generation (Parabolic Overflow) `[G_{-1}, G_{-1}] ⊆ G_{-2}`. -/
theorem bracket_gradeNeg1_gradeNeg1 (X Y : ParabolicOp B) :
    pComm (gradeNeg1 X) (gradeNeg1 Y) = gradeNeg2 (pComm (gradeNeg1 X) (gradeNeg1 Y)) := by
  dsimp only [pComm, gradeNeg1, gradeNeg2]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Nilpotent Boundary Termination `[G_{+1}, G_{+2}] = 0`. -/
theorem bracket_gradePos1_gradePos2 (X Y : ParabolicOp B) :
    pComm (gradePos1 X) (gradePos2 Y) = 0 := by
  dsimp only [pComm, gradePos1, gradePos2]; simp only [mul_mk, sub_mk, zero_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Nilpotent Boundary Termination `[G_{+2}, G_{+2}] = 0`. -/
theorem bracket_gradePos2_gradePos2 (X Y : ParabolicOp B) :
    pComm (gradePos2 X) (gradePos2 Y) = 0 := by
  dsimp only [pComm, gradePos2]; simp only [mul_mk, sub_mk, zero_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Nilpotent Boundary Termination `[G_{-1}, G_{-2}] = 0`. -/
theorem bracket_gradeNeg1_gradeNeg2 (X Y : ParabolicOp B) :
    pComm (gradeNeg1 X) (gradeNeg2 Y) = 0 := by
  dsimp only [pComm, gradeNeg1, gradeNeg2]; simp only [mul_mk, sub_mk, zero_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Nilpotent Boundary Termination `[G_{-2}, G_{-2}] = 0`. -/
theorem bracket_gradeNeg2_gradeNeg2 (X Y : ParabolicOp B) :
    pComm (gradeNeg2 X) (gradeNeg2 Y) = 0 := by
  dsimp only [pComm, gradeNeg2]; simp only [mul_mk, sub_mk, zero_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Contact-to-Levi Recombination `[G_{+2}, G_{-2}] ⊆ G_0`. -/
theorem bracket_gradePos2_gradeNeg2 (X Y : ParabolicOp B) :
    pComm (gradePos2 X) (gradeNeg2 Y) = gradeZero (pComm (gradePos2 X) (gradeNeg2 Y)) := by
  dsimp only [pComm, gradePos2, gradeNeg2, gradeZero]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Levi action on the grade-`+2` boundary: `[G₀, G₊₂] ⊆ G₊₂`. -/
theorem bracket_gradeZero_gradePos2 (X Y : ParabolicOp B) :
    pComm (gradeZero X) (gradePos2 Y) = gradePos2 (pComm (gradeZero X) (gradePos2 Y)) := by
  dsimp only [pComm, gradeZero, gradePos2]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Levi action on the grade-`-2` boundary: `[G₀, G₋₂] ⊆ G₋₂`. -/
theorem bracket_gradeZero_gradeNeg2 (X Y : ParabolicOp B) :
    pComm (gradeZero X) (gradeNeg2 Y) = gradeNeg2 (pComm (gradeZero X) (gradeNeg2 Y)) := by
  dsimp only [pComm, gradeZero, gradeNeg2]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Opposite contact-step action `[G₊₁, G₋₂] ⊆ G₋₁`. -/
theorem bracket_gradePos1_gradeNeg2 (X Y : ParabolicOp B) :
    pComm (gradePos1 X) (gradeNeg2 Y) = gradeNeg1 (pComm (gradePos1 X) (gradeNeg2 Y)) := by
  dsimp only [pComm, gradePos1, gradeNeg2, gradeNeg1]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-- Opposite contact-step action `[G₋₁, G₊₂] ⊆ G₊₁`. -/
theorem bracket_gradeNeg1_gradePos2 (X Y : ParabolicOp B) :
    pComm (gradeNeg1 X) (gradePos2 Y) = gradePos1 (pComm (gradeNeg1 X) (gradePos2 Y)) := by
  dsimp only [pComm, gradeNeg1, gradePos2, gradePos1]; simp only [mul_mk, sub_mk]
  ext <;> dsimp <;> noncomm_ring

/-! ### Node `𝔐𝔅₃`: Third-Order Internal `ParabolicOp` Coagulation Welds 1–4 -/

/-- Even reductive projection `ω = X_{-2} + X_0 + X_{+2} ∈ 𝔨`. -/
def evenProj (X : ParabolicOp B) : ParabolicOp B :=
  gradeNeg2 X + gradeZero X + gradePos2 X

/-- Odd solder/vielbein projection `e = X_{-1} + X_{+1} ∈ 𝔭`. -/
def oddProj (X : ParabolicOp B) : ParabolicOp B :=
  gradeNeg1 X + gradePos1 X

/-- Weyl-covariant curvature 2-form `F_W(A₁, A₂) = D(A₂) - D(A₁) + [A₁, A₂]`. -/
def weylCurvature (A1 A2 : ParabolicOp B) : ParabolicOp B :=
  D A2 - D A1 + pComm A1 A2

theorem P_hor_eq : (P_hor : ParabolicOp B) = ⟨1, 0, 0, 0, 0, 0, 0, 0, 1⟩ := by
  dsimp only [P_hor, weylH]; simp only [mul_mk]
  ext <;> dsimp <;> noncomm_ring

theorem evenProj_eq (X : ParabolicOp B) :
    evenProj X = ⟨X.a00, 0, X.a02, 0, X.a11, 0, X.a20, 0, X.a22⟩ := by
  dsimp only [evenProj, gradeNeg2, gradeZero, gradePos2]; simp only [add_mk]
  ext <;> dsimp <;> abel

theorem oddProj_eq (X : ParabolicOp B) :
    oddProj X = ⟨0, X.a01, 0, X.a10, 0, X.a12, 0, X.a21, 0⟩ := by
  dsimp only [oddProj, gradeNeg1, gradePos1]; simp only [add_mk]
  ext <;> dsimp <;> abel

/-- **Third-Order Weld 1 (`internal_dewitt_chiral_involution_and_macdowell_mansouri`)**:
Inside `ParabolicOp B`, `P_hor = weylH²` and `S_par = 2 weylH² - 1` satisfy unconditionally:
1. `P_hor * P_hor = P_hor` and `S_par * S_par = 1`,
2. `D S_par = [weylH, S_par] = 0`,
3. `S_par * evenProj X * S_par = evenProj X` and `S_par * oddProj X * S_par = -oddProj X`,
4. `S_par * weylCurvature (ω₁ + e₁) (ω₂ + e₂) * S_par = weylCurvature (ω₁ - e₁) (ω₂ - e₂)`. -/
theorem internal_dewitt_chiral_involution_and_macdowell_mansouri
    (X Y : ParabolicOp B) :
    let ω1 := evenProj X
    let e1 := oddProj X
    let ω2 := evenProj Y
    let e2 := oddProj Y
    (P_hor : ParabolicOp B) * P_hor = P_hor ∧
    (S_par : ParabolicOp B) * S_par = 1 ∧
    D (S_par : ParabolicOp B) = 0 ∧
    S_par * ω1 * S_par = ω1 ∧
    S_par * e1 * S_par = - e1 ∧
    S_par * (ω1 + e1) * S_par = ω1 - e1 ∧
    S_par * weylCurvature (ω1 + e1) (ω2 + e2) * S_par =
      weylCurvature (ω1 - e1) (ω2 - e2) := by
  intro ω1 e1 ω2 e2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [P_hor_eq]; simp only [mul_mk]; ext <;> dsimp <;> noncomm_ring
  · rw [S_par_eq]; simp only [mul_mk, one_mk]; ext <;> dsimp <;> noncomm_ring
  · rw [D_eq, S_par_eq]; simp only [zero_mk]; ext <;> dsimp <;> abel
  · dsimp only [ω1]; rw [S_par_eq, evenProj_eq]; simp only [mul_mk]; ext <;> dsimp <;> noncomm_ring
  · dsimp only [e1]; rw [S_par_eq, oddProj_eq]; simp only [mul_mk, neg_mk]; ext <;> dsimp <;> noncomm_ring
  · dsimp only [ω1, e1]; rw [S_par_eq, evenProj_eq, oddProj_eq]
    simp only [add_mk, sub_mk, mul_mk]; ext <;> dsimp <;> noncomm_ring
  · dsimp only [weylCurvature, pComm, ω1, e1, ω2, e2]
    rw [D_eq (evenProj Y + oddProj Y), D_eq (evenProj X + oddProj X),
        D_eq (evenProj Y - oddProj Y), D_eq (evenProj X - oddProj X),
        S_par_eq, evenProj_eq X, oddProj_eq X, evenProj_eq Y, oddProj_eq Y]
    simp only [add_mk, sub_mk, mul_mk]
    ext <;> dsimp <;> noncomm_ring

/-- **Third-Order Weld 2 (`internal_parabolic_rotating_ball_equilibrium`)**:
For twin contact horizon waves `N_+ = gradePos2 X` and `N_- = gradeNeg2 Y` inside `ParabolicOp B`,
`Σ = weylH * V = V * weylH`, `Σ² = V²`, `-[Φ, [Φ, J]] + 2[Σ, Φ] = 0`, and
`[Σ, [Σ, Φ]] + V[J, [J, Φ]] = 0`. -/
theorem internal_parabolic_rotating_ball_equilibrium
    (X Y : ParabolicOp B) :
    let np := gradePos2 X
    let nm := gradeNeg2 Y
    let ph := np + nm
    let j  := np - nm
    let v  := pAnticomm np nm
    let s  := pComm np nm
    s = weylH * v ∧
    s = v * weylH ∧
    s * s = v * v ∧
    - pComm ph (pComm ph j) + (pComm s ph + pComm s ph) = 0 ∧
    pComm s (pComm s ph) + v * pComm j (pComm j ph) = 0 := by
  intro np nm ph j v s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [np, nm, ph, j, v, s, weylH, pComm, pAnticomm, gradePos2, gradeNeg2]
    simp only [add_mk, sub_mk, neg_mk, mul_mk, zero_mk]
    ext <;> dsimp <;> noncomm_ring

/-- **Third-Order Weld 3 (`unipotent_maurer_cartan_form_and_innerGauge_weyl_dressing`)**:
For `N = gradePos1 X + gradePos2 X`, `g = 1 + N`, and `g_inv = 1 - N + N²`,
proves `g * g_inv = 1`, `g_inv * g = 1`, `θ_W = gradePos1 X + (2 gradePos2 X - (gradePos1 X)²)`,
`g_inv * weylH * g = weylH + θ_W`, `d_Q C (d_Q C g) = 0`, the exact general formula
`d_Q C (d_Q C Z) = - smulZ 2 (gradePos2 C * gradeNeg2 Z * gradePos2 C)`, and `d_Q θ_Q + θ_Q² = 0`. -/
theorem unipotent_maurer_cartan_form_and_innerGauge_weyl_dressing
    (X C Z : ParabolicOp B) :
    let N     := gradePos1 X + gradePos2 X
    let g     := 1 + N
    let g_inv := 1 - N + N * N
    let θ_W   := g_inv * D g
    let θ_Q   := g_inv * d_Q C g
    g * g_inv = 1 ∧
    g_inv * g = 1 ∧
    θ_W = gradePos1 X + (gradePos2 X + gradePos2 X - gradePos1 X * gradePos1 X) ∧
    g_inv * weylH * g = weylH + θ_W ∧
    d_Q C (d_Q C g) = 0 ∧
    d_Q C (d_Q C Z) = - smulZ 2 (gradePos2 C * gradeNeg2 Z * gradePos2 C) ∧
    d_Q C θ_Q + θ_Q * θ_Q = 0 := by
  intro N g g_inv θ_W θ_Q
  have h8 := ParabolicOp.node8_parabolic_maurer_cartan_tower_24_projectors_and_galois X C
  refine ⟨h8.2.2.1, ?_, h8.2.2.2.1, h8.2.2.2.2.1, ?_, ?_, h8.2.2.2.2.2.1⟩
  · dsimp only [g, g_inv, N, gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [g, N, d_Q, pComm, gradePos1, gradePos2]
    simp only [add_mk, sub_mk, mul_mk, one_mk, zero_mk]
    ext <;> dsimp <;> noncomm_ring
  · dsimp only [d_Q, pComm, gradePos2, gradeNeg2, smulZ]
    simp only [mul_mk, sub_mk, neg_mk]
    ext <;> dsimp <;> noncomm_ring

/-- **Third-Order Weld 4 (`poly24_scaled_projector_algebra`)**:
Complete decomposition of `24 • X`, `24`-scaled idempotence, and both directed compositions
vanishing for every distinct pair among the five polynomial grade maps. Since `24` need not be
invertible in an arbitrary ring, these are scaled projector identities, not literal idempotents. -/
theorem poly24_scaled_projector_algebra (X : ParabolicOp B) :
    Poly24_neg2 X + Poly24_neg1 X + Poly24_0 X + Poly24_pos1 X + Poly24_pos2 X = smulZ 24 X ∧
    Poly24_0    (Poly24_0 X)    = smulZ 24 (Poly24_0 X) ∧
    Poly24_pos1 (Poly24_pos1 X) = smulZ 24 (Poly24_pos1 X) ∧
    Poly24_neg1 (Poly24_neg1 X) = smulZ 24 (Poly24_neg1 X) ∧
    Poly24_pos2 (Poly24_pos2 X) = smulZ 24 (Poly24_pos2 X) ∧
    Poly24_neg2 (Poly24_neg2 X) = smulZ 24 (Poly24_neg2 X) ∧
    Poly24_0 (Poly24_pos1 X) = 0 ∧
    Poly24_0 (Poly24_neg1 X) = 0 ∧
    Poly24_0 (Poly24_pos2 X) = 0 ∧
    Poly24_0 (Poly24_neg2 X) = 0 ∧
    Poly24_pos1 (Poly24_neg1 X) = 0 ∧
    Poly24_pos1 (Poly24_pos2 X) = 0 ∧
    Poly24_pos1 (Poly24_neg2 X) = 0 ∧
    Poly24_neg1 (Poly24_pos2 X) = 0 ∧
    Poly24_neg1 (Poly24_neg2 X) = 0 ∧
    Poly24_pos2 (Poly24_neg2 X) = 0 ∧
    Poly24_pos1 (Poly24_0 X) = 0 ∧
    Poly24_neg1 (Poly24_0 X) = 0 ∧
    Poly24_pos2 (Poly24_0 X) = 0 ∧
    Poly24_neg2 (Poly24_0 X) = 0 ∧
    Poly24_neg1 (Poly24_pos1 X) = 0 ∧
    Poly24_pos2 (Poly24_pos1 X) = 0 ∧
    Poly24_neg2 (Poly24_pos1 X) = 0 ∧
    Poly24_pos2 (Poly24_neg1 X) = 0 ∧
    Poly24_neg2 (Poly24_neg1 X) = 0 ∧
    Poly24_neg2 (Poly24_pos2 X) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Poly24_neg2_eq, Poly24_neg1_eq, Poly24_0_eq, Poly24_pos1_eq, Poly24_pos2_eq]
    dsimp only [smulZ, gradeNeg2, gradeNeg1, gradeZero, gradePos1, gradePos2]
    simp only [add_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradeZero]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradePos1]; ext <;> dsimp <;> abel
  · rw [Poly24_neg1_eq (Poly24_neg1 X), Poly24_neg1_eq X]
    dsimp only [smulZ, gradeNeg1]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradePos2]; ext <;> dsimp <;> abel
  · rw [Poly24_neg2_eq (Poly24_neg2 X), Poly24_neg2_eq X]
    dsimp only [smulZ, gradeNeg2]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradeZero, gradePos1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_neg1 X), Poly24_neg1_eq X]
    dsimp only [smulZ, gradeZero, gradeNeg1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradeZero, gradePos2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_0_eq (Poly24_neg2 X), Poly24_neg2_eq X]
    dsimp only [smulZ, gradeZero, gradeNeg2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_neg1 X), Poly24_neg1_eq X]
    dsimp only [smulZ, gradePos1, gradeNeg1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradePos1, gradePos2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_neg2 X), Poly24_neg2_eq X]
    dsimp only [smulZ, gradePos1, gradeNeg2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg1_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradeNeg1, gradePos2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg1_eq (Poly24_neg2 X), Poly24_neg2_eq X]
    dsimp only [smulZ, gradeNeg1, gradeNeg2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_neg2 X), Poly24_neg2_eq X]
    dsimp only [smulZ, gradePos2, gradeNeg2, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos1_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradePos1, gradeZero, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg1_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradeNeg1, gradeZero, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradePos2, gradeZero, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg2_eq (Poly24_0 X), Poly24_0_eq X]
    dsimp only [smulZ, gradeNeg2, gradeZero, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg1_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradeNeg1, gradePos1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradePos2, gradePos1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg2_eq (Poly24_pos1 X), Poly24_pos1_eq X]
    dsimp only [smulZ, gradeNeg2, gradePos1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_pos2_eq (Poly24_neg1 X), Poly24_neg1_eq X]
    dsimp only [smulZ, gradePos2, gradeNeg1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg2_eq (Poly24_neg1 X), Poly24_neg1_eq X]
    dsimp only [smulZ, gradeNeg2, gradeNeg1, zero_mk]; ext <;> dsimp <;> abel
  · rw [Poly24_neg2_eq (Poly24_pos2 X), Poly24_pos2_eq X]
    dsimp only [smulZ, gradeNeg2, gradePos2, zero_mk]; ext <;> dsimp <;> abel

/-! ### Node `𝔐𝔅₄`: Fourth-Order Odd-Vielbein Horizon–Waist Factorization & Bichiral Hodge Calculus -/

/-- Outgoing horizon-to-waist odd spin wave `Ψ_out(X) = P_hor * X * (1 - P_hor) ∈ G_{-1} ⊕ G_{+1}`. -/
def Psi_out (X : ParabolicOp B) : ParabolicOp B :=
  (P_hor : ParabolicOp B) * X * (1 - P_hor)

/-- Ingoing waist-to-horizon odd spin wave `Ψ_in(Y) = (1 - P_hor) * Y * P_hor ∈ G_{-1} ⊕ G_{+1}`. -/
def Psi_in (Y : ParabolicOp B) : ParabolicOp B :=
  (1 - (P_hor : ParabolicOp B)) * Y * P_hor

/-- Chiral parity conjugation `α(Z) = S_par * Z * S_par`. -/
def parConj (Z : ParabolicOp B) : ParabolicOp B :=
  (S_par : ParabolicOp B) * Z * S_par

/-- Outgoing odd-vielbein exterior derivative `d_out(Z) = Ψ_out(X) * Z - α(Z) * Ψ_out(X)`. -/
def d_out (X Z : ParabolicOp B) : ParabolicOp B :=
  Psi_out X * Z - parConj Z * Psi_out X

/-- Ingoing odd-vielbein exterior coderivative `d_in(Z) = Ψ_in(Y) * Z - α(Z) * Ψ_in(Y)`. -/
def d_in (Y Z : ParabolicOp B) : ParabolicOp B :=
  Psi_in Y * Z - parConj Z * Psi_in Y

theorem Psi_out_eq (X : ParabolicOp B) :
    Psi_out X = ⟨0, X.a01, 0, 0, 0, 0, 0, X.a21, 0⟩ := by
  dsimp only [Psi_out]; rw [P_hor_eq]
  simp only [sub_mk, one_mk, mul_mk]
  ext <;> dsimp <;> noncomm_ring

theorem Psi_in_eq (Y : ParabolicOp B) :
    Psi_in Y = ⟨0, 0, 0, Y.a10, 0, Y.a12, 0, 0, 0⟩ := by
  dsimp only [Psi_in]; rw [P_hor_eq]
  simp only [sub_mk, one_mk, mul_mk]
  ext <;> dsimp <;> noncomm_ring

theorem parConj_eq (Z : ParabolicOp B) :
    parConj Z = ⟨Z.a00, -Z.a01, Z.a02, -Z.a10, Z.a11, -Z.a12, Z.a20, -Z.a21, Z.a22⟩ := by
  dsimp only [parConj]; rw [S_par_eq]
  simp only [mul_mk]
  ext <;> dsimp <;> noncomm_ring

/-- **Fourth-Order Weld 1 (`odd_vielbein_horizon_waist_factorization_and_parity`)**:
Horizon–waist factorization of the 4-entry odd vielbein space `G_{-1} ⊕ G_{+1}`, odd chiral
parity, universal square-zero nilpotency, and unit Weyl Laplacian eigenvalue `D² = +1`. -/
theorem odd_vielbein_horizon_waist_factorization_and_parity
    (X Y : ParabolicOp B) :
    Psi_out X + Psi_in X = oddProj X ∧
    parConj (Psi_out X) = - Psi_out X ∧
    parConj (Psi_in Y)  = - Psi_in Y ∧
    Psi_out X * Psi_out Y = 0 ∧
    Psi_in X * Psi_in Y   = 0 ∧
    D2 (Psi_out X) = Psi_out X ∧
    D2 (Psi_in Y)  = Psi_in Y ∧
    D2 (oddProj X) = oddProj X := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Psi_out_eq, Psi_in_eq, oddProj_eq]; simp only [add_mk]; ext <;> dsimp <;> abel
  · rw [parConj_eq (Psi_out X), Psi_out_eq]; simp only [neg_mk]; ext <;> dsimp <;> abel
  · rw [parConj_eq (Psi_in Y), Psi_in_eq]; simp only [neg_mk]; ext <;> dsimp <;> abel
  · rw [Psi_out_eq X, Psi_out_eq Y]; simp only [mul_mk, zero_mk]; ext <;> dsimp <;> noncomm_ring
  · rw [Psi_in_eq X, Psi_in_eq Y]; simp only [mul_mk, zero_mk]; ext <;> dsimp <;> noncomm_ring
  · rw [D2_eq (Psi_out X), Psi_out_eq]; ext <;> dsimp <;> abel
  · rw [D2_eq (Psi_in Y), Psi_in_eq]; ext <;> dsimp <;> abel
  · rw [D2_eq (oddProj X), oddProj_eq]; ext <;> dsimp <;> abel

/-- **Fourth-Order Weld 2 (`full_odd_vielbein_clifford_and_rotating_ball_equilibrium`)**:
Full 4-parameter odd-vielbein Clifford squares, central harmonicity, and 1st/2nd-order
rotating-ball equilibria on `ParabolicOp B`. -/
theorem full_odd_vielbein_clifford_and_rotating_ball_equilibrium
    (X Y : ParabolicOp B) :
    let np := Psi_out X
    let nm := Psi_in Y
    let ph := np + nm
    let j  := np - nm
    let v  := pAnticomm np nm
    let s  := pComm np nm
    parConj ph = - ph ∧
    parConj j  = - j ∧
    parConj v  = v ∧
    parConj s  = s ∧
    s = S_par * v ∧
    s = v * S_par ∧
    ph * ph = v ∧
    j * j   = - v ∧
    s * s   = v * v ∧
    pComm v ph = 0 ∧
    pComm v j  = 0 ∧
    pComm v s  = 0 ∧
    - pComm ph (pComm ph j) + (pComm s ph + pComm s ph) = 0 ∧
    pComm s (pComm s ph) + v * pComm j (pComm j ph) = 0 := by
  intro np nm ph j v s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [np, nm, ph, j, v, s, pComm, pAnticomm]
    try rw [parConj_eq]
    rw [Psi_out_eq X, Psi_in_eq Y]
    try rw [S_par_eq]
    simp only [add_mk, sub_mk, neg_mk, mul_mk, zero_mk]
    ext <;> dsimp <;> first | noncomm_ring | abel

/-- **Fourth-Order Weld 3 (`full_odd_vielbein_bichiral_hodge_laplacian`)**:
Bichiral exterior derivatives `d_out`, `d_in` (`d_out² = d_in² = 0`), graded Leibniz rule,
metric birth `d_out(Φ) = d_in(Φ) = V`, and Hodge–de Rham Laplacian `{d_out, d_in}(Z) = [V, Z]`. -/
theorem full_odd_vielbein_bichiral_hodge_laplacian
    (X Y Z Z1 Z2 : ParabolicOp B) :
    let np := Psi_out X
    let nm := Psi_in Y
    let ph := np + nm
    let j  := np - nm
    let v  := pAnticomm np nm
    d_out X (d_out X Z) = 0 ∧
    d_in Y (d_in Y Z)   = 0 ∧
    d_out X (Z1 * Z2) = d_out X Z1 * Z2 + parConj Z1 * d_out X Z2 ∧
    d_in Y (Z1 * Z2)  = d_in Y Z1 * Z2  + parConj Z1 * d_in Y Z2 ∧
    d_out X nm = v ∧
    d_in Y np  = v ∧
    d_out X ph = v ∧
    d_in Y ph  = v ∧
    d_out X j  = - v ∧
    d_in Y j   = v ∧
    d_out X (d_in Y Z) + d_in Y (d_out X Z) = pComm v Z := by
  intro np nm ph j v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [d_out, d_in, np, nm, ph, j, v, pComm, pAnticomm]
    repeat rw [parConj_eq]
    repeat rw [Psi_out_eq X]
    repeat rw [Psi_in_eq Y]
    simp only [add_mk, sub_mk, neg_mk, mul_mk, zero_mk]
    ext <;> dsimp <;> noncomm_ring

/-- **Fourth-Order Weld 4 (`quartic_weyl_derivation_to_chiral_parity_bridge`)**:
DeWitt chiral parity conjugation `parConj X = S_par X S_par`, `evenProj X`, and `oddProj X`
expressed as pure polynomial functions of `D²` and `D⁴`. -/
theorem quartic_weyl_derivation_to_chiral_parity_bridge
    (X : ParabolicOp B) :
    smulZ 3 (parConj X)  = smulZ 3 X - smulZ 8 (D2 X) + smulZ 2 (D4 X) ∧
    smulZ 6 (evenProj X) = smulZ 6 X - smulZ 8 (D2 X) + smulZ 2 (D4 X) ∧
    smulZ 6 (oddProj X)  = smulZ 8 (D2 X) - smulZ 2 (D4 X) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [parConj_eq, D2_eq, D4_eq]
    dsimp only [smulZ]; simp only [sub_mk, add_mk]; ext <;> dsimp <;> abel
  · rw [evenProj_eq, D2_eq, D4_eq]
    dsimp only [smulZ]; simp only [sub_mk, add_mk]; ext <;> dsimp <;> abel
  · rw [oddProj_eq, D2_eq, D4_eq]
    dsimp only [smulZ]; simp only [sub_mk]; ext <;> dsimp <;> abel

end ParabolicOp

/-! ### Item 4: Explicit Nonzero Metric and Area from Disjoint Nilpotent Matrix Operators -/

/-- Matrix unit `E₀₁` in the concrete `3 × 3` operator algebra `ParabolicOp B`. -/
def disjointE01 : ParabolicOp B := ⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Matrix unit `E₁₀` in the concrete `3 × 3` operator algebra `ParabolicOp B`. -/
def disjointE10 : ParabolicOp B := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- The Peirce metric `E₀₀ + E₁₁` generated by the two disjoint square-zero operators. -/
def disjointMetric : ParabolicOp B := ⟨1, 0, 0, 0, 1, 0, 0, 0, 0⟩

/-- The oriented area operator `E₀₀ - E₁₁` generated by their ordered commutator. -/
def disjointArea : ParabolicOp B := ⟨1, 0, 0, 0, -1, 0, 0, 0, 0⟩

/--
For any nontrivial unital ring (`1 ≠ 0`), these strictly Peirce-disjoint matrix units in the
noncommutative `3 × 3` operator algebra are square-zero, while their anticommutator and ordered
commutator produce nonzero metric and area operators. Nonvanishing is explicitly conditional on
`1 ≠ 0`.
-/
theorem disjoint_nilpotents_generate_nonzero_metric_and_area
    (hOne : (1 : B) ≠ 0) :
    disjointE01 (B := B) * disjointE01 (B := B) = (0 : ParabolicOp B) ∧
    disjointE10 (B := B) * disjointE10 (B := B) = (0 : ParabolicOp B) ∧
    disjointE01 (B := B) * disjointE10 (B := B) = (⟨1, 0, 0, 0, 0, 0, 0, 0, 0⟩ : ParabolicOp B) ∧
    disjointE10 (B := B) * disjointE01 (B := B) = (⟨0, 0, 0, 0, 1, 0, 0, 0, 0⟩ : ParabolicOp B) ∧
    disjointE01 (B := B) * disjointE10 (B := B) + disjointE10 (B := B) * disjointE01 (B := B) = disjointMetric (B := B) ∧
    ParabolicOp.pComm (disjointE01 (B := B)) (disjointE10 (B := B)) = disjointArea (B := B) ∧
    disjointMetric (B := B) ≠ (0 : ParabolicOp B) ∧ disjointArea (B := B) ≠ (0 : ParabolicOp B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : ParabolicOp B) *
      (⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : ParabolicOp B) = _
    ext <;> simp [ParabolicOp.mul_mk]
  · change (⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩ : ParabolicOp B) *
      (⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩ : ParabolicOp B) = _
    ext <;> simp [ParabolicOp.mul_mk]
  · change (⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : ParabolicOp B) *
      (⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩ : ParabolicOp B) = _
    ext <;> simp [ParabolicOp.mul_mk]
  · change (⟨0, 0, 0, 1, 0, 0, 0, 0, 0⟩ : ParabolicOp B) *
      (⟨0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : ParabolicOp B) = _
    ext <;> simp [ParabolicOp.mul_mk]
  · ext <;> simp [disjointE01, disjointE10, disjointMetric, ParabolicOp.mul_mk,
      ParabolicOp.add_mk]
  · ext <;> simp [ParabolicOp.pComm, disjointE01, disjointE10, disjointArea,
      ParabolicOp.mul_mk, ParabolicOp.sub_mk]
  · intro h
    have h00 := congrArg ParabolicOp.a00 h
    exact hOne (by simpa [disjointMetric] using h00)
  · intro h
    have h00 := congrArg ParabolicOp.a00 h
    exact hOne (by simpa [disjointArea] using h00)

/-! ### Node `𝔐𝔅₅`: Algebraic Amari Dual-Flatness, Exponential Sections & Bruhat Lax Transport -/

/-- Self-dual Levi-Civita (`0`-connection) `∇^{(0)}(Z) = D(Z) + [ω, Z]`. -/
def connZero (D : OpDerivation B) (ω Z : B) : B :=
  D.toFun Z + comm ω Z

/-- Amari exponential (`+1`-connection) `∇^{(+1)}(Z) = D(Z) + [ω + e, Z]`. -/
def connExp (D : OpDerivation B) (ω e Z : B) : B :=
  D.toFun Z + comm (ω + e) Z

/-- Amari mixture (`-1`-connection) `∇^{(-1)}(Z) = D(Z) + [ω - e, Z]`. -/
def connMix (D : OpDerivation B) (ω e Z : B) : B :=
  D.toFun Z + comm (ω - e) Z

/-- **Algebraic Amari Dual Connections (`amari_bundle_dual_connections_sum_diff_and_dual_flatness`)**:
Sum `∇^{(+1)} + ∇^{(-1)} = 2 ∇^{(0)}`, difference `∇^{(+1)} - ∇^{(-1)} = 2[e, ·]`, para-Kähler
conjugation `S ∇^{(+1)}(S Z S) S = ∇^{(-1)}(Z)`, and curvature constraints from flatness
(`F₁₂(ω ± e) = 0 ⟹ 2 T₁₂ = 0 ∧ 2 F₁₂(ω) = -2[e₁, e₂]`). Over a general ring these doubled
equalities do not imply `T₁₂ = 0` or `F₁₂(ω) = -[e₁,e₂]` without an additional cancellation
hypothesis. The carrier here is an algebra with derivations, not a bundle. -/
theorem amari_bundle_dual_connections_sum_diff_and_dual_flatness
    (D D1 D2 : OpDerivation B) (S ω ω1 ω2 e e1 e2 Z : B)
    (hS2 : S * S = 1) (hDS : D.toFun S = 0)
    (hω : S * ω * S = ω) (he : S * e * S = -e)
    (hFlatExp : curvature2Form D1 D2 (ω1 + e1) (ω2 + e2) = 0)
    (hFlatMix : curvature2Form D1 D2 (ω1 - e1) (ω2 - e2) = 0) :
    connExp D ω e Z + connMix D ω e Z = connZero D ω Z + connZero D ω Z ∧
    connExp D ω e Z - connMix D ω e Z = comm e Z + comm e Z ∧
    S * connExp D ω e (S * Z * S) * S = connMix D ω e Z ∧
    torsion2Form D1 D2 ω1 ω2 e1 e2 + torsion2Form D1 D2 ω1 ω2 e1 e2 = 0 ∧
    curvature2Form D1 D2 ω1 ω2 + curvature2Form D1 D2 ω1 ω2 =
      - (comm e1 e2 + comm e1 e2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [connExp, connMix, connZero, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub]; abel
  · dsimp [connExp, connMix, comm]
    simp only [add_mul, mul_add, sub_mul, mul_sub]; abel
  · dsimp [connExp, connMix, comm]
    rw [D.leibniz' (S * Z) S, D.leibniz' S Z, hDS]
    simp only [zero_mul, mul_zero, add_zero, zero_add]
    have hS_inv : ∀ U V : B, (S * U * S) * (S * V * S) = S * (U * V) * S := fun U V => by
      calc (S * U * S) * (S * V * S) = S * U * (S * S) * V * S := by noncomm_ring
        _ = S * (U * V) * S := by rw [hS2]; noncomm_ring
    have hSZS2 : S * (S * Z * S) * S = Z := by
      calc S * (S * Z * S) * S = (S * S) * Z * (S * S) := by noncomm_ring
        _ = Z := by rw [hS2]; noncomm_ring
    have hωe : S * (ω + e) * S = ω - e := by
      calc S * (ω + e) * S = S * ω * S + S * e * S := by noncomm_ring
        _ = ω - e := by rw [hω, he]; abel
    have h_left : S * ((ω + e) * (S * Z * S)) * S = (ω - e) * Z := by
      rw [← hS_inv (ω + e) (S * Z * S), hωe, hSZS2]
    have h_right : S * ((S * Z * S) * (ω + e)) * S = Z * (ω - e) := by
      rw [← hS_inv (S * Z * S) (ω + e), hSZS2, hωe]
    have hD : S * (S * D.toFun Z * S) * S = D.toFun Z := by
      calc S * (S * D.toFun Z * S) * S = (S * S) * D.toFun Z * (S * S) := by noncomm_ring
        _ = D.toFun Z := by rw [hS2]; noncomm_ring
    calc S * (S * D.toFun Z * S + ((ω + e) * (S * Z * S) - (S * Z * S) * (ω + e))) * S
      _ = S * (S * D.toFun Z * S) * S + S * ((ω + e) * (S * Z * S)) * S -
          S * ((S * Z * S) * (ω + e)) * S := by noncomm_ring
      _ = D.toFun Z + ((ω - e) * Z - Z * (ω - e)) := by
          rw [hD, h_left, h_right]; noncomm_ring
  · have hDiff_eq : torsion2Form D1 D2 ω1 ω2 e1 e2 + torsion2Form D1 D2 ω1 ω2 e1 e2 =
        curvature2Form D1 D2 (ω1 + e1) (ω2 + e2) - curvature2Form D1 D2 (ω1 - e1) (ω2 - e2) := by
      dsimp only [curvature2Form, torsion2Form, comm]
      rw [D1.map_add', D2.map_add', D1.map_sub', D2.map_sub']
      noncomm_ring
    rw [hDiff_eq, hFlatExp, hFlatMix, sub_self]
  · have hSum_eq : curvature2Form D1 D2 ω1 ω2 + curvature2Form D1 D2 ω1 ω2 =
        (curvature2Form D1 D2 (ω1 + e1) (ω2 + e2) + curvature2Form D1 D2 (ω1 - e1) (ω2 - e2)) -
        (comm e1 e2 + comm e1 e2) := by
      dsimp only [curvature2Form, comm]
      rw [D1.map_add', D2.map_add', D1.map_sub', D2.map_sub']
      noncomm_ring
    rw [hSum_eq, hFlatExp, hFlatMix, add_zero, zero_sub]

/-- Unipotent forward (`+1`) exponential operator family `E_+(P, X) = 1 + N_+` and inverse. -/
def expPlus    (P X : B) : B := 1 + N_plus P X
def expPlusInv (P X : B) : B := 1 - N_plus P X

/-- Unipotent backward (`-1`) mixture operator family `E_-(P, Y) = 1 + N_-` and inverse. -/
def expMinus    (P Y : B) : B := 1 + N_minus P Y
def expMinusInv (P Y : B) : B := 1 - N_minus P Y

/-- Forward (`+1`) exponential-family para-Kähler section `Γ^{(+1)} = E_+⁻¹ S_P E_+`. -/
def GammaExp (P X : B) : B := expPlusInv P X * S_P P * expPlus P X

/-- Backward (`-1`) mixture-family para-Kähler section `Γ^{(-1)} = E_- S_P E_-⁻¹`. -/
def GammaMix (P Y : B) : B := expMinus P Y * S_P P * expMinusInv P Y

/-- **Para-Kähler Sum & Difference of Exterior Connections (`parakahler_sum_and_difference_of_exterior_connections`)**:
Metric compatibility `d_±(V) = 0`, diagonalized frame action `d_sum(Φ) = 2V`, `d_sum(J) = 0`,
`d_diff(Φ) = 0`, `d_diff(J) = -2V`, and opposite Hodge Laplacian squares `d_sum²(Z) = +[V, Z]`,
`d_diff²(Z) = -[V, Z]`. -/
theorem parakahler_sum_and_difference_of_exterior_connections
    (P X Y Z : B) (hP : P * P = P) :
    let sp := S_P P
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    s = sp * v ∧
    s = v * sp ∧
    v = sp * s ∧
    v = s * sp ∧
    d_plus P X v = 0 ∧
    d_minus P Y v = 0 ∧
    d_sum P X Y v = 0 ∧
    d_diff P X Y v = 0 ∧
    d_sum P X Y ph = v + v ∧
    d_sum P X Y j  = 0 ∧
    d_diff P X Y ph = 0 ∧
    d_diff P X Y j  = - (v + v) ∧
    d_sum P X Y (d_sum P X Y Z) = comm v Z ∧
    d_diff P X Y (d_diff P X Y Z) = - comm v Z ∧
    d_sum P X Y (d_sum P X Y Z) + d_diff P X Y (d_diff P X Y Z) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [d_sum, d_diff, d_plus, d_minus, chiralConj,
                Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-- **Action of `d_sum` & `d_diff` on Para-Kähler 2-Form `Σ` (`amari_connection_sum_diff_on_parakahler_symplectic_form`)**:
`d_sum(Σ) = -2 V J = -[Σ, Φ] = -1/2 [Φ, [Φ, J]]` and `d_diff(Σ) = -2 V Φ = -[Σ, J] = 1/2 [J, [J, Φ]]`. -/
theorem amari_connection_sum_diff_on_parakahler_symplectic_form
    (P X Y : B) (hP : P * P = P) :
    let np := N_plus P X
    let nm := N_minus P Y
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    d_plus P X s  = - ((v + v) * np) ∧
    d_minus P Y s = (v + v) * nm ∧
    d_sum P X Y s = - ((v + v) * j) ∧
    d_sum P X Y s = - comm s ph ∧
    d_sum P X Y s + d_sum P X Y s = - comm ph (comm ph j) ∧
    d_diff P X Y s = - ((v + v) * ph) ∧
    d_diff P X Y s = - comm s j ∧
    d_diff P X Y s + d_diff P X Y s = comm j (comm j ph) ∧
    v * (d_diff P X Y s + d_diff P X Y s) = - comm s (comm s ph) ∧
    v * (d_diff P X Y s + d_diff P X Y s) = v * comm j (comm j ph) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [d_sum, d_diff, d_plus, d_minus, chiralConj,
                Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-- **Exponential Operator Family Section Lifts (`exponential_operator_family_lifts_sum_diff_and_fisher_metric`)**:
`Γ^{(+1)} = S_P + 2 N_+`, `Γ^{(-1)} = S_P + 2 N_-`, `(Γ^{(±1)})² = 1`, `Γ^{(+1)} - Γ^{(-1)} = 2 J`,
`{Γ^{(+1)}, Γ^{(-1)}} = 2 + 4 V`, and `[Γ^{(+1)}, Γ^{(-1)}] = 4 Σ - 4 Φ`. -/
theorem exponential_operator_family_lifts_sum_diff_and_fisher_metric
    (P X Y : B) (hP : P * P = P) :
    let sp := S_P P
    let np := N_plus P X
    let nm := N_minus P Y
    let ph := Phi_v P X Y
    let j  := J_mc P X Y
    let v  := V_met P X Y
    let s  := Sigma_sp P X Y
    let gp := GammaExp P X
    let gm := GammaMix P Y
    expPlus P X * expPlusInv P X = 1 ∧
    expMinus P Y * expMinusInv P Y = 1 ∧
    gp = sp + (np + np) ∧
    gm = sp + (nm + nm) ∧
    gp * gp = 1 ∧
    gm * gm = 1 ∧
    gp - gm = j + j ∧
    (gp - sp) + (gm - sp) = ph + ph ∧
    anticomm gp gm = (1 + 1) + (v + v + v + v) ∧
    comm gp gm = (s + s + s + s) - (ph + ph + ph + ph) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [GammaExp, GammaMix, expPlus, expPlusInv, expMinus, expMinusInv,
                Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm, anticomm]
    amari_peirce_nf hP

/-- Primal Bruhat gauge `G_+ = (1 - N_+)(1 + N_-)` and its inverse `G_+⁻¹ = (1 - N_-)(1 + N_+)`. -/
def G_bruhat_e    (P X Y : B) : B := (1 - N_plus P X) * (1 + N_minus P Y)
def G_bruhat_eInv (P X Y : B) : B := (1 - N_minus P Y) * (1 + N_plus P X)

/-- Dual Bruhat gauge `G_- = (1 + N_-)(1 - N_+)` and its inverse `G_-⁻¹ = (1 + N_+)(1 - N_-)`. -/
def G_bruhat_m    (P X Y : B) : B := (1 + N_minus P Y) * (1 - N_plus P X)
def G_bruhat_mInv (P X Y : B) : B := (1 + N_plus P X) * (1 - N_minus P Y)

/-- Tangent differential `dG_+ = (-dN_+)(1 + N_-) + (1 - N_+)(dN_-)` of `G_+`. -/
def dG_bruhat_e (P X Y dX dY : B) : B :=
  (- N_plus P dX) * (1 + N_minus P Y) + (1 - N_plus P X) * N_minus P dY

/-- Tangent differential `dG_- = (dN_-)(1 - N_+) + (1 + N_-)(-dN_+)` of `G_-`. -/
def dG_bruhat_m (P X Y dX dY : B) : B :=
  N_minus P dY * (1 - N_plus P X) + (1 + N_minus P Y) * (- N_plus P dX)

/-- Right-invariant Bruhat Maurer–Cartan connection 1-forms `𝒜_G^(e)` and `𝒜_G^(m)`. -/
def MC_Bruhat_e (P X Y dX dY : B) : B := dG_bruhat_e P X Y dX dY * G_bruhat_eInv P X Y
def MC_Bruhat_m (P X Y dX dY : B) : B := dG_bruhat_m P X Y dX dY * G_bruhat_mInv P X Y

/-- Leibniz differential `dV = d(N_+ N_- + N_- N_+)` of the metric `V`. -/
def dV (P X Y dX dY : B) : B :=
  (N_plus P dX * N_minus P Y + N_plus P X * N_minus P dY) +
  (N_minus P dY * N_plus P X + N_minus P Y * N_plus P dX)

/-- Tangent differential `dP̂_+ = dΦ - dΣ - (dV) N_+ - V (dN_+)`. -/
def dP_hat_e (P X Y dX dY : B) : B :=
  (N_plus P dX + N_minus P dY) - dSigma P X Y dX dY -
  (dV P X Y dX dY * N_plus P X + V_met P X Y * N_plus P dX)

/-- Tangent differential `dP̂_- = dΦ - dΣ - (dV) N_- - V (dN_-)`. -/
def dP_hat_m (P X Y dX dY : B) : B :=
  (N_plus P dX + N_minus P dY) - dSigma P X Y dX dY -
  (dV P X Y dX dY * N_minus P Y + V_met P X Y * N_minus P dY)

/-- **Fifth-Order Weld 1 (`bruhat_gauge_conjugation_idempotence_and_difference`)**:
First-principles Bruhat gauge conjugation `G_± P G_±⁻¹ = P̂_±`, idempotence `P̂_±² = P̂_±`,
and difference `P̂_- - P̂_+ = V J = Σ Φ`. -/
theorem bruhat_gauge_conjugation_idempotence_and_difference
    (P X Y : B) (hP : P * P = P) :
    let Ge    := G_bruhat_e P X Y
    let GeInv := G_bruhat_eInv P X Y
    let Gm    := G_bruhat_m P X Y
    let GmInv := G_bruhat_mInv P X Y
    let Pe    := P_hat_plus P X Y
    let Pm    := P_hat_minus P X Y
    Ge * GeInv = 1 ∧
    Gm * GmInv = 1 ∧
    Gm - Ge = Sigma_sp P X Y ∧
    Ge * P * GeInv = Pe ∧
    Gm * P * GmInv = Pm ∧
    Pe * Pe = Pe ∧
    Pm * Pm = Pm ∧
    Pm - Pe = V_met P X Y * J_mc P X Y ∧
    Pm - Pe = Sigma_sp P X Y * Phi_v P X Y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [G_bruhat_e, G_bruhat_eInv, G_bruhat_m, G_bruhat_mInv,
                P_hat_plus, P_hat_minus, Psi1, Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg]
    amari_peirce_nf hP

/-- **Fifth-Order Weld 2 (`bruhat_projector_covariant_maurer_cartan_transport`)**:
Covariant Lax / Maurer–Cartan transport `dP̂_+ = [𝒜_G^(e), P̂_+]`, `dP̂_- = [𝒜_G^(m), P̂_-]`,
and `[𝒜_G^(m), P̂_-] - [𝒜_G^(e), P̂_+] = (dV) J + V (dJ)`. -/
theorem bruhat_projector_covariant_maurer_cartan_transport
    (P X Y dX dY : B) (hP : P * P = P) :
    let AG_e := MC_Bruhat_e P X Y dX dY
    let AG_m := MC_Bruhat_m P X Y dX dY
    let Pe   := P_hat_plus P X Y
    let Pm   := P_hat_minus P X Y
    let dPe  := dP_hat_e P X Y dX dY
    let dPm  := dP_hat_m P X Y dX dY
    dPe = comm AG_e Pe ∧
    dPm = comm AG_m Pm ∧
    comm AG_m Pm - comm AG_e Pe =
      dV P X Y dX dY * J_mc P X Y + V_met P X Y * (N_plus P dX - N_minus P dY) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp only [MC_Bruhat_e, MC_Bruhat_m, dG_bruhat_e, dG_bruhat_m,
                G_bruhat_eInv, G_bruhat_mInv, P_hat_plus, P_hat_minus, Psi1,
                dP_hat_e, dP_hat_m, dV, dSigma, Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    amari_peirce_nf hP

/-- **Fifth-Order Weld 3 (`maurer_cartan_euler_and_modular_ray_bridges`)**:
Gaussian Maurer–Cartan connection sum and difference `𝒜^(e) ± 𝒜^(m)` evaluated along the
Euler radial ray (`dX = X, dY = Y`) vs. the modular/Weyl horizon ray (`dX = X, dY = -Y`,
where `4 V (𝒜_P^(e) - 𝒜_P^(m)) = [Σ, [Σ, Φ]] = -V[J, [J, Φ]]`). -/
theorem maurer_cartan_euler_and_modular_ray_bridges
    (P X Y : B) (hP : P * P = P) :
    let ph     := Phi_v P X Y
    let j      := J_mc P X Y
    let v      := V_met P X Y
    let s      := Sigma_sp P X Y
    let Pe     := P_hat_plus P X Y
    let Pm     := P_hat_minus P X Y
    let Ae_rad := MC_Conn_e P X Y X Y
    let Am_rad := MC_Conn_m P X Y X Y
    let Ae_mod := MC_Conn_e P X Y X (-Y)
    let Am_mod := MC_Conn_m P X Y X (-Y)
    Ae_rad - Am_rad = (s + s) - v * j ∧
    Ae_rad - Am_rad = (s + s) - (Pm - Pe) ∧
    Ae_rad + Am_rad = (ph + ph) - v * ph ∧
    Ae_mod - Am_mod = v * ph ∧
    (v + v + v + v) * (Ae_mod - Am_mod) = comm s (comm s ph) ∧
    (v + v + v + v) * (Ae_mod - Am_mod) = - (v * comm j (comm j ph)) ∧
    Ae_mod + Am_mod = (j + j) - (s + s) + v * j := by
  have h_neg : N_minus P (-Y) = - N_minus P Y := by
    dsimp only [N_minus]; noncomm_ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [MC_Conn_e, MC_Conn_m, P_hat_plus, P_hat_minus, Psi1,
                Phi_v, J_mc, V_met, Sigma_sp, Q_pos, Q_neg, comm]
    try rw [h_neg]
    amari_peirce_nf hP

/-- **Fifth-Order Weld 4 (`symmetric_single_resolvent_hua_bergman_dikin_sum_and_diff`)**:
Single-resolvent `R_V = (1 - V)⁻¹` centrality (`[R_V, N_±] = 0`) and symmetric collapse of
both primal and dual Legendre differentials `dη_- + dη_+ = R_V dΦ R_V` and `dη_- - dη_+ = R_V dJ R_V`. -/
theorem symmetric_single_resolvent_hua_bergman_dikin_sum_and_diff
    (P X Y dX dY Rv : B) (hP : P * P = P)
    (hRv_l : Rv * (1 - V_met P X Y) = 1)
    (hRv_r : (1 - V_met P X Y) * Rv = 1) :
    let np     := N_plus P X
    let nm     := N_minus P Y
    let dnp    := N_plus P dX
    let dnm    := N_minus P dY
    let dph    := dnp + dnm
    let dj     := dnp - dnm
    let deta_m := Rv * dnp + Rv * dnp * nm * (Rv * np)
    let deta_p := Rv * dnm + Rv * dnm * np * (Rv * nm)
    Rv * np = np * Rv ∧
    Rv * nm = nm * Rv ∧
    deta_m = Rv * dnp * Rv ∧
    deta_p = Rv * dnm * Rv ∧
    deta_m + deta_p = Rv * dph * Rv ∧
    deta_m - deta_p = Rv * dj * Rv := by
  have h_comm_np : (1 - V_met P X Y) * N_plus P X = N_plus P X * (1 - V_met P X Y) := by
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  have h_comm_nm : (1 - V_met P X Y) * N_minus P Y = N_minus P Y * (1 - V_met P X Y) := by
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  have h_Rv_np : Rv * N_plus P X = N_plus P X * Rv := by
    calc Rv * N_plus P X
      _ = Rv * N_plus P X * ((1 - V_met P X Y) * Rv) := by rw [hRv_r, mul_one]
      _ = Rv * (N_plus P X * (1 - V_met P X Y)) * Rv := by simp only [mul_assoc]
      _ = (Rv * (1 - V_met P X Y)) * N_plus P X * Rv := by rw [← h_comm_np]; simp only [mul_assoc]
      _ = N_plus P X * Rv                            := by rw [hRv_l, one_mul]
  have h_Rv_nm : Rv * N_minus P Y = N_minus P Y * Rv := by
    calc Rv * N_minus P Y
      _ = Rv * N_minus P Y * ((1 - V_met P X Y) * Rv) := by rw [hRv_r, mul_one]
      _ = Rv * (N_minus P Y * (1 - V_met P X Y)) * Rv := by simp only [mul_assoc]
      _ = (Rv * (1 - V_met P X Y)) * N_minus P Y * Rv := by rw [← h_comm_nm]; simp only [mul_assoc]
      _ = N_minus P Y * Rv                            := by rw [hRv_l, one_mul]
  have h_dnp_V : N_plus P dX * V_met P X Y = N_plus P dX * Q_neg P X Y := by
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  have h_dnm_V : N_minus P dY * V_met P X Y = N_minus P dY * Q_pos P X Y := by
    dsimp only [V_met, Q_pos, Q_neg]; amari_peirce_nf hP
  have h_abs_p : N_plus P dX + N_plus P dX * Q_neg P X Y * Rv = N_plus P dX * Rv := by
    calc N_plus P dX + N_plus P dX * Q_neg P X Y * Rv
      _ = N_plus P dX * ((1 - V_met P X Y) * Rv) + N_plus P dX * Q_neg P X Y * Rv := by
          rw [hRv_r, mul_one]
      _ = (N_plus P dX - N_plus P dX * V_met P X Y + N_plus P dX * Q_neg P X Y) * Rv := by
          noncomm_ring
      _ = N_plus P dX * Rv := by rw [h_dnp_V]; noncomm_ring
  have h_abs_m : N_minus P dY + N_minus P dY * Q_pos P X Y * Rv = N_minus P dY * Rv := by
    calc N_minus P dY + N_minus P dY * Q_pos P X Y * Rv
      _ = N_minus P dY * ((1 - V_met P X Y) * Rv) + N_minus P dY * Q_pos P X Y * Rv := by
          rw [hRv_r, mul_one]
      _ = (N_minus P dY - N_minus P dY * V_met P X Y + N_minus P dY * Q_pos P X Y) * Rv := by
          noncomm_ring
      _ = N_minus P dY * Rv := by rw [h_dnm_V]; noncomm_ring
  have h_deta_m : Rv * N_plus P dX + Rv * N_plus P dX * N_minus P Y * (Rv * N_plus P X) =
      Rv * N_plus P dX * Rv := by
    calc Rv * N_plus P dX + Rv * N_plus P dX * N_minus P Y * (Rv * N_plus P X)
      _ = Rv * N_plus P dX + Rv * N_plus P dX * N_minus P Y * (N_plus P X * Rv) := by
          rw [h_Rv_np]
      _ = Rv * (N_plus P dX + N_plus P dX * Q_neg P X Y * Rv) := by
          dsimp [Q_neg]; noncomm_ring
      _ = Rv * N_plus P dX * Rv := by rw [h_abs_p]; noncomm_ring
  have h_deta_p : Rv * N_minus P dY + Rv * N_minus P dY * N_plus P X * (Rv * N_minus P Y) =
      Rv * N_minus P dY * Rv := by
    calc Rv * N_minus P dY + Rv * N_minus P dY * N_plus P X * (Rv * N_minus P Y)
      _ = Rv * N_minus P dY + Rv * N_minus P dY * N_plus P X * (N_minus P Y * Rv) := by
          rw [h_Rv_nm]
      _ = Rv * (N_minus P dY + N_minus P dY * Q_pos P X Y * Rv) := by
          dsimp [Q_pos]; noncomm_ring
      _ = Rv * N_minus P dY * Rv := by rw [h_abs_m]; noncomm_ring
  refine ⟨h_Rv_np, h_Rv_nm, h_deta_m, h_deta_p, ?_, ?_⟩
  · rw [h_deta_m, h_deta_p]; noncomm_ring
  · rw [h_deta_m, h_deta_p]; noncomm_ring

/-! ### Node `𝔐𝔅₆`: Sixth-Order Three-Horizon Super-Grassmannian Coagulation Welds 1–4 -/

/-- Central waist projector `P₀ = 1 - P₁ - P₂`. -/
def P0_waist (P1 P2 : B) : B := 1 - P1 - P2

/-- Tripotent Weyl/modular dilation generator `H = P₁ - P₂` (`H³ = H`). -/
def H_weyl (P1 P2 : B) : B := P1 - P2

/-- Horizon idempotent `P_hor3 = H² = P₁ + P₂` (`P_hor3² = P_hor3`). -/
def P_hor3 (P1 P2 : B) : B := P1 + P2

/-- Internal DeWitt para-Kähler involution `S_par3 = 2 H² - 1` (`S_par3² = 1`). -/
def S_par3 (P1 P2 : B) : B := P_hor3 P1 P2 + P_hor3 P1 P2 - 1

/-- Expanding weight-`+1` Weyl step-1 wave `N_{+1} = P₁ X P₀ + P₀ X P₂`. -/
def N_pos1_3 (P1 P2 X : B) : B :=
  P1 * X * P0_waist P1 P2 + P0_waist P1 P2 * X * P2

/-- Contracting weight-`-1` Weyl step-1 wave `N_{-1} = P₀ Y P₁ + P₂ Y P₀`. -/
def N_neg1_3 (P1 P2 Y : B) : B :=
  P0_waist P1 P2 * Y * P1 + P2 * Y * P0_waist P1 P2

/-- Outgoing square-zero Para-Kähler horizon-to-waist wave `Ψ_out = P₁ X P₀ + P₂ Y P₀`. -/
def Psi_out3 (P1 P2 X Y : B) : B :=
  P1 * X * P0_waist P1 P2 + P2 * Y * P0_waist P1 P2

/-- Ingoing square-zero Para-Kähler waist-to-horizon wave `Ψ_in = P₀ Y P₁ + P₀ X P₂`. -/
def Psi_in3 (P1 P2 X Y : B) : B :=
  P0_waist P1 P2 * Y * P1 + P0_waist P1 P2 * X * P2

/-- Full 4-block odd vielbein solder form `Φ_odd = Ψ_out + Ψ_in`. -/
def Phi_odd3 (P1 P2 X Y : B) : B :=
  Psi_out3 P1 P2 X Y + Psi_in3 P1 P2 X Y

/-- Weyl scaling current `J_Weyl = N_{+1} - N_{-1}`. -/
def J_Weyl3 (P1 P2 X Y : B) : B :=
  N_pos1_3 P1 P2 X - N_neg1_3 P1 P2 Y

/-- Para-Kähler horizon–waist current `J_PK = Ψ_out - Ψ_in`. -/
def J_PK3 (P1 P2 X Y : B) : B :=
  Psi_out3 P1 P2 X Y - Psi_in3 P1 P2 X Y

/-- Weyl-invariant step-1 metric `V₁ = {N_{+1}, N_{-1}}`. -/
def V1_weyl3 (P1 P2 X Y : B) : B :=
  anticomm (N_pos1_3 P1 P2 X) (N_neg1_3 P1 P2 Y)

/-- Full 5-entry Para-Kähler metric `V_PK = {Ψ_out, Ψ_in}`. -/
def V_PK3 (P1 P2 X Y : B) : B :=
  anticomm (Psi_out3 P1 P2 X Y) (Psi_in3 P1 P2 X Y)

/-- Full 5-entry Para-Kähler spin bivector `Σ_PK = [Ψ_out, Ψ_in]`. -/
def Sigma_PK3 (P1 P2 X Y : B) : B :=
  comm (Psi_out3 P1 P2 X Y) (Psi_in3 P1 P2 X Y)

/-- Para-Kähler chiral conjugation `α_par(Z) = S_par3 * Z * S_par3`. -/
def parConj3 (P1 P2 Z : B) : B :=
  S_par3 P1 P2 * Z * S_par3 P1 P2

/-- Outgoing exterior derivative `d_out3(Z) = Ψ_out * Z - α_par(Z) * Ψ_out`. -/
def d_out3 (P1 P2 X Y Z : B) : B :=
  Psi_out3 P1 P2 X Y * Z - parConj3 P1 P2 Z * Psi_out3 P1 P2 X Y

/-- Ingoing exterior coderivative `d_in3(Z) = Ψ_in * Z - α_par(Z) * Ψ_in`. -/
def d_in3 (P1 P2 X Y Z : B) : B :=
  Psi_in3 P1 P2 X Y * Z - parConj3 P1 P2 Z * Psi_in3 P1 P2 X Y

def d_sum3  (P1 P2 X Y Z : B) : B := d_out3 P1 P2 X Y Z + d_in3 P1 P2 X Y Z
def d_diff3 (P1 P2 X Y Z : B) : B := d_out3 P1 P2 X Y Z - d_in3 P1 P2 X Y Z

/-- Unrenormalized 3-horizon frame `Ψ₁_hor = P_hor3 + Φ_odd - Σ_PK`. -/
def Psi1_hor3 (P1 P2 X Y : B) : B :=
  P_hor3 P1 P2 + Phi_odd3 P1 P2 X Y - Sigma_PK3 P1 P2 X Y

/-- Bruhat-renormalized 3-horizon projectors `P̂_hor,+` and `P̂_hor,-`. -/
def P_hat_hor_plus3 (P1 P2 X Y : B) : B :=
  Psi1_hor3 P1 P2 X Y - V_PK3 P1 P2 X Y * Psi_out3 P1 P2 X Y

def P_hat_hor_minus3 (P1 P2 X Y : B) : B :=
  Psi1_hor3 P1 P2 X Y - V_PK3 P1 P2 X Y * Psi_in3 P1 P2 X Y

theorem P_hor3_idem {P1 P2 : B}
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    P_hor3 P1 P2 * P_hor3 P1 P2 = P_hor3 P1 P2 := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  dsimp only [P_hor3]
  parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

theorem Psi_out3_eq_N_plus {P1 P2 : B}
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) (X Y : B) :
    Psi_out3 P1 P2 X Y = N_plus (P_hor3 P1 P2) (P1 * X + P2 * Y) := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  dsimp only [Psi_out3, P0_waist, N_plus, P_hor3]
  parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

theorem Psi_in3_eq_N_minus {P1 P2 : B}
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) (X Y : B) :
    Psi_in3 P1 P2 X Y = N_minus (P_hor3 P1 P2) (Y * P1 + X * P2) := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  dsimp only [Psi_in3, P0_waist, N_minus, P_hor3]
  parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- **Sixth-Order Weld 1 (`dual_weyl_and_parakahler_partition_of_odd_vielbein`)**:
Dual Weyl (`N_{+1} + N_{-1} = Φ_odd`) and Para-Kähler (`Ψ_out + Ψ_in = Φ_odd`) partitions
of the 4-block odd vielbein, dual current extractions `[H, Φ_odd] = J_Weyl` vs.
`S_par * Φ_odd = J_PK`, and cube-zero Weyl waves (`N_{±1}³ = 0`) vs. square-zero
Para-Kähler waves (`Ψ_out² = Ψ_in² = 0`). -/
theorem dual_weyl_and_parakahler_partition_of_odd_vielbein
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let H    := H_weyl P1 P2
    let Spar := S_par3 P1 P2
    let np1  := N_pos1_3 P1 P2 X
    let nm1  := N_neg1_3 P1 P2 Y
    let pout := Psi_out3 P1 P2 X Y
    let pin  := Psi_in3 P1 P2 X Y
    let ph   := Phi_odd3 P1 P2 X Y
    let jW   := J_Weyl3 P1 P2 X Y
    let jPK  := J_PK3 P1 P2 X Y
    H * H = P_hor3 P1 P2 ∧
    H * (H * H) = H ∧
    Spar * Spar = 1 ∧
    comm H Spar = 0 ∧
    np1 + nm1 = ph ∧
    pout + pin = ph ∧
    comm H ph = jW ∧
    Spar * ph = jPK ∧
    comm H pout + comm H pin = jW ∧
    Spar * np1 + Spar * nm1 = jPK ∧
    np1 * (np1 * np1) = 0 ∧
    nm1 * (nm1 * nm1) = 0 ∧
    pout * pout = 0 ∧
    pin * pin = 0 := by
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [H_weyl, P_hor3, S_par3, P0_waist, N_pos1_3, N_neg1_3,
                Psi_out3, Psi_in3, Phi_odd3, J_Weyl3, J_PK3, comm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'

/-- **Sixth-Order Weld 2 (`fundamental_weyl_to_parakahler_metric_bridge`)**:
The Para-Kähler metric `V_PK = {Ψ_out, Ψ_in}` decomposes into the Weyl-invariant step-1
metric `V₁ = {N_{+1}, N_{-1}}` plus the step-2 contact shells `N_{+1}² + N_{-1}²`, separated
by the Weyl Laplacian `ad_H²(V_PK) = 4(N_{+2} + N_{-2})`. -/
theorem fundamental_weyl_to_parakahler_metric_bridge
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let H    := H_weyl P1 P2
    let Spar := S_par3 P1 P2
    let np1  := N_pos1_3 P1 P2 X
    let nm1  := N_neg1_3 P1 P2 Y
    let np2  := np1 * np1
    let nm2  := nm1 * nm1
    let ph   := Phi_odd3 P1 P2 X Y
    let jPK  := J_PK3 P1 P2 X Y
    let v1   := V1_weyl3 P1 P2 X Y
    let vPK  := V_PK3 P1 P2 X Y
    let sPK  := Sigma_PK3 P1 P2 X Y
    vPK = v1 + np2 + nm2 ∧
    ph * ph = vPK ∧
    jPK * jPK = - vPK ∧
    comm H v1 = 0 ∧
    comm H (comm H vPK) = 4 • (np2 + nm2) ∧
    4 • vPK - comm H (comm H vPK) = 4 • v1 ∧
    sPK = Spar * vPK ∧
    sPK = vPK * Spar ∧
    sPK * sPK = vPK * vPK := by
  intro H Spar np1 nm1 np2 nm2 ph jPK v1 vPK sPK
  have h1'  : ∀ W, P1 * (P1 * W) = P1 * W := fun W => by rw [← mul_assoc, h1]
  have h2'  : ∀ W, P2 * (P2 * W) = P2 * W := fun W => by rw [← mul_assoc, h2]
  have h12' : ∀ W, P1 * (P2 * W) = 0 := fun W => by rw [← mul_assoc, h12, zero_mul]
  have h21' : ∀ W, P2 * (P1 * W) = 0 := fun W => by rw [← mul_assoc, h21, zero_mul]
  have hP_hor := P_hor3_idem h1 h2 h12 h21
  have h_out := Psi_out3_eq_N_plus h1 h2 h12 h21 X Y
  have h_in  := Psi_in3_eq_N_minus h1 h2 h12 h21 X Y
  have h_vPK_eq : vPK = v1 + np2 + nm2 := by
    dsimp only [vPK, v1, np2, nm2, np1, nm1, V_PK3, V1_weyl3,
                Psi_out3, Psi_in3, N_pos1_3, N_neg1_3, P0_waist, anticomm]
    parabolic_idem_nf h1 h2 h12 h21 h1' h2' h12' h21'
  have h7 := node7_log_radial_modular_time_and_five_graded_weyl_invariance P1 P2 X Y h1 h2 h12 h21
  have h_v1_0 : comm H v1 = 0 := h7.2.2.2.2.2.2.2.2.1
  have h_np2  : comm H np2 = 2 • np2 := h7.2.2.2.2.2.2.1
  have h_nm2  : comm H nm2 = - (2 • nm2) := h7.2.2.2.2.2.2.2.1
  have h_comm1 : comm H vPK = 2 • np2 - 2 • nm2 := by
    rw [h_vPK_eq, comm_add_right, comm_add_right, h_v1_0, h_np2, h_nm2]
    abel
  have h_comm2 : comm H (comm H vPK) = 4 • (np2 + nm2) := by
    rw [h_comm1, comm_sub_right]
    have hp : comm H (2 • np2) = 2 • comm H np2 := by
      simp only [two_nsmul, comm_add_right]
    have hm : comm H (2 • nm2) = 2 • comm H nm2 := by
      simp only [two_nsmul, comm_add_right]
    rw [hp, hm, h_np2, h_nm2]
    abel
  refine ⟨h_vPK_eq, ?_, ?_, h_v1_0, h_comm2, ?_, ?_, ?_, ?_⟩
  · dsimp only [ph, vPK, Phi_odd3, V_PK3, anticomm]
    rw [h_out, h_in]; amari_peirce_nf hP_hor
  · dsimp only [jPK, vPK, J_PK3, V_PK3, anticomm]
    rw [h_out, h_in]; amari_peirce_nf hP_hor
  · rw [h_comm2, h_vPK_eq]; abel
  · dsimp only [sPK, Spar, vPK, Sigma_PK3, V_PK3, S_par3, comm, anticomm]
    rw [h_out, h_in]; change _ = S_P (P_hor3 P1 P2) * _; amari_peirce_nf hP_hor
  · dsimp only [sPK, Spar, vPK, Sigma_PK3, V_PK3, S_par3, comm, anticomm]
    rw [h_out, h_in]; change _ = _ * S_P (P_hor3 P1 P2); amari_peirce_nf hP_hor
  · dsimp only [sPK, vPK, Sigma_PK3, V_PK3, comm, anticomm]
    rw [h_out, h_in]; amari_peirce_nf hP_hor

/-- **Sixth-Order Weld 3 (`three_horizon_rotating_ball_and_cl11_weitzenbock_calculus`)**:
On the 3-horizon 5-graded system `(P₁, P₀, P₂)`, the 4-block odd vielbein `Φ_odd` and
Para-Kähler current `J_PK` obey central harmonicity, the 1st/2nd-order rotating-ball
equilibria, bichiral nilpotency `d_out² = d_in² = 0`, Hodge Laplacian `{d_out, d_in}(Z) = [V_PK, Z]`,
`Cl(1,1)` anticommutation `{d_sum, d_diff} = 0`, and Weitzenböck curvature `d_diff(d_sum(Σ_PK)) = 4 V_PK²`. -/
theorem three_horizon_rotating_ball_and_cl11_weitzenbock_calculus
    (P1 P2 X Y Z : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let ph  := Phi_odd3 P1 P2 X Y
    let jPK := J_PK3 P1 P2 X Y
    let vPK := V_PK3 P1 P2 X Y
    let sPK := Sigma_PK3 P1 P2 X Y
    comm vPK ph = 0 ∧ comm vPK jPK = 0 ∧ comm vPK sPK = 0 ∧
    - comm ph (comm ph jPK) + 2 • comm sPK ph = 0 ∧
    comm sPK (comm sPK ph) + vPK * comm jPK (comm jPK ph) = 0 ∧
    d_out3 P1 P2 X Y (d_out3 P1 P2 X Y Z) = 0 ∧
    d_in3 P1 P2 X Y (d_in3 P1 P2 X Y Z) = 0 ∧
    d_out3 P1 P2 X Y ph = vPK ∧
    d_in3 P1 P2 X Y ph = vPK ∧
    d_out3 P1 P2 X Y (d_in3 P1 P2 X Y Z) + d_in3 P1 P2 X Y (d_out3 P1 P2 X Y Z) = comm vPK Z ∧
    d_sum3 P1 P2 X Y (d_diff3 P1 P2 X Y Z) + d_diff3 P1 P2 X Y (d_sum3 P1 P2 X Y Z) = 0 ∧
    d_diff3 P1 P2 X Y (d_sum3 P1 P2 X Y sPK) = 4 • (vPK * vPK) := by
  have hP_hor := P_hor3_idem h1 h2 h12 h21
  have h_out := Psi_out3_eq_N_plus h1 h2 h12 h21 X Y
  have h_in  := Psi_in3_eq_N_minus h1 h2 h12 h21 X Y
  have h_Spar : S_par3 P1 P2 = S_P (P_hor3 P1 P2) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [d_sum3, d_diff3, d_out3, d_in3, parConj3,
                Phi_odd3, J_PK3, V_PK3, Sigma_PK3, comm, anticomm]
    try rw [h_out]
    try rw [h_in]
    try rw [h_Spar]
    amari_peirce_nf hP_hor

/-- **Sixth-Order Weld 4 (`three_horizon_exterior_bruhat_projector_renormalization`)**:
On the 3-horizon system `(P₁, P₀, P₂)`, the unrenormalized frame `Ψ₁_hor = P_hor + Φ_odd - Σ_PK`
has quartic defect `Ψ₁_hor² - Ψ₁_hor = V_PK²`, cured by `2 P̂_hor,+ = 2 Ψ₁_hor + d_out(Σ_PK)`
and `2 P̂_hor,- = 2 Ψ₁_hor - d_in(Σ_PK)` (`P̂_hor,±² = P̂_hor,±`, `P̂_hor,- - P̂_hor,+ = V_PK J_PK`). -/
theorem three_horizon_exterior_bruhat_projector_renormalization
    (P1 P2 X Y : B)
    (h1 : P1 * P1 = P1) (h2 : P2 * P2 = P2)
    (h12 : P1 * P2 = 0) (h21 : P2 * P1 = 0) :
    let psi1 := Psi1_hor3 P1 P2 X Y
    let Php  := P_hat_hor_plus3 P1 P2 X Y
    let Phm  := P_hat_hor_minus3 P1 P2 X Y
    let vPK  := V_PK3 P1 P2 X Y
    let sPK  := Sigma_PK3 P1 P2 X Y
    let jPK  := J_PK3 P1 P2 X Y
    psi1 * psi1 - psi1 = vPK * vPK ∧
    2 • Php = 2 • psi1 + d_out3 P1 P2 X Y sPK ∧
    2 • Phm = 2 • psi1 - d_in3 P1 P2 X Y sPK ∧
    Php * Php = Php ∧
    Phm * Phm = Phm ∧
    Phm - Php = vPK * jPK ∧
    2 • (Phm - Php) = - d_sum3 P1 P2 X Y sPK := by
  have hP_hor := P_hor3_idem h1 h2 h12 h21
  have h_out := Psi_out3_eq_N_plus h1 h2 h12 h21 X Y
  have h_in  := Psi_in3_eq_N_minus h1 h2 h12 h21 X Y
  have h_Spar : S_par3 P1 P2 = S_P (P_hor3 P1 P2) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · dsimp only [P_hat_hor_plus3, P_hat_hor_minus3, Psi1_hor3, d_sum3, d_out3, d_in3, parConj3,
                Phi_odd3, J_PK3, V_PK3, Sigma_PK3, comm, anticomm]
    try rw [h_out]
    try rw [h_in]
    try rw [h_Spar]
    amari_peirce_nf hP_hor

end InfoGeometry.OperatorAlgebra.PeirceSpine.ParabolicMaurerCartanAndBruhatTransportPoset
