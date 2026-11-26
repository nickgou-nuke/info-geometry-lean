/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
import InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis
import InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis
import InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis
import InfoGeometry.Core.JordanAssociatorRing
import InfoGeometry.Core.PeirceDoubleCommutator
import InfoGeometry.Core.CornerCentrality
import InfoGeometry.Erlangen.InvariantGeometry
import InfoGeometry.NCG.NoncommutativeCyclicCocycle
import InfoGeometry.NCG.CuntzColimitKMSTiltGNS
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Erlangen 2.0 over Noncommutative Operator Rings (Preexisting-Owner Integration)

Formalizes Erlangen 2.0 purely over arbitrary noncommutative rings `[Ring A]` and `*-rings`
`[Ring A] [StarRing A]`, without real scalars or division by `2`, directly reusing the
repository's preexisting noncommutative operator-ring owners:

1. **Division-Free Jordan–Lie–Casimir Erlangen Laws (`NoncommutativeCyclicCocycle`,
   `JordanAssociatorRing`, `InvariantGeometry`, `NoncommutativeMetriplecticAndColimitAlgebraSynthesis`):**
   Uses `NCG.jordanProduct X Y = X * Y + Y * X`, the associative Lie commutator `⁅X, Y⁆`,
   `JC.symm_associator_eq_double_commutator`, `IG.IsRingCasimir A Z`, and `NCMet.metriplecticFlow`
   over any `[Ring A]`.
2. **Operator-Valued `*-Cone` Variance & Metriplectic Laws (`NoncommutativeGrandApexSynthesis`,
   `NoncommutativeMetriplecticAndColimitAlgebraSynthesis`, `CuntzColimitKMSTiltGNS`):**
   Proves zero Gabor–Parseval `NCApex.gibbsCovariance` on constants in any `[Ring A] [StarRing A]`,
   tracial First/Second Law identities for `NCMet.metriplecticFlow` over arbitrary `[Ring R] [Ring A]`,
   and the `NCG.noncommutativeSLDFisher` / `NCG.PositiveState.gnsInner` bridge.
3. **All-Scales Casimir Center & `M₂(A)` / `ClTower A n` Chiral Atom (`NoncommutativeCliffordPrimitives`,
   `PeirceDoubleCommutator`, `NoncommutativeDiracMassAndEntropicTowerSynthesis`):**
   Classifies `IG.IsRingCasimir (ClTower A n) M ↔ ∃ c, IG.IsRingCasimir A c ∧ M = towerScalar n c`
   at every tower level `n`, proves unit/trace/double-bracket/mass-mixing/nilpotent laws on
   `gamma1Op`, `sigmaOp`, `omegaOp`, `F_plus`, `sheetMassOp` over any `[Ring A] [StarRing A] [Nontrivial A]`,
   and embeds all-scales metriplectic colimit stability.
4. **Reducible Product Center vs. Corner Separation (`Core.CornerCentrality`):**
   Constructs `(1, 0)` and `(0, 1)` inside `A × A` over any `[Ring A] [Nontrivial A]` to exhibit
   non-diagonal central Casimirs and apply `CC.orthogonal_corner_ssubset_centralizer`.
-/

noncomputable section

namespace InfoGeometry.Erlangen.ErlangenTwoZeroOperatorRing

open Matrix
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Part 1: Division-Free Jordan–Lie–Casimir Erlangen Laws (`[Ring A]`) -/

section DivisionFreeJordanLie

variable {A : Type*} [Ring A]

/-- Division-free characterization of `InvariantGeometry.IsRingCasimir`:
`IsRingCasimir A Z` holds if and only if every Lie bracket `⁅Z, X⁆` vanishes. -/
theorem isRingCasimir_iff_lie_zero (Z : A) :
    InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir A Z ↔ ∀ X : A, ⁅Z, X⁆ = 0 := by
  constructor
  · intro hZ X
    rw [Ring.lie_def, (hZ X).symm, sub_self]
  · intro hZ X
    exact (sub_eq_zero.mp (by simpa only [Ring.lie_def] using hZ X)).symm

/-- **Erlangen 2.0 Division-Free Jordan–Lie–Casimir Laws** over any associative ring `[Ring A]`.
Reuses `NCG.jordanProduct`, `Core.JordanAssociator.symm_associator_eq_double_commutator`,
`InvariantGeometry.IsRingCasimir`, and `metriplecticFlow` without assuming commutativity or real scalars. -/
theorem erlangen_ring_jordan_lie_laws (X Y Z H L : A) :
    (InfoGeometry.NCG.jordanProduct X Y + ⁅X, Y⁆ = 2 • (X * Y)) ∧
    (InfoGeometry.NCG.jordanProduct X Y - ⁅X, Y⁆ = 2 • (Y * X)) ∧
    (InfoGeometry.NCG.jordanProduct X Y = InfoGeometry.NCG.jordanProduct Y X) ∧
    (⁅X, Y⁆ = -⁅Y, X⁆) ∧
    (⁅X, ⁅Y, Z⁆⁆ + ⁅Y, ⁅Z, X⁆⁆ + ⁅Z, ⁅X, Y⁆⁆ = 0) ∧
    (InfoGeometry.NCG.jordanProduct (InfoGeometry.NCG.jordanProduct X Y) Z -
        InfoGeometry.NCG.jordanProduct X (InfoGeometry.NCG.jordanProduct Y Z) = ⁅Y, ⁅X, Z⁆⁆) ∧
    (InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir A Z →
      InfoGeometry.NCG.jordanProduct Z X = 2 • (Z * X) ∧
      ⁅Z, X⁆ = 0 ∧
      InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H L Z = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [InfoGeometry.NCG.jordanProduct]
    simp only [Ring.lie_def, two_nsmul]
    noncomm_ring
  · dsimp [InfoGeometry.NCG.jordanProduct]
    simp only [Ring.lie_def, two_nsmul]
    noncomm_ring
  · exact InfoGeometry.NCG.jordanProduct_comm X Y
  · simp only [Ring.lie_def]
    abel
  · simp only [Ring.lie_def]
    noncomm_ring
  · simpa only [InfoGeometry.NCG.jordanProduct, Ring.lie_def] using
      InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator X Y Z
  · intro hZ
    have hCom : ∀ W : A, ⁅W, Z⁆ = 0 := by
      intro W
      rw [Ring.lie_def, hZ W, sub_self]
    refine ⟨?_, (isRingCasimir_iff_lie_zero Z).mp hZ X, ?_⟩
    · dsimp [InfoGeometry.NCG.jordanProduct]
      rw [← hZ X, two_nsmul]
    · dsimp [InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow,
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.hamFlow,
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow]
      rw [hCom H, hCom L, Ring.lie_def, mul_zero, zero_mul, sub_self, neg_zero, add_zero]

/-- Re-export of the preexisting inner-commutator Jordan Leibniz derivation law from
`Core.JordanAssociatorRing` over arbitrary `[Ring A]`. -/
theorem erlangen_commutator_jordan_leibniz (L X Y : A) :
    ⁅L, InfoGeometry.NCG.jordanProduct X Y⁆ =
      ⁅L, X⁆ * Y + Y * ⁅L, X⁆ + (X * ⁅L, Y⁆ + ⁅L, Y⁆ * X) := by
  dsimp [InfoGeometry.NCG.jordanProduct]
  simp only [Ring.lie_def]
  exact InfoGeometry.Core.JordanAssociator.commutator_symm_leibniz L X Y

end DivisionFreeJordanLie

/-! ### Part 2: Operator-Valued `*-Cone` Variance, Metriplectic Conservation & GNS Pairing -/

section StarConeAndTracialDynamics

/-- Operator-valued Parseval–Gabor Jaynes variance (`NoncommutativeGrandApexSynthesis`) vanishes
identically on constant observables `fun _ => c` in any `[Ring A] [StarRing A]`. -/
theorem parseval_constant_zero_variance {A : Type*} [Ring A] [StarRing A] {n : ℕ}
    (φ : Fin n → A) (h_pars : ∑ i : Fin n, φ i * star (φ i) = 1) (c : A) :
    let w := fun i => φ i * star (φ i)
    InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis.gibbsExpectationR w (fun _ => c) = c ∧
    InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis.gibbsCovariance
      w (fun _ => c) (fun _ => star c) = 0 := by
  intro w
  have hExp :
      InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis.gibbsExpectationR w (fun _ => c) = c := by
    dsimp [InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis.gibbsExpectationR]
    rw [← Finset.mul_sum, h_pars, mul_one]
  refine ⟨hExp, ?_⟩
  dsimp [InfoGeometry.Algebra.NoncommutativeGrandApexSynthesis.gibbsCovariance]
  rw [hExp]
  simp only [sub_self, zero_mul, Finset.sum_const_zero]

/-- **Universal Noncommutative Tracial Metriplectic Laws**:
Directly lifts `NoncommutativeMetriplecticAndColimitAlgebraSynthesis.universal_metriplectic_conservation_and_entropy_production`
along any `NCG.TracialFunctional R A` over arbitrary operator rings `[Ring R] [Ring A]`:
1. Lie drift preserves `τ(ρ * · + · * ρ) = 0`;
2. Double-bracket dissipation satisfies `τ(-(ρ * D_L(ρ))) = τ(star ⁅L, ρ⁆ * ⁅L, ρ⁆)` in the `*-cone`;
3. Every conserved observable `K` with `⁅K, H⁆ = 0` and `⁅K, L⁆ = 0` satisfies `τ(K * M_{H, L}(ρ)) = 0`;
4. Any Casimir `C` commuting with `H` and `L` is stationary: `M_{H, L}(C) = 0`. -/
theorem tracial_metriplectic_conservation_and_star_cone_entropy
    {R A : Type*} [Ring R] [Ring A] [Module R A] [StarRing A]
    (τ : InfoGeometry.NCG.TracialFunctional R A)
    (H L ρ K C : A)
    (hL : star L = L) (hρ : star ρ = ρ)
    (hKH : ⁅K, H⁆ = 0) (hKL : ⁅K, L⁆ = 0)
    (hHC : ⁅H, C⁆ = 0) (hLC : ⁅L, C⁆ = 0) :
    (τ (ρ * InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.hamFlow H ρ +
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.hamFlow H ρ * ρ) = 0) ∧
    (τ (-(ρ * InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow L ρ)) =
      τ (star ⁅L, ρ⁆ * ⁅L, ρ⁆)) ∧
    (τ (K * InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H L ρ) = 0) ∧
    (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H L C = 0) := by
  rcases InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.universal_metriplectic_conservation_and_entropy_production
      H L ρ C hL hρ hHC hLC with ⟨hHam, hDiss, hCas⟩
  have hTrCommZero : ∀ X Y : A, τ ⁅X, Y⁆ = 0 := by
    intro X Y
    rw [Ring.lie_def, τ.map_sub, τ.cyclic X Y, sub_self]
  have hKBracket : ∀ (G Y : A), ⁅K, G⁆ = 0 → τ (K * ⁅G, Y⁆) = 0 := by
    intro G Y hKG
    have hMul : K * G = G * K := sub_eq_zero.mp (by simpa only [Ring.lie_def] using hKG)
    have hEq : K * ⁅G, Y⁆ = ⁅G, K * Y⁆ := by
      simp only [Ring.lie_def]
      calc K * (G * Y - Y * G)
          = (K * G) * Y - K * Y * G := by noncomm_ring
        _ = (G * K) * Y - K * Y * G := by rw [hMul]
        _ = G * (K * Y) - (K * Y) * G := by noncomm_ring
    rw [hEq, hTrCommZero]
  refine ⟨?_, ?_, ?_, hCas⟩
  · rw [hHam, hTrCommZero H (ρ * ρ)]
  · rw [hDiss, τ.map_add, hTrCommZero L (ρ * ⁅L, ρ⁆), add_zero]
  · dsimp [InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow,
      InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.hamFlow,
      InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow]
    rw [mul_add, mul_neg, τ.map_add, τ.map_neg, hKBracket H ρ hKH,
      hKBracket L ⁅L, ρ⁆ hKL, neg_zero, add_zero]

/-- **SLD-GNS Pairing Bridge**:
Over any operator rings `[Ring R] [Ring A] [Module R A] [StarRing A]`, when a `PositiveState`
agrees with a `TracialFunctional` at `1`, `NCG.noncommutativeSLDFisher τ 1 1 (star X) Y` equals
`2 • ω.gnsInner Y X`. -/
theorem noncommutativeSLDFisher_eq_two_nsmul_gnsInner
    {R A : Type*} [Ring R] [Ring A] [Module R A] [StarRing A]
    (τ : InfoGeometry.NCG.TracialFunctional R A)
    (ω : InfoGeometry.NCG.PositiveState R A)
    (hωτ : ∀ Z : A, ω Z = τ Z)
    (X Y : A) :
    InfoGeometry.NCG.noncommutativeSLDFisher τ (1 : R) 1 (star X) Y =
      2 • ω.gnsInner Y X := by
  dsimp [InfoGeometry.NCG.noncommutativeSLDFisher, InfoGeometry.NCG.jordanProduct,
    InfoGeometry.NCG.PositiveState.gnsInner]
  rw [one_mul, one_mul, τ.map_add, τ.cyclic Y (star X), hωτ (star X * Y), two_nsmul]

end StarConeAndTracialDynamics

/-! ### Part 3: All-Scales Casimir Center & `M₂(A)` / `ClTower A n` Chiral Atom (`[Ring A]`) -/

section TowerCasimirsAndChiralAtom

private lemma clTower_mat2_eq_prim_mat2 {A : Type*} (a b c d : A) :
    InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.mat2 a b c d =
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.mat2 a b c d := by
  apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;> rfl

/-- **Exact `2 × 2` Operator-Matrix Casimir Classification**:
Over any associative ring `[Ring A]` (noncommutative, without dividing by `2`), an element `M`
of `Matrix (Fin 2) (Fin 2) A` belongs to the Erlangen center (`IsRingCasimir`) if and only if
`M = NCPrim.fiberEmbed c` for a central element `c` of `A`. -/
theorem mat2_isRingCasimir_iff {A : Type*} [Ring A] (M : Matrix (Fin 2) (Fin 2) A) :
    InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir (Matrix (Fin 2) (Fin 2) A) M ↔
      ∃ c : A, InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir A c ∧
        M = InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.fiberEmbed c := by
  constructor
  · intro hM
    have hP : InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus * M =
        M * InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus :=
      hM InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus
    have hF : InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus * M =
        M * InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus :=
      hM InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus
    have h01 : M 0 1 = 0 := by
      have h := congrFun (congrFun hP 0) 1
      simpa [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus,
        Matrix.mul_apply, Fin.sum_univ_two] using h
    have h10 : M 1 0 = 0 := by
      have h := congrFun (congrFun hP 1) 0
      simpa [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus,
        Matrix.mul_apply, Fin.sum_univ_two] using h.symm
    have hdiag : M 1 1 = M 0 0 := by
      have h := congrFun (congrFun hF 0) 1
      simpa [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus,
        Matrix.mul_apply, Fin.sum_univ_two] using h
    have hc : InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir A (M 0 0) := by
      intro x
      have h := congrFun (congrFun
        (hM (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.fiberEmbed x)) 0) 0
      simpa [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.fiberEmbed,
        Matrix.mul_apply, Fin.sum_univ_two] using h
    refine ⟨M 0 0, hc, ?_⟩
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2
    · rfl
    · exact h01
    · exact h10
    · exact hdiag
  · rintro ⟨c, hc, rfl⟩ X
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.fiberEmbed,
        Matrix.mul_apply, Fin.sum_univ_two, hc (X 0 0), hc (X 0 1), hc (X 1 0), hc (X 1 1)]

/-- **All-Scales Tower Casimir Theorem**:
At every level `n : ℕ` of the inductive operator tower `ClTower A n`, the central Casimirs
(`IsRingCasimir (ClTower A n) M`) are precisely the tower scalar embeddings `towerScalar n c`
of base-ring Casimirs `c` (`IsRingCasimir A c`). -/
theorem clTower_isRingCasimir_iff {A : Type*} [Ring A] :
    ∀ (n : ℕ)
      (M : InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n),
      InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir
          (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n) M ↔
        ∃ c : A, InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir A c ∧
          M = InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar n c
  | 0, M => ⟨fun hM => ⟨M, hM, rfl⟩, fun ⟨c, hc, hEq⟩ => by subst hEq; exact hc⟩
  | n + 1, M => by
      let : Ring (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n) :=
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.instRingClTower n
      let : Ring (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A (n + 1)) :=
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.instRingClTower (n + 1)
      constructor
      · intro hM
        have hM' : InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir
            (Matrix (Fin 2) (Fin 2)
              (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n)) M := hM
        rcases (mat2_isRingCasimir_iff M).mp hM' with ⟨d, hd, hEq⟩
        rcases (clTower_isRingCasimir_iff n d).mp hd with ⟨c, hc, hdEq⟩
        refine ⟨c, hc, ?_⟩
        rw [hEq, hdEq]
        dsimp [InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar]
        rw [clTower_mat2_eq_prim_mat2]
        rfl
      · rintro ⟨c, hc, rfl⟩
        have hLev : InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir
            (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n)
            (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar n c) :=
          (clTower_isRingCasimir_iff n _).mpr ⟨c, hc, rfl⟩
        change InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir
            (Matrix (Fin 2) (Fin 2)
              (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n)) _
        apply (mat2_isRingCasimir_iff _).mpr
        refine ⟨InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar n c,
          hLev, ?_⟩
        dsimp [InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar]
        rw [clTower_mat2_eq_prim_mat2]
        rfl

/-- Explicit noncommutativity witness on `Matrix (Fin 2) (Fin 2) A` over any nontrivial ring `A`
using `NCPrim.P_plus` and `NCPrim.F_plus`. -/
theorem mat2_exists_noncomm {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus,
    InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus,
    InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus,
    Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- **Complete Operator-Ring Chiral Atom & Tower Specification (`[Ring A] [StarRing A] [Nontrivial A]`)**:
Combines `NCPrim` (`gamma1Op`, `sigmaOp`, `omegaOp`, `F_plus`), `PDC.ring_double_commutator_of_anticommute`,
`NCDirac.sheet_mixing_mass_and_chiral_supertrace_anomaly`, and
`NCMet.all_scales_metriplectic_eigenmode_and_colimit_stability` over arbitrary noncommutative rings:
1. Traceless chiral generators `gamma1Op`, `sigmaOp`, `omegaOp` with unit-cone traces `(2 : A)`;
2. Nilpotent `F_plus`: zero square & trace `0` yet non-Casimir and positive `*-norm` `1`;
3. Double-bracket Lindblad damping `lindbladFlow omegaOp gamma1Op = 4 • gamma1Op`;
4. Inter-sheet mass supertrace commutator anomaly `superTrace2 ((sheetMassOp μ₊ μ₋)^2) = ⁅μ₊, μ₋⁆`;
5. All-scales metriplectic eigenmode & Bott colimit stability on `ClTower A n`. -/
theorem mat2_chiral_atom_operator_ring_spec
    {A : Type*} [Ring A] [StarRing A] [Nontrivial A]
    (μ_plus μ_minus ω₀ m₀ : A) (n : ℕ)
    (X : InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.ClTower A n) :
    (Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A)) = 0 ∧
     Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A)) = 0 ∧
     Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A)) = 0) ∧
    (Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A)) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op) = (2 : A) ∧
     Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A)) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp) = (2 : A) ∧
     Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A)) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp) = (2 : A)) ∧
    (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus = 0 ∧
     Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus) = 0 ∧
     ¬ InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir (Matrix (Fin 2) (Fin 2) A)
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus ∧
     Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A)) *
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus) = 1) ∧
    (⁅InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A),
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op⁆ =
      2 • InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A) ∧
     InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow
        (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A))
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op =
      4 • InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A)) ∧
    (InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis.superTrace2
        (InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis.sheetMassOp μ_plus μ_minus *
         InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis.sheetMassOp μ_plus μ_minus) =
      ⁅μ_plus, μ_minus⁆) ∧
    (let H_n := InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.massGapOp ω₀ n
     let L_n := InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.massGapOp m₀ n
     let H_n1 := InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.massGapOp ω₀ (n + 1)
     let L_n1 := InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.massGapOp m₀ (n + 1)
     let Ψ_coh := InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.coherenceMode n X
     InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow
        H_n L_n (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.cantorProj n) = 0 ∧
     InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H_n L_n Ψ_coh =
        InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.towerScalar n (ω₀ - m₀ * m₀) * Ψ_coh ∧
     InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H_n1 L_n1
        (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.bottEmbed Ψ_coh) =
      InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.bottEmbed
        (InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.metriplecticFlow H_n L_n Ψ_coh)) := by
  have hTr0 :
      Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A)) = 0 ∧
      Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A)) = 0 ∧
      Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A)) = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp,
        Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hStarSq :
      Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A)) *
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op) = (2 : A) ∧
      Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A)) *
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp) = (2 : A) ∧
      Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A)) *
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp) = (2 : A) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp,
        Matrix.trace, Matrix.diag, Fin.sum_univ_two, one_add_one_eq_two]
  have hF2 : InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A) *
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus = 0 := by
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus]
  have hTrF2 : Matrix.trace (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A) *
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus) = 0 := by
    rw [hF2, Matrix.trace_zero]
  have hNotCasF : ¬ InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir (Matrix (Fin 2) (Fin 2) A)
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus := by
    intro hCas
    have hEq := congrFun (congrFun
      (hCas InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus) 0) 1
    simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.P_plus,
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus,
      Matrix.mul_apply, Fin.sum_univ_two] at hEq
  have hStarF : Matrix.trace (star (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus (A := A)) *
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus) = 1 := by
    simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.F_plus,
      Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  have hCommOG :
      ⁅InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A),
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op⁆ =
      2 • InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp (A := A) := by
    rw [Ring.lie_def, two_nsmul]
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.sigmaOp]
  have hAntiOG :
      InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A) *
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op +
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op *
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp = 0 := by
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp,
        InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op]
  have hOmegaSq : InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A) ^ 2 = -1 := by
    rw [pow_two]
    apply InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ext_fin2 <;>
      simp [InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp]
  have hLind :
      InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow
          (InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.omegaOp (A := A))
          InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op =
        4 • InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.gamma1Op (A := A) := by
    dsimp [InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.lindbladFlow]
    rw [InfoGeometry.Core.PeirceDoubleCommutator.ring_double_commutator_of_anticommute _ _ hAntiOG,
      hOmegaSq, neg_one_mul, smul_neg, neg_neg]
  have hMass :=
    (InfoGeometry.Algebra.NoncommutativeDiracMassAndEntropicTowerSynthesis.sheet_mixing_mass_and_chiral_supertrace_anomaly
      μ_plus μ_minus μ_plus).2.2.1
  have hTower :=
    InfoGeometry.Algebra.NoncommutativeMetriplecticAndColimitAlgebraSynthesis.all_scales_metriplectic_eigenmode_and_colimit_stability
      ω₀ m₀ n X
  exact ⟨hTr0, hStarSq, ⟨hF2, hTrF2, hNotCasF, hStarF⟩, ⟨hCommOG, hLind⟩, hMass, hTower⟩

/-! ### Part 4: Reducible Product Counterexample (`A × A`, `Core.CornerCentrality`) -/

/-- **Counterexample to Scalar Center Reduction on Reducible Operator Rings (`A × A`)**:
Over any nontrivial noncommutative ring `[Ring A] [Nontrivial A]`, `(1, 0)` and `(0, 1)` are
orthogonal central idempotents satisfying:
1. `IsRingCasimir (A × A) (1, 0)` yet `(1, 0)` is neither `0` nor diagonal `(c, c)`;
2. `Set.range (fun x => (0, 1) * x * (0, 1)) ⊂ Set.centralizer (Set.range (fun x => (1, 0) * x * (1, 0)))`
   via `Core.CornerCentrality.orthogonal_corner_ssubset_centralizer`. -/
theorem prod_casimir_and_corner_separation {A : Type*} [Ring A] [Nontrivial A] :
    let p : A × A := (1, 0)
    let q : A × A := (0, 1)
    InfoGeometry.Erlangen.InvariantGeometry.IsRingCasimir (A × A) p ∧
    p ≠ 0 ∧
    (¬ ∃ c : A, p = (c, c)) ∧
    Set.range (fun x : A × A => q * x * q) ⊂
      Set.centralizer (Set.range (fun x : A × A => p * x * p)) := by
  intro p q
  have hp : p * p = p := by ext <;> simp [p]
  have hpq : p * q = 0 := by ext <;> simp [p, q]
  have hqp : q * p = 0 := by ext <;> simp [p, q]
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : (1 : A) = 0 := congrArg Prod.fst h
    exact one_ne_zero h1
  refine ⟨?_, hp0, ?_,
    InfoGeometry.Core.CornerCentrality.orthogonal_corner_ssubset_centralizer p q hp hpq hqp hp0⟩
  · intro x
    ext <;> simp [p]
  · rintro ⟨c, hc⟩
    have hc1 : (1 : A) = c := congrArg Prod.fst hc
    have hc0 : (0 : A) = c := congrArg Prod.snd hc
    exact one_ne_zero (hc1.trans hc0.symm)

end TowerCasimirsAndChiralAtom

end InfoGeometry.Erlangen.ErlangenTwoZeroOperatorRing

end noncomputable section
