/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Kaehler.Basic
import InfoGeometry.Algebra.DerivationLieLane
import InfoGeometry.Algebra.ElementaryMatrixOperators
import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Algebra.PeirceTetraktysKreinBridge
import InfoGeometry.Canonical.ConnesNCGFormAlgebra
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
import InfoGeometry.OperatorAlgebra.MaurerCartanTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness
import InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
import InfoGeometry.Physics.ConnesCyclicCohomology

/-!
# Pillar 3 (`R1`) Primary-Source Formalization: Peirce, Maurer–Cartan, CE, Koszul, Kähler, Karoubi, Connes, & Dubois-Violette

Formalizes primary-source archetypes `S3-01`..`S3-10` atop native Mathlib v4.34.1 and existing
repository owners, preserving `R3.4` throughout:
1. `S3-01` B. Peirce (1870/1881): complete orthogonal idempotent decomposition
   `A = ⨁_{i,j} e_i A e_j`, nilpotency of off-diagonal Peirce blocks, and Dorroh unit-adjunction
   for non-unital associative rings.
2. `S3-02` C. S. Peirce (1870/1880/1883): relational dyadic matrix units `(I:J)(K:L) = δ_{JK}(I:L)`
   and transvection correspondence over arbitrary `[Ring A]`.
3. `S3-03` & `S3-04` L. Maurer (1888/1891) & É. Cartan (1899/1904): Maurer–Cartan flatness
   `dθ_L + θ_L ∧ θ_L = 0`, Cartan torsion/curvature, First Bianchi identity, and Peirce-graded
   soldering (`R3.4`).
4. `S3-05` Chevalley–Eilenberg (1948; OA sub: Koszul 1950): faithfulness-free `LieActionLane`
   cochain complex, interior product `ι_x`, Cartan homotopy `L_x = ι_x ∘ d + d ∘ ι_x`, and an
   explicit non-faithful `LieActionLane` witness (`¬ Function.Injective act`).
5. `S3-06` J.-L. Koszul (1960): faithfulness-free `LieRinehartAnchor`, algebraic `KoszulConnection`,
   $A$-trilinear curvature, and $A$-bilinear torsion.
6. `S3-07` E. Kähler (1953; OA sub: Lerman 2023): canonical comparison `OneForms S →+ Ω[S⁄R]`
   collapsing left/right actions in the commutative case vs. noncommutative separation on `Mat₂(ℤ)`.
7. `S3-08` M. Karoubi (1983/1987): commutator-quotient de Rham complex `KaroubiDR0`/`KaroubiDR1`
   and arbitrary-degree `KaroubiForm K n` using graded commutators `(-1)^(p*q)`.
8. `S3-09` A. Connes (1985): quantized involution calculus `F² = 1`, closed graded traces factoring
   through `KaroubiForm`, and `HC¹` cyclic comparison.
9. `S3-10` M. Dubois-Violette (1988–1999): faithfulness-free `CentralLieRinehartLane`, central
   $Z(A)$-multilinear derivation subcomplex `DuboisVioletteForm`, universal comparison
   `Ω¹_univ(A) → Ω¹_Der(A)`, central bimodule connections, and the matrix center edge case.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-! ## Section 1: B. Peirce (1870/1881) Idempotent Decomposition & Unit-Adjunction (`S3-01`) -/

/-- `[S3-01]` B. Peirce (1881) §§41–46: A finite family of idempotents `e : ι → A` in an
associative ring `[Ring A]` is complete orthogonal when `e i * e j = δ_{ij} e i` and `∑ i, e i = 1`.
Preserves noncommutative `[Ring A]` (`R3.4`). -/
def CompleteOrthogonalIdempotents {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (e : ι → A) : Prop :=
  (∀ i j : ι, e i * e j = if i = j then e i else 0) ∧ (∑ i : ι, e i = 1)

/-- `[S3-01]` B. Peirce (1881) §§45–46: The `(i, j)` Peirce block projection `e i * x * e j`
in an associative ring `[Ring A]` (`R3.4`). -/
def peirceBlock {A ι : Type*} [Ring A] (e : ι → A) (i j : ι) (x : A) : A :=
  e i * x * e j

/-- `[S3-01]` B. Peirce (1881) §§45–46: Completeness of the Peirce block decomposition
`x = ∑ i, ∑ j, e_i x e_j` for any complete orthogonal idempotent family `e`. -/
theorem sum_peirceBlock_eq {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) (x : A) :
    (∑ i : ι, ∑ j : ι, peirceBlock e i j x) = x := by
  have hsum : ∑ i : ι, e i = 1 := he.2
  calc
    (∑ i : ι, ∑ j : ι, peirceBlock e i j x)
        = ∑ i : ι, (e i * x) * (∑ j : ι, e j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [peirceBlock, Finset.mul_sum]
    _ = (∑ i : ι, e i) * x := by
          simp only [hsum, mul_one, ← Finset.sum_mul]
    _ = x := by rw [hsum, one_mul]

/-- `[S3-01]` B. Peirce (1881) §46: Peirce multiplication table
`(e_i x e_j)(e_k y e_l) = δ_{jk} e_i (x e_j y) e_l`. -/
theorem peirceBlock_mul_eq {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) (i j k l : ι) (x y : A) :
    peirceBlock e i j x * peirceBlock e k l y =
      if j = k then peirceBlock e i l (x * e j * y) else 0 := by
  dsimp [peirceBlock]
  have hjk := he.1 j k
  have hcalc : (e i * x * e j) * (e k * y * e l) = e i * x * (e j * e k) * y * e l := by
    noncomm_ring
  rw [hcalc, hjk]
  split_ifs with h
  · subst h
    noncomm_ring
  · noncomm_ring

/-- `[S3-01]` B. Peirce (1881) §46: Uniqueness (direct-sum property) of the Peirce block
decomposition `A = ⨁_{i,j} e_i A e_j`. -/
theorem peirceBlock_unique {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (e : ι → A) (he : CompleteOrthogonalIdempotents e) (b : ι → ι → A)
    (hb : ∀ i j : ι, e i * b i j * e j = b i j) (i j : ι) :
    peirceBlock e i j (∑ k : ι, ∑ l : ι, b k l) = b i j := by
  dsimp [peirceBlock]
  rw [Finset.mul_sum, Finset.sum_mul]
  have hrow : ∀ k : ι, e i * (∑ l : ι, b k l) * e j =
      if k = i then b i j else 0 := by
    intro k
    rw [Finset.mul_sum, Finset.sum_mul]
    have hcell : ∀ l : ι, e i * b k l * e j = if k = i ∧ l = j then b i j else 0 := by
      intro l
      have hkl : e i * b k l * e j = (e i * e k) * b k l * (e l * e j) := by
        calc
          e i * b k l * e j = e i * (e k * b k l * e l) * e j := by rw [hb k l]
          _ = (e i * e k) * b k l * (e l * e j) := by noncomm_ring
      rw [hkl, he.1 i k, he.1 l j]
      by_cases hik : i = k <;> by_cases hlj : l = j
      · rw [ite_eq_left hik, ite_eq_left hlj, ite_eq_left ⟨hik.symm, hlj⟩, ← hik, hlj]
        exact hb i j
      · rw [ite_eq_left hik, ite_eq_right hlj, mul_zero, ite_eq_right (fun h => hlj h.2)]
      · rw [ite_eq_right hik, zero_mul, zero_mul, ite_eq_right (fun h => hik h.1.symm)]
      · rw [ite_eq_right hik, zero_mul, zero_mul, ite_eq_right (fun h => hik h.1.symm)]
    simp_rw [hcell]
    by_cases hik : k = i
    · subst hik
      simp
    · simp [hik]
  simp_rw [hrow]
  simp

/-- `[S3-01]` B. Peirce (1881) §§41–46: The binary idempotent pair `![P, 1 - P]` associated to
an idempotent `P² = P`. -/
def binaryPeirceIdempotents {A : Type*} [Ring A] (P : A) : Fin 2 → A :=
  ![P, 1 - P]

/-- `[S3-01]` B. Peirce (1881) §§41–46: Completeness and orthogonality of `![P, 1 - P]`
whenever `P * P = P`. -/
theorem binaryPeirceIdempotents_complete {A : Type*} [Ring A] {P : A} (hP : P * P = P) :
    CompleteOrthogonalIdempotents (binaryPeirceIdempotents P) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · simp [binaryPeirceIdempotents, hP]
    · simp only [binaryPeirceIdempotents, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta,
        Fin.mk_one, zero_ne_one, ↓reduceIte]
      calc P * (1 - P) = P - P * P := by noncomm_ring
        _ = 0 := by rw [hP, sub_self]
    · simp only [binaryPeirceIdempotents, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one,
        Fin.zero_eta, one_ne_zero, ↓reduceIte]
      calc (1 - P) * P = P - P * P := by noncomm_ring
        _ = 0 := by rw [hP, sub_self]
    · simp only [binaryPeirceIdempotents, ↓reduceIte]
      calc (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
        _ = 1 - P := by rw [hP]; noncomm_ring
  · rw [Fin.sum_univ_two]
    simp [binaryPeirceIdempotents]

/-- `[S3-01]` B. Peirce (1881) §§45–46: Alignment of `peirceBlock (binaryPeirceIdempotents P)`
with the repository's `PeirceSpine` blocks `peirce11`, `conePlus`, `coneMinus`, `peirce00`. -/
theorem binaryPeirceBlock_eq_peirceSpine {A : Type*} [Ring A] (P x : A) :
    peirceBlock (binaryPeirceIdempotents P) 0 0 x = PeirceSpine.peirce11 P x ∧
    peirceBlock (binaryPeirceIdempotents P) 0 1 x = PeirceSpine.conePlus P x ∧
    peirceBlock (binaryPeirceIdempotents P) 1 0 x = PeirceSpine.coneMinus P x ∧
    peirceBlock (binaryPeirceIdempotents P) 1 1 x = PeirceSpine.peirce00 P x := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `[S3-01]` B. Peirce (1881) §47: Nilpotency (`dn² = 0`, `nd² = 0`) of the off-diagonal
Peirce corners in an associative ring `[Ring A]`. -/
theorem peirce_offDiagonal_nilpotent_sq_zero {A : Type*} [Ring A] {P : A} (hP : P * P = P)
    (x y : A) :
    PeirceSpine.conePlus P x * PeirceSpine.conePlus P y = 0 ∧
    PeirceSpine.coneMinus P x * PeirceSpine.coneMinus P y = 0 :=
  ⟨PeirceSpine.conePlus_mul_conePlus hP x y, PeirceSpine.coneMinus_mul_coneMinus hP x y⟩

/-- `[S3-01]` B. Peirce (1881) §§10–20: Dorroh unit-adjunction `R × A` equipping any
non-unital associative `R`-algebra `[NonUnitalRing A]` with a multiplicative unit `(1, 0)`. -/
@[ext]
structure DorrohUnitization (R A : Type*) where
  fst : R
  snd : A

/-- Constructive T17 witness inhabiting `DorrohUnitization ℤ ℤ`. -/
def dorrohUnitizationWitness : DorrohUnitization ℤ ℤ :=
  ⟨1, 0⟩

instance instAddCommGroupDorrohUnitization (R A : Type*) [AddCommGroup R] [AddCommGroup A] :
    AddCommGroup (DorrohUnitization R A) where
  add x y := ⟨x.fst + y.fst, x.snd + y.snd⟩
  add_assoc x y z := congrArg₂ DorrohUnitization.mk (add_assoc x.fst y.fst z.fst)
    (add_assoc x.snd y.snd z.snd)
  zero := ⟨0, 0⟩
  zero_add x := congrArg₂ DorrohUnitization.mk (zero_add x.fst) (zero_add x.snd)
  add_zero x := congrArg₂ DorrohUnitization.mk (add_zero x.fst) (add_zero x.snd)
  nsmul n x := ⟨n • x.fst, n • x.snd⟩
  nsmul_zero x := congrArg₂ DorrohUnitization.mk (zero_nsmul x.fst) (zero_nsmul x.snd)
  nsmul_succ n x := congrArg₂ DorrohUnitization.mk (succ_nsmul x.fst n) (succ_nsmul x.snd n)
  neg x := ⟨-x.fst, -x.snd⟩
  zsmul n x := ⟨n • x.fst, n • x.snd⟩
  zsmul_zero' x := congrArg₂ DorrohUnitization.mk (zero_zsmul x.fst) (zero_zsmul x.snd)
  zsmul_succ' n x := congrArg₂ DorrohUnitization.mk
    (by change (↑n + 1 : ℤ) • x.fst = (n : ℤ) • x.fst + x.fst; rw [add_zsmul, one_zsmul])
    (by change (↑n + 1 : ℤ) • x.snd = (n : ℤ) • x.snd + x.snd; rw [add_zsmul, one_zsmul])
  zsmul_neg' n x := congrArg₂ DorrohUnitization.mk
    (by change (Int.negSucc n) • x.fst = -((↑n + 1 : ℤ) • x.fst); rw [Int.negSucc_eq, neg_smul])
    (by change (Int.negSucc n) • x.snd = -((↑n + 1 : ℤ) • x.snd); rw [Int.negSucc_eq, neg_smul])
  neg_add_cancel x := congrArg₂ DorrohUnitization.mk (neg_add_cancel x.fst) (neg_add_cancel x.snd)
  add_comm x y := congrArg₂ DorrohUnitization.mk (add_comm x.fst y.fst) (add_comm x.snd y.snd)

instance instRingDorrohUnitization (R A : Type*) [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    Ring (DorrohUnitization R A) where
  mul x y := ⟨x.fst * y.fst, x.fst • y.snd + y.fst • x.snd + x.snd * y.snd⟩
  left_distrib x y z := by
    refine congrArg₂ DorrohUnitization.mk (mul_add x.fst y.fst z.fst) ?_
    change x.fst • (y.snd + z.snd) + (y.fst + z.fst) • x.snd + x.snd * (y.snd + z.snd) =
      (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) +
        (x.fst • z.snd + z.fst • x.snd + x.snd * z.snd)
    rw [smul_add, add_smul, mul_add]
    abel
  right_distrib x y z := by
    refine congrArg₂ DorrohUnitization.mk (add_mul x.fst y.fst z.fst) ?_
    change (x.fst + y.fst) • z.snd + z.fst • (x.snd + y.snd) + (x.snd + y.snd) * z.snd =
      (x.fst • z.snd + z.fst • x.snd + x.snd * z.snd) +
        (y.fst • z.snd + z.fst • y.snd + y.snd * z.snd)
    rw [add_smul, smul_add, add_mul]
    abel
  zero_mul x := congrArg₂ DorrohUnitization.mk (zero_mul x.fst)
    (by change (0 : R) • x.snd + x.fst • (0 : A) + 0 * x.snd = 0; simp)
  mul_zero x := congrArg₂ DorrohUnitization.mk (mul_zero x.fst)
    (by change x.fst • (0 : A) + (0 : R) • x.snd + x.snd * 0 = 0; simp)
  mul_assoc x y z := by
    refine congrArg₂ DorrohUnitization.mk (mul_assoc x.fst y.fst z.fst) ?_
    change (x.fst * y.fst) • z.snd + z.fst • (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) +
        (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) * z.snd =
      x.fst • (y.fst • z.snd + z.fst • y.snd + y.snd * z.snd) + (y.fst * z.fst) • x.snd +
        x.snd * (y.fst • z.snd + z.fst • y.snd + y.snd * z.snd)
    simp only [smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_smul,
      smul_comm z.fst x.fst, smul_comm y.fst z.fst, mul_assoc]
    abel
  one := ⟨1, 0⟩
  one_mul x := congrArg₂ DorrohUnitization.mk (one_mul x.fst)
    (by change (1 : R) • x.snd + x.fst • (0 : A) + 0 * x.snd = x.snd; simp)
  mul_one x := congrArg₂ DorrohUnitization.mk (mul_one x.fst)
    (by change x.fst • (0 : A) + (1 : R) • x.snd + x.snd * 0 = x.snd; simp)

/-- `[S3-01]` B. Peirce (1881) §§10–20: Canonical non-unital ring embedding
`a ↦ (0, a)` of `A` into its Dorroh unitization `DorrohUnitization R A`. -/
def dorrohEmbed (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    A →ₙ+* DorrohUnitization R A where
  toFun a := ⟨0, a⟩
  map_zero' := rfl
  map_add' a b := congrArg₂ DorrohUnitization.mk (add_zero 0).symm rfl
  map_mul' a b := congrArg₂ DorrohUnitization.mk (mul_zero 0).symm
    (by
      change a * b = (0 : R) • b + (0 : R) • a + a * b
      simp)

/-- `[S3-01]` B. Peirce (1881) §§10–20: Injectivity of `dorrohEmbed`. -/
theorem dorrohEmbed_injective (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    Function.Injective (dorrohEmbed R (A := A)) := by
  intro a b h
  exact congrArg DorrohUnitization.snd h

/-- `[S3-01]` B. Peirce (1881) §47: Nilpotency preservation under `dorrohEmbed`. -/
theorem dorrohEmbed_sq_zero (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {a : A} (ha : a * a = 0) :
    dorrohEmbed R a * dorrohEmbed R a = 0 := by
  rw [← map_mul, ha, map_zero]

/-- `[S3-01]` Compatibility of `peirceBlock` with the repository's `KreinPeirceTowerIntertwine`
and `PeirceTetraktysKreinBridge` colimit descent. -/
theorem peirce_krein_tower_compatibility
    {B : Type*} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    {γ₀ : B} (hγ₀_star : star γ₀ = γ₀)
    (n : ℕ)
    (P X A C : InfoGeometry.Algebra.NoncommutativeCliffordPrimitives.ClTower B n)
    (hP_sq : P * P = P) (hP_star : star P = P)
    (hP_pos : InfoGeometry.Algebra.TwoSheetDiracMassEntropy.kroneckerGamma γ₀ n * P = P)
    (stP stA stC stX : InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n) :
    peirceBlock (binaryPeirceIdempotents P) 0 0 X = PeirceSpine.peirce11 P X ∧
      (0 : B) ≤ InfoGeometry.Algebra.TwoSheetDiracMassEntropy.towerTrace
        (InfoGeometry.Algebra.NoncommutativeYangMillsKreinCantorSynthesis.kreinAdjoint γ₀ n
          (PeirceSpine.peirce11 P X) * PeirceSpine.peirce11 P X) ∧
      PeirceDefectBridge.peirceCovariantDeriv P A C (PeirceSpine.genV P A C) = 0 ∧
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n (PeirceSpine.peirce11 stP stX) =
        PeirceSpine.peirce11
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n stP)
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage n stX) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (KreinPeirceTowerIntertwine.peirce11_positive_sector_krein_positivity_and_bianchi
      hγ₀_star n P X A C hP_sq hP_star hP_pos).2.1
  · exact (KreinPeirceTowerIntertwine.peirce11_positive_sector_krein_positivity_and_bianchi
      hγ₀_star n P X A C hP_sq hP_star hP_pos).2.2.2
  · exact (PeirceTetraktysKreinBridge.ofStage_preserves_peirce_yang_mills n
      stP stA stC stX).1

/-! ## Section 2: C. S. Peirce (1870/1880/1883) Dyadic Relational Matrix Units (`S3-02`) -/

/-- `[S3-02]` C. S. Peirce (1883) Note B pp. 187–190: Dyadic matrix unit `(I : J)` represented
as `Matrix.single i j (1 : A)` over an arbitrary noncommutative ring `[Ring A]` (`R3.4`). -/
def dyadicUnit {ι A : Type*} [DecidableEq ι] [Zero A] [One A] (i j : ι) : Matrix ι ι A :=
  Matrix.single i j (1 : A)

/-- `[S3-02]` C. S. Peirce (1883) Note B pp. 187–190: Relational relative product law
`(I : J)(K : L) = δ_{JK} (I : L)` over an arbitrary noncommutative ring `[Ring A]`. -/
theorem dyadicUnit_mul {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] (i j k l : ι) :
    (dyadicUnit i j : Matrix ι ι A) * dyadicUnit k l =
      if j = k then dyadicUnit i l else 0 := by
  dsimp [dyadicUnit]
  split_ifs with h
  · subst h
    simp [Matrix.single_mul_single_same]
  · exact Matrix.single_mul_single_of_ne (1 : A) i j k h (1 : A)

/-- `[S3-02]` C. S. Peirce (1883) Note B: The diagonal dyadic units `i ↦ (i : i)` form a
complete orthogonal idempotent family in `Matrix ι ι A`. -/
theorem dyadicUnit_diag_complete {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] :
    CompleteOrthogonalIdempotents (fun i : ι => (dyadicUnit i i : Matrix ι ι A)) := by
  refine ⟨fun i j => by by_cases hij : i = j <;> simp [dyadicUnit_mul, hij], ?_⟩
  simpa [dyadicUnit] using (Matrix.sum_single_one (m := ι) (α := A))

/-- `[S3-02]` Unification of B. Peirce (`peirceBlock`) and C. S. Peirce (`dyadicUnit`):
compressing `M` by `(i : i)` on the left and `(j : j)` on the right isolates `Matrix.single i j (M i j)`. -/
theorem peirceBlock_dyadicUnit_eq {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
    (M : Matrix ι ι A) (i j : ι) :
    peirceBlock (fun k : ι => (dyadicUnit k k : Matrix ι ι A)) i j M = Matrix.single i j (M i j) := by
  ext a b
  dsimp [peirceBlock]
  rw [Matrix.mul_apply]
  have hL : ∀ k : ι, ((dyadicUnit i i : Matrix ι ι A) * M) a k = if a = i then M i k else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · dsimp [dyadicUnit]
      by_cases ha : i = a
      · subst ha; simp
      · simp [ha, Ne.symm ha]
    · intro x _ hx
      dsimp [dyadicUnit]
      simp [Ne.symm hx]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp_rw [hL]
  rw [Finset.sum_eq_single j]
  · dsimp [dyadicUnit]
    by_cases ha : i = a <;> by_cases hb : j = b
    · subst ha; subst hb; simp
    · subst ha; simp [hb]
    · subst hb; simp [ha, Ne.symm ha]
    · simp [ha, Ne.symm ha]
  · intro k _ hk
    dsimp [dyadicUnit]
    simp [Ne.symm hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- `[S3-02]` C. S. Peirce matrix decomposition: every matrix `M : Matrix ι ι A` is the sum of
its Peirce blocks along diagonal dyadic units. -/
theorem matrix_eq_sum_peirceBlock {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
    (M : Matrix ι ι A) :
    (∑ i : ι, ∑ j : ι, peirceBlock (fun k : ι => (dyadicUnit k k : Matrix ι ι A)) i j M) = M :=
  sum_peirceBlock_eq (fun k : ι => dyadicUnit k k) dyadicUnit_diag_complete M

/-- `[S3-02]` Compatibility with `ElementaryMatrixOperators.elementaryUnit`: scalar elementary
transvections decompose as `1 + a • dyadicUnit i j` over `[Ring A]`. -/
theorem elementaryUnit_eq_one_add_smul_dyadic {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
    (i j : ι) (hij : i ≠ j) (a : A) :
    (ElementaryMatrixOperators.elementaryUnit i j hij a : Matrix ι ι A) =
      1 + Matrix.single i j a :=
  ElementaryMatrixOperators.coe_elementaryUnit i j hij a

/-- `[S3-02]` Closed noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℤ` (`T16`). -/
theorem matrix_int_two_noncommuting_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A :=
  ⟨MatrixNoncommutativity.swapMatrix, MatrixNoncommutativity.tiltedMatrix,
    MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne⟩

/-! ## Section 3: Maurer (1888/1891) & É. Cartan (1899/1904) Soldered Connections & Peirce Grading (`S3-03`, `S3-04`, `R3.4`) -/

/-- `[S3-04]` É. Cartan (1904) Ch. II §§13–20: Torsion 2-form `Θ = dθ + ω ∧ θ` of a coframe
`θ` and connection `ω` on a faithfulness-free `LieActionLane R A` (`R3.4`). -/
def cartanTorsion {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω θ : ActionOperatorForm K 1) : ActionOperatorForm K 2 :=
  actionExteriorDerivative K 1 θ + actionWedge K ω θ

/-- `[S3-04]` É. Cartan (1904) Ch. II §§13–20: Curvature 2-form `Ω = dω + ω ∧ ω` coinciding
with `MaurerCartanTower.actionCurvature K ω` on a faithfulness-free `LieActionLane R A` (`R3.4`). -/
def cartanCurvature {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) : ActionOperatorForm K 2 :=
  MaurerCartanTower.actionCurvature K ω

/-- `[S3-04]` É. Cartan (1904) Ch. II: Left-covariant exterior derivative `D_ω^L η = dη + ω ∧ η`
acting on `ActionOperatorForm K n` over a faithfulness-free `LieActionLane R A`. -/
def cartanLeftCovariantDeriv {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (ω : ActionOperatorForm K 1) (n : ℕ) :
    ActionOperatorForm K n →ₗ[R] ActionOperatorForm K (n + 1) where
  toFun η := actionExteriorDerivative K n η + reindexForm (Nat.add_comm 1 n) (actionWedge K ω η)
  map_add' η₁ η₂ := by
    simp only [map_add, actionWedge_add_right, reindexForm_add]
    abel
  map_smul' c η := by
    simp only [map_smul, actionWedge_smul_right, reindexForm_smul, RingHom.id_apply, smul_add]

/-- `[S3-04]` É. Cartan (1904) Ch. II: Cartan's First Bianchi Identity `D_ω^L Θ = Ω ∧ θ`
on any faithfulness-free `LieActionLane R A` satisfying `IsLeibnizAction K` (`R3.4`). -/
theorem cartan_first_bianchi {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K)
    (ω θ : ActionOperatorForm K 1) :
    cartanLeftCovariantDeriv K ω 2 (cartanTorsion K ω θ) =
      reindexForm (by omega : (1 + 1) + 1 = 2 + 1) (actionWedge K (cartanCurvature K ω) θ) := by
  dsimp [cartanLeftCovariantDeriv, cartanTorsion, cartanCurvature, MaurerCartanTower.actionCurvature]
  rw [map_add, actionExteriorDerivative_succ_comp, zero_add,
    actionExteriorDerivative_actionWedge K hK 1 1 ω θ,
    actionWedge_add_right, actionWedge_add_left, reindexForm_add, reindexForm_add]
  have hp1 : ((-1 : R) ^ (1 : ℕ)) •
      reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
        (actionWedge K ω (actionExteriorDerivative K 1 θ)) =
      -reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
        (actionWedge K ω (actionExteriorDerivative K 1 θ)) := by
    rw [pow_one]
    exact neg_one_smul R (reindexForm (by omega : 1 + (1 + 1) = 2 + 1)
      (actionWedge K ω (actionExteriorDerivative K 1 θ)))
  have hassoc :
      reindexForm (Nat.add_comm 1 2) (actionWedge K ω (actionWedge K ω θ)) =
        reindexForm (by omega : (1 + 1) + 1 = 2 + 1)
          (actionWedge K (actionWedge K ω ω) θ) := by
    rw [← MaurerCartanTower.actionWedge_assoc' K 1 1 1 ω ω θ, reindexForm_trans]
  rw [hp1, hassoc]
  ext v
  simp only [AlternatingMap.add_apply, AlternatingMap.neg_apply, reindexForm_apply]
  have hv1 : v ∘ finCongr (Nat.add_comm 1 2) = v ∘ finCongr (by omega : 1 + (1 + 1) = 2 + 1) :=
    rfl
  rw [hv1]
  abel

/-- `[S3-03]` L. Maurer (1891) §§1–6 (partial gap noted for 1888 Munich Sitzungsber. 18):
The left-logarithmic Maurer–Cartan 1-form `θ_L(g)(x) = g⁻¹ D_x(g)` satisfies the structural
Maurer–Cartan equation `dθ_L(x, y) + [θ_L(x), θ_L(y)] = 0` on any Leibniz `LieActionLane R A`. -/
theorem maurerCartan_thetaL_bracket_eq {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (g : Aˣ) (x y : K.L) :
    actionExteriorDerivative K 1 (MaurerCartanTower.actionThetaL K g) ![x, y] +
      (MaurerCartanTower.actionThetaL K g ![x] * MaurerCartanTower.actionThetaL K g ![y] -
       MaurerCartanTower.actionThetaL K g ![y] * MaurerCartanTower.actionThetaL K g ![x]) = 0 := by
  have hflat := congrArg (fun ω : ActionOperatorForm K 2 => ω ![x, y])
    (MaurerCartanTower.actionThetaL_flat K hK g)
  change (actionExteriorDerivative K 1 (MaurerCartanTower.actionThetaL K g) +
      actionWedge K (MaurerCartanTower.actionThetaL K g)
        (MaurerCartanTower.actionThetaL K g)) ![x, y] = 0 at hflat
  simpa [AlternatingMap.add_apply, actionWedge_one_one_apply] using hflat

/-- `[S3-04]` `R3.4` Peirce-even projection of an `ActionOperatorForm K n` relative to `P : A`. -/
def peirceEvenForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (P : A) {n : ℕ} (ω : ActionOperatorForm K n) :
    ActionOperatorForm K n :=
  { toFun := fun v => PeirceSpine.evenGrade P (ω v)
    map_update_add' := fun v i x y => by
      simp only [ω.map_update_add, PeirceSpine.evenGrade_add]
    map_update_smul' := fun v i c x => by
      simp only [ω.map_update_smul, PeirceSpine.evenGrade, smul_add, mul_smul_comm, smul_mul_assoc]
    map_eq_zero_of_eq' := fun v {i j} hv hij => by
      rw [ω.map_eq_zero_of_eq v hv hij]
      simp [PeirceSpine.evenGrade] }

/-- `[S3-04]` `R3.4` Peirce-odd projection of an `ActionOperatorForm K n` relative to `P : A`. -/
def peirceOddForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (P : A) {n : ℕ} (ω : ActionOperatorForm K n) :
    ActionOperatorForm K n :=
  { toFun := fun v => PeirceSpine.oddGrade P (ω v)
    map_update_add' := fun v i x y => by
      simp only [ω.map_update_add, PeirceSpine.oddGrade_add]
    map_update_smul' := fun v i c x => by
      simp only [ω.map_update_smul, PeirceSpine.oddGrade, smul_add, mul_smul_comm, smul_mul_assoc]
    map_eq_zero_of_eq' := fun v {i j} hv hij => by
      rw [ω.map_eq_zero_of_eq v hv hij]
      simp [PeirceSpine.oddGrade] }

/-- `[S3-04]` `R3.4` Peirce-graded soldering parity law: when the connection 1-form `ω` is
Peirce-odd and the coframe 1-form `θ` is Peirce-even, `ω ∧ θ` is purely Peirce-odd (`evenGrade = 0`)
and `ω ∧ ω` is purely Peirce-even (`oddGrade = 0`). -/
theorem peirce_soldering_torsion_parity_split {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) {P : A} (hP : P * P = P)
    (ω θ : ActionOperatorForm K 1)
    (hω_odd : ∀ v, PeirceSpine.oddGrade P (ω v) = ω v)
    (hθ_even : ∀ v, PeirceSpine.evenGrade P (θ v) = θ v) (x y : K.L) :
    PeirceSpine.evenGrade P (actionWedge K ω θ ![x, y]) = 0 ∧
    PeirceSpine.oddGrade P (actionWedge K ω ω ![x, y]) = 0 := by
  have hω_e : ∀ v, PeirceSpine.evenGrade P (ω v) = 0 := fun v => by
    rw [← hω_odd v]
    exact (PeirceSpine.grade_projection_laws hP (ω v)).2.1
  have hθ_o : ∀ v, PeirceSpine.oddGrade P (θ v) = 0 := fun v => by
    rw [← hθ_even v]
    exact (PeirceSpine.grade_projection_laws hP (θ v)).2.2.1
  constructor
  · rw [actionWedge_one_one_apply]
    have hsub : PeirceSpine.evenGrade P (ω ![x] * θ ![y] - ω ![y] * θ ![x]) =
        PeirceSpine.evenGrade P (ω ![x] * θ ![y]) -
          PeirceSpine.evenGrade P (ω ![y] * θ ![x]) := by
      simp only [PeirceSpine.evenGrade]; noncomm_ring
    rw [hsub, PeirceSpine.evenGrade_mul hP, PeirceSpine.evenGrade_mul hP,
      hω_e ![x], hω_e ![y], hθ_o ![x], hθ_o ![y]]
    simp
  · rw [actionWedge_one_one_apply]
    have hsub : PeirceSpine.oddGrade P (ω ![x] * ω ![y] - ω ![y] * ω ![x]) =
        PeirceSpine.oddGrade P (ω ![x] * ω ![y]) -
          PeirceSpine.oddGrade P (ω ![y] * ω ![x]) := by
      simp only [PeirceSpine.oddGrade]; noncomm_ring
    rw [hsub, PeirceSpine.oddGrade_mul hP, PeirceSpine.oddGrade_mul hP,
      hω_e ![x], hω_e ![y]]
    simp

/-- `[S3-03]` `[S3-04]` `R3.4` Soldering compatibility with `MaurerCartanTower.peirce_three_graded_mc_stage`
and `peirce_five_graded_mc_stage`. -/
theorem peirce_soldering_stage_compatibility {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A : B) :
    let np := PeirceSpine.conePlus P A
    have hnp2 : np * np = 0 := PeirceSpine.conePlus_mul_conePlus hP A A
    let u : Bˣ := ⟨1 + np, 1 - np,
      by calc (1 + np) * (1 - np) = 1 - np * np := by noncomm_ring
        _ = 1 := by rw [hnp2, sub_zero],
      by calc (1 - np) * (1 + np) = 1 - np * np := by noncomm_ring
        _ = 1 := by rw [hnp2, sub_zero]⟩
    (MaurerCartanTower.peirceThreeGradedWitnessStage B).IsFlat
      ((MaurerCartanTower.peirceThreeGradedWitnessStage B).thetaL u) ∧
    (MaurerCartanTower.peirceThreeGradedWitnessStage B).thetaL u ![P] = np := by
  intro np hnp2 u
  have h := MaurerCartanTower.peirce_three_graded_mc_stage hP A
  exact ⟨h.2.2.1, h.2.1⟩

/-! ## Section 4: Chevalley–Eilenberg (1948) / Koszul (1950) Faithfulness-Free Calculus (`S3-05`, `R3.4`) -/

/-- `[S3-05]` Chevalley–Eilenberg (1948); OA sub: Koszul (1950) Ch. II §3 eq. (3.7):
Interior contraction `ι_x : ActionOperatorForm K (n + 1) →ₗ[R] ActionOperatorForm K n`
on any faithfulness-free `LieActionLane R A` (`R3.4`). -/
def interiorProduct {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (n : ℕ) (x : K.L) :
    ActionOperatorForm K (n + 1) →ₗ[R] ActionOperatorForm K n :=
  AlternatingMap.curryLeftLinearMap.flip x

@[simp] theorem interiorProduct_apply {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (n : ℕ) (x : K.L) (ω : ActionOperatorForm K (n + 1)) :
    interiorProduct K n x ω = ω.curryLeft x :=
  rfl

/-- `[S3-05]` Koszul (1950) Ch. II §3 eq. (3.7): Degree-0 Cartan homotopy identity
`ι_x (d ω) = L_x ω` on any faithfulness-free `LieActionLane R A` (`R3.4`). -/
theorem cartan_homotopy_zero {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (x : K.L) (ω : ActionOperatorForm K 0) :
    interiorProduct K 0 x (actionExteriorDerivative K 0 ω) = lieDeriv K x ω :=
  actionExteriorDerivative_zero_curryLeft K ω x

/-- `[S3-05]` Koszul (1950) Ch. II §3 eq. (3.7): Arbitrary-degree Cartan homotopy formula
`L_x ω = ι_x (d ω) + d (ι_x ω)` on any faithfulness-free `LieActionLane R A` (`R3.4`). -/
theorem cartan_homotopy_succ {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (n : ℕ) (x : K.L) (ω : ActionOperatorForm K (n + 1)) :
    lieDeriv K x ω =
      interiorProduct K (n + 1) x (actionExteriorDerivative K (n + 1) ω) +
        actionExteriorDerivative K n (interiorProduct K n x ω) := by
  simp only [interiorProduct_apply, actionExteriorDerivative_succ_curryLeft]
  abel

/-- `[S3-05]` Koszul (1950) Ch. II §3: Square-zero law for interior contraction `ι_x ∘ ι_x = 0`. -/
theorem interiorProduct_comp_self {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (n : ℕ) (x : K.L) (ω : ActionOperatorForm K (n + 2)) :
    interiorProduct K n x (interiorProduct K (n + 1) x ω) = 0 :=
  AlternatingMap.curryLeft_same ω x

/-- `[S3-05]` Koszul (1950) Ch. II §3: Commutator identity `[L_x, ι_y] = ι_{[x, y]}`. -/
theorem lieDeriv_interiorProduct_commutator {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (K : LieActionLane R A) (n : ℕ) (x y : K.L) (ω : ActionOperatorForm K (n + 1)) :
    lieDeriv K x (interiorProduct K n y ω) - interiorProduct K n y (lieDeriv K x ω) =
      interiorProduct K n ⁅x, y⁆ ω := by
  simp only [interiorProduct_apply, lieDeriv_curryLeft]
  abel

/-- `[S3-05]` `R3.4` Explicit non-faithful `LieActionLane` witness over `ℝ`:
`L := ℝ × ℝ` with abelian bracket `0` acts on `ℝ` via `(u, v) ↦ u • id`, so the second
coordinate lies in `ker act` (`¬ Function.Injective act`). -/
def nonFaithfulAbelianLieActionLane : LieActionLane ℝ ℝ :=
  letI : LieRing (ℝ × ℝ) :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra ℝ (ℝ × ℝ) :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  letI : LieRing (Module.End ℝ ℝ) := LieRing.ofAssociativeRing
  { L := ℝ × ℝ
    lieRing := ‹_›
    lieAlgebra := ‹_›
    act :=
      { toFun := fun p => p.1 • LinearMap.id
        map_add' := fun p q => LinearMap.ext fun a => by simp [add_mul]
        map_smul' := fun r p => LinearMap.ext fun a => by simp [mul_assoc]
        map_lie' := fun {p q} => LinearMap.ext fun a => by
          change (0 : ℝ) • LinearMap.id a = _
          simp [Ring.lie_def]
          ring } }

/-- `[S3-05]` `R3.4` Proof that `nonFaithfulAbelianLieActionLane.act` is genuinely non-injective
(faithfulness-free preservation). -/
theorem nonFaithfulAbelianLieActionLane_not_injective :
    ¬ Function.Injective nonFaithfulAbelianLieActionLane.act := by
  intro hinj
  have h01 : nonFaithfulAbelianLieActionLane.act (0, 0) =
      nonFaithfulAbelianLieActionLane.act (0, 1) := by
    apply LinearMap.ext
    intro a
    change ((0 : ℝ) • LinearMap.id) a = ((0 : ℝ) • LinearMap.id) a
    rfl
  have heq := hinj h01
  have h1 : (0 : ℝ) = 1 := congrArg Prod.snd heq
  norm_num at h1

/-- `[S3-05]` `R3.4` Even on the non-faithful `nonFaithfulAbelianLieActionLane`, Chevalley–Eilenberg
`d² = 0` and Cartan homotopy hold unconditionally. -/
theorem nonFaithful_ce_d_sq_zero (n : ℕ)
    (ω : ActionOperatorForm nonFaithfulAbelianLieActionLane n) :
    actionExteriorDerivative nonFaithfulAbelianLieActionLane (n + 1)
      (actionExteriorDerivative nonFaithfulAbelianLieActionLane n ω) = 0 :=
  actionExteriorDerivative_succ_comp nonFaithfulAbelianLieActionLane n ω

/-! ## Section 5: Koszul (1960) Algebraic Connections & $A$-Bilinear Curvature (`S3-06`, `R3.4`) -/

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.2: Faithfulness-free Lie–Rinehart anchor extending
`LieActionLane R A` with an `A`-module structure on `lane.L` satisfying `act(f • X) = f * act(X)`
and the Lie–Rinehart Leibniz rule `⁅X, f • Y⁆ = (X f) • Y + f • ⁅X, Y⁆`.
Crucially omits `Function.Injective lane.act` (`R3.4`). -/
structure LieRinehartAnchor.{u₁, u₂, u₃} (R : Type u₁) (A : Type u₂)
    [CommRing R] [CommRing A] [Algebra R A] where
  lane : LieActionLane.{u₁, u₂, u₃} R A
  moduleA : Module A lane.L
  isScalarTower : IsScalarTower R A lane.L
  isLeibniz : IsLeibnizAction lane
  act_smul_A : ∀ (f : A) (x : lane.L) (a : A),
    lane.operatorAction (f • x) a = f * lane.operatorAction x a
  bracket_smul_right : ∀ (x y : lane.L) (f : A),
    ⁅x, f • y⁆ = (lane.operatorAction x f) • y + f • ⁅x, y⁆

attribute [instance] LieRinehartAnchor.moduleA LieRinehartAnchor.isScalarTower

/-- `[S3-06]` `R3.4` Constructive T17 non-faithful witness for `LieRinehartAnchor ℝ ℝ`:
`L := ℝ` with abelian Lie bracket `0` and trivial anchor `act := 0`. -/
def trivialLieRinehartAnchor : LieRinehartAnchor ℝ ℝ :=
  letI : LieRing ℝ :=
    { bracket := fun _ _ => 0
      add_lie := fun _ _ _ => (add_zero 0).symm
      lie_add := fun _ _ _ => (add_zero 0).symm
      lie_self := fun _ => rfl
      leibniz_lie := fun _ _ _ => (add_zero 0).symm }
  letI : LieAlgebra ℝ ℝ :=
    { lie_smul := fun _ _ _ => (smul_zero _).symm }
  letI : LieRing (Module.End ℝ ℝ) := LieRing.ofAssociativeRing
  { lane :=
      { L := ℝ
        lieRing := ‹_›
        lieAlgebra := ‹_›
        act := 0 }
    moduleA := inferInstance
    isScalarTower := inferInstance
    isLeibniz := fun _ _ _ => by simp [LieActionLane.operatorAction]
    act_smul_A := fun _ _ _ => by simp [LieActionLane.operatorAction]
    bracket_smul_right := fun _ _ _ => by
      change (0 : ℝ) = (0 : ℝ) • _ + _ • (0 : ℝ)
      simp }

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.2: Left `A`-linearity of the Lie–Rinehart bracket
`⁅f • X, Y⁆ = f • ⁅X, Y⁆ - (Y f) • X`. -/
theorem LieRinehartAnchor.bracket_smul_left {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (anchor : LieRinehartAnchor R A) (f : A) (x y : anchor.lane.L) :
    ⁅f • x, y⁆ = f • ⁅x, y⁆ - (anchor.lane.operatorAction y f) • x := by
  rw [← lie_skew (f • x) y, anchor.bracket_smul_right y x f, neg_add, ← lie_skew x y]
  simp only [smul_neg, sub_eq_add_neg, add_comm]

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.2 Def. 2: Algebraic Koszul connection (derivation law)
`∇ : L → M → M` on an `A`-module `M` over a faithfulness-free `LieRinehartAnchor R A` (`R3.4`). -/
structure KoszulConnection {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (anchor : LieRinehartAnchor R A) (M : Type*)
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] where
  nabla : anchor.lane.L → M → M
  nabla_add_left : ∀ X Y s, nabla (X + Y) s = nabla X s + nabla Y s
  nabla_add_right : ∀ X s t, nabla X (s + t) = nabla X s + nabla X t
  nabla_smul_R_right : ∀ (r : R) X s, nabla X (r • s) = r • nabla X s
  nabla_smul_A_left : ∀ (f : A) X s, nabla (f • X) s = f • nabla X s
  leibniz : ∀ (f : A) X s, nabla X (f • s) = (anchor.lane.operatorAction X f) • s + f • nabla X s

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.2: Canonical flat Koszul connection on `M = A` induced by
`anchor.lane.operatorAction`. -/
def koszulConnectionOfAnchor {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (anchor : LieRinehartAnchor R A) : KoszulConnection anchor A where
  nabla X a := anchor.lane.operatorAction X a
  nabla_add_left X Y a := by simp
  nabla_add_right X a b := by simp
  nabla_smul_R_right r X a := by simp
  nabla_smul_A_left f X a := anchor.act_smul_A f X a
  leibniz f X a := by
    change anchor.lane.operatorAction X (f * a) =
      anchor.lane.operatorAction X f * a + f * anchor.lane.operatorAction X a
    exact anchor.isLeibniz X f a

/-- Constructive T17 witness for `KoszulConnection`. -/
def trivialKoszulConnection : KoszulConnection trivialLieRinehartAnchor ℝ :=
  koszulConnectionOfAnchor trivialLieRinehartAnchor

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: Curvature `R(X, Y) s = ∇_X ∇_Y s - ∇_Y ∇_X s - ∇_{[X,Y]} s`
of an algebraic Koszul connection. -/
def koszulCurvature {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : KoszulConnection anchor M) (X Y : anchor.lane.L) (s : M) : M :=
  D.nabla X (D.nabla Y s) - D.nabla Y (D.nabla X s) - D.nabla ⁅X, Y⁆ s

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: Skew-symmetry `R(X, Y) s = -R(Y, X) s`. -/
theorem koszulCurvature_skew {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : KoszulConnection anchor M) (X Y : anchor.lane.L) (s : M) :
    koszulCurvature D X Y s = -koszulCurvature D Y X s := by
  dsimp [koszulCurvature]
  rw [← lie_skew X Y]
  have hneg : D.nabla (-⁅Y, X⁆) s = -D.nabla ⁅Y, X⁆ s := by
    have h0 : D.nabla 0 s = 0 := by
      calc D.nabla 0 s = D.nabla 0 s + D.nabla 0 s - D.nabla 0 s := (add_sub_cancel_right _ _).symm
        _ = D.nabla (0 + 0) s - D.nabla 0 s := by rw [D.nabla_add_left]
        _ = 0 := by rw [zero_add, sub_self]
    have h1 := D.nabla_add_left (-⁅Y, X⁆) ⁅Y, X⁆ s
    rw [neg_add_cancel, h0] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  rw [hneg]
  abel

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: $A$-linearity of `koszulCurvature` in the section `s`. -/
theorem koszulCurvature_smul_section {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : KoszulConnection anchor M) (X Y : anchor.lane.L) (f : A) (s : M) :
    koszulCurvature D X Y (f • s) = f • koszulCurvature D X Y s := by
  dsimp [koszulCurvature]
  rw [D.leibniz f Y s, D.nabla_add_right, D.leibniz, D.leibniz]
  rw [D.leibniz f X s, D.nabla_add_right, D.leibniz, D.leibniz]
  rw [D.leibniz f ⁅X, Y⁆ s]
  rw [anchor.lane.operatorAction_commutator_apply X Y f, sub_smul]
  simp only [smul_sub]
  abel

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: $A$-linearity of `koszulCurvature` in the first vector `X`. -/
theorem koszulCurvature_smul_left {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : KoszulConnection anchor M) (f : A) (X Y : anchor.lane.L) (s : M) :
    koszulCurvature D (f • X) Y s = f • koszulCurvature D X Y s := by
  dsimp [koszulCurvature]
  rw [D.nabla_smul_A_left f X (D.nabla Y s),
    D.nabla_smul_A_left f X s,
    D.leibniz f Y (D.nabla X s),
    anchor.bracket_smul_left f X Y]
  have hsub : D.nabla (f • ⁅X, Y⁆ - anchor.lane.operatorAction Y f • X) s =
      D.nabla (f • ⁅X, Y⁆) s - D.nabla (anchor.lane.operatorAction Y f • X) s := by
    have h := D.nabla_add_left (f • ⁅X, Y⁆ - anchor.lane.operatorAction Y f • X)
      (anchor.lane.operatorAction Y f • X) s
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  rw [hsub, D.nabla_smul_A_left f ⁅X, Y⁆ s, D.nabla_smul_A_left (anchor.lane.operatorAction Y f) X s]
  simp only [smul_sub]
  abel

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: $A$-linearity of `koszulCurvature` in the second vector `Y`. -/
theorem koszulCurvature_smul_right {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (D : KoszulConnection anchor M) (f : A) (X Y : anchor.lane.L) (s : M) :
    koszulCurvature D X (f • Y) s = f • koszulCurvature D X Y s := by
  rw [koszulCurvature_skew D X (f • Y) s, koszulCurvature_smul_left D f Y X s,
    koszulCurvature_skew D Y X s, smul_neg, neg_neg]

/-- `[S3-06]` Koszul (1960) Ch. 1 §1.9: The canonical anchor connection on `M = A` is flat. -/
theorem koszulCurvature_ofAnchor_eq_zero {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (anchor : LieRinehartAnchor R A) (X Y : anchor.lane.L) (a : A) :
    koszulCurvature (koszulConnectionOfAnchor anchor) X Y a = 0 := by
  change anchor.lane.operatorAction X (anchor.lane.operatorAction Y a) -
      anchor.lane.operatorAction Y (anchor.lane.operatorAction X a) -
      anchor.lane.operatorAction ⁅X, Y⁆ a = 0
  rw [anchor.lane.operatorAction_commutator_apply X Y a, sub_self]

/-- `[S3-06]` Koszul (1960) Ch. 1: Torsion tensor `T(X, Y) = ∇_X Y - ∇_Y X - ⁅X, Y⁆` of a
Koszul connection on the tangent Lie–Rinehart module `anchor.lane.L`. -/
def koszulTorsion {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} (D : KoszulConnection anchor anchor.lane.L)
    (X Y : anchor.lane.L) : anchor.lane.L :=
  D.nabla X Y - D.nabla Y X - ⁅X, Y⁆

/-- `[S3-06]` Skew-symmetry and $A$-bilinearity of `koszulTorsion`. -/
theorem koszulTorsion_skew_and_smul_left {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {anchor : LieRinehartAnchor R A} (D : KoszulConnection anchor anchor.lane.L)
    (f : A) (X Y : anchor.lane.L) :
    koszulTorsion D X Y = -koszulTorsion D Y X ∧
      koszulTorsion D (f • X) Y = f • koszulTorsion D X Y := by
  constructor
  · dsimp [koszulTorsion]
    rw [← lie_skew X Y]
    abel
  · dsimp [koszulTorsion]
    rw [D.nabla_smul_A_left f X Y, D.leibniz f Y X, anchor.bracket_smul_left f X Y]
    simp only [smul_sub]
    abel

/-! ## Section 6: Kähler (1953) Differentials & Noncommutative Contrast (`S3-07`) -/

/-- `[S3-07]` Kähler (1953) auxiliary bilinear map `(a, b) ↦ a • d b` into `Ω[S⁄R]`. -/
private def kaehlerPair (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    S →+ S →+ Ω[S⁄R] where
  toFun a :=
    { toFun := fun b => a • KaehlerDifferential.D R S b
      map_zero' := by simp
      map_add' := fun b₁ b₂ => by simp [map_add, smul_add] }
  map_zero' := by
    ext b
    simp
  map_add' a₁ a₂ := by
    ext b
    simp [add_smul]

private theorem kaehlerPair_balanced (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (n : ℤ) (a b : S) :
    kaehlerPair R S (n • a) b = kaehlerPair R S a (n • b) := by
  change (n • a) • KaehlerDifferential.D R S b = a • KaehlerDifferential.D R S (n • b)
  rw [map_zsmul, smul_assoc, smul_comm a n (KaehlerDifferential.D R S b)]

/-- `[S3-07]` Kähler (1953); OA sub: Lerman (2023) §3 Def. 3.1: Canonical additive map
`OneForms S →+ Ω[S⁄R]` from noncommutative universal 1-forms to Mathlib's `KaehlerDifferential R S`
when `S` is commutative (`a ⊗ b ↦ a • D b`). -/
def oneFormsToKaehler (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    PeirceSpine.UniversalNoncommutativeOneForms.OneForms S →+ Ω[S⁄R] where
  toFun ω := PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom S
    (kaehlerPair R S) (kaehlerPair_balanced R S) ω.val
  map_zero' := map_zero _
  map_add' ω₁ ω₂ := map_add _ ω₁.val ω₂.val

@[simp] theorem oneFormsToKaehler_differential (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (a : S) :
    oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.differential S a) =
      KaehlerDifferential.D R S a := by
  change PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom S (kaehlerPair R S) (kaehlerPair_balanced R S)
      (PeirceSpine.UniversalNoncommutativeOneForms.differential S a).val = KaehlerDifferential.D R S a
  rw [PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom_differential]
  change (1 : S) • KaehlerDifferential.D R S a - a • KaehlerDifferential.D R S 1 =
    KaehlerDifferential.D R S a
  simp

@[simp] theorem oneFormsToKaehler_leftDifferentialForm
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (a b : S) :
    oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b) =
      a • KaehlerDifferential.D R S b := by
  change PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom S (kaehlerPair R S) (kaehlerPair_balanced R S)
      (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialTensor S a b) = a • KaehlerDifferential.D R S b
  rw [PeirceSpine.UniversalNoncommutativeOneForms.tensorAddHom_leftDifferentialTensor]
  change a • KaehlerDifferential.D R S b - (a * b) • KaehlerDifferential.D R S 1 =
    a • KaehlerDifferential.D R S b
  simp

/-- `[S3-07]` In the commutative setting `[CommRing S]`, `oneFormsToKaehler` collapses both
`leftAction` and `rightAction` on `OneForms S` to the single commutative scalar action `c • -`. -/
theorem oneFormsToKaehler_leftAction_eq_rightAction
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (c : S)
    (ω : PeirceSpine.UniversalNoncommutativeOneForms.OneForms S) :
    oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftAction S c ω) =
      c • oneFormsToKaehler R S ω ∧
    oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.rightAction S c ω) =
      c • oneFormsToKaehler R S ω := by
  let fL : PeirceSpine.UniversalNoncommutativeOneForms.OneForms S →+ Ω[S⁄R] :=
    (oneFormsToKaehler R S).comp (PeirceSpine.UniversalNoncommutativeOneForms.leftAction S c)
  let gL : PeirceSpine.UniversalNoncommutativeOneForms.OneForms S →+ Ω[S⁄R] :=
    { toFun := fun η => c • oneFormsToKaehler R S η
      map_zero' := by simp
      map_add' := fun η₁ η₂ => by simp [smul_add] }
  have hfL : fL = gL := by
    apply PeirceSpine.UniversalNoncommutativeOneForms.oneForms_addHom_ext S
    intro a b
    change oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftAction S c
        (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b)) =
      c • oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b)
    rw [PeirceSpine.UniversalNoncommutativeOneForms.leftAction_leftDifferentialForm,
      oneFormsToKaehler_leftDifferentialForm, oneFormsToKaehler_leftDifferentialForm, mul_smul]
  let fR : PeirceSpine.UniversalNoncommutativeOneForms.OneForms S →+ Ω[S⁄R] :=
    (oneFormsToKaehler R S).comp (PeirceSpine.UniversalNoncommutativeOneForms.rightAction S c)
  have hfR : fR = gL := by
    apply PeirceSpine.UniversalNoncommutativeOneForms.oneForms_addHom_ext S
    intro a b
    change oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.rightAction S c
        (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b)) =
      c • oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b)
    rw [PeirceSpine.UniversalNoncommutativeOneForms.rightAction_leftDifferentialForm, map_sub,
      oneFormsToKaehler_leftDifferentialForm, oneFormsToKaehler_leftDifferentialForm,
      oneFormsToKaehler_leftDifferentialForm, Derivation.leibniz]
    simp only [smul_add, smul_smul, mul_comm c a, add_sub_cancel_left]
  exact ⟨DFunLike.congr_fun hfL ω, DFunLike.congr_fun hfR ω⟩

/-- `[S3-07]` Compatibility of `oneFormsToKaehler` with Mathlib's universal property
`Derivation.liftKaehlerDifferential` for any commutative derivation `D : Derivation R S M`. -/
theorem oneFormsToKaehler_liftKaehlerDifferential_compat
    (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (D : Derivation R S M) (a b : S) :
    D.liftKaehlerDifferential
        (oneFormsToKaehler R S (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm S a b)) =
      a • D b := by
  rw [oneFormsToKaehler_leftDifferentialForm, map_smul,
    Derivation.liftKaehlerDifferential_comp_D]

/-- `[S3-07]` Noncommutative contrast witness: in `Matrix (Fin 2) (Fin 2) ℤ`, `leftAction`
and `rightAction` do NOT coincide on `OneForms A`. -/
theorem matrix_oneForms_leftAction_ne_rightAction :
    let A := Matrix (Fin 2) (Fin 2) ℤ
    let a : A := MatrixNoncommutativity.swapMatrix
    let b : A := MatrixNoncommutativity.tiltedMatrix
    PeirceSpine.UniversalNoncommutativeOneForms.leftAction A a
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) ≠
      PeirceSpine.UniversalNoncommutativeOneForms.rightAction A a
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) := by
  intro A a b h
  have heval := congrArg (Canonical.ConnesNCGFormAlgebra.connesUniversalOneFormMap (A := A) a) h
  rw [PeirceSpine.UniversalNoncommutativeOneForms.leftAction_differential,
    PeirceSpine.UniversalNoncommutativeOneForms.rightAction_differential,
    Canonical.ConnesNCGFormAlgebra.connesUniversalOneFormMap_leftDifferentialForm,
    Canonical.ConnesNCGFormAlgebra.connesUniversalOneFormMap_rightDifferentialForm] at heval
  have hne : a * Canonical.ConnesNCGFormAlgebra.ncDeriv a b ≠
      Canonical.ConnesNCGFormAlgebra.ncDeriv a b * a := by
    intro heq
    have h00 := congrArg (fun M : A => M 0 0) heq
    dsimp [a, b, Canonical.ConnesNCGFormAlgebra.ncDeriv, MatrixNoncommutativity.swapMatrix,
      MatrixNoncommutativity.tiltedMatrix] at h00
    revert h00
    decide
  exact hne heval

/-! ## Section 7: Karoubi (1983/1987) Commutator-Quotient de Rham Complex (`S3-08`) -/

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Degree-0 commutator subgroup `[A, A]` spanned by
`a * b - b * a` in any associative ring `[Ring A]`. -/
def karoubiCommutatorSubgroup0 (A : Type*) [Ring A] : AddSubgroup A :=
  AddSubgroup.closure {x : A | ∃ a b : A, x = a * b - b * a}

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Degree-1 commutator subgroup `[A, Ω¹(A)]` spanned by
`a · ω - ω · a` in `PeirceSpine.UniversalNoncommutativeOneForms.OneForms A`. -/
def karoubiCommutatorSubgroup1 (A : Type*) [Ring A] :
    AddSubgroup (PeirceSpine.UniversalNoncommutativeOneForms.OneForms A) :=
  AddSubgroup.closure
    {η : PeirceSpine.UniversalNoncommutativeOneForms.OneForms A |
      ∃ (a : A) (ω : PeirceSpine.UniversalNoncommutativeOneForms.OneForms A),
        η = PeirceSpine.UniversalNoncommutativeOneForms.leftAction A a ω -
          PeirceSpine.UniversalNoncommutativeOneForms.rightAction A a ω}

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Universal degree-0 Karoubi noncommutative de Rham
quotient `DR⁰(A) = A / [A, A]`. -/
abbrev KaroubiDR0 (A : Type*) [Ring A] := A ⧸ karoubiCommutatorSubgroup0 A

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Universal degree-1 Karoubi noncommutative de Rham
quotient `DR¹(A) = Ω¹(A) / [A, Ω¹(A)]`. -/
abbrev KaroubiDR1 (A : Type*) [Ring A] :=
  PeirceSpine.UniversalNoncommutativeOneForms.OneForms A ⧸ karoubiCommutatorSubgroup1 A

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Additive homomorphism packaging
`PeirceSpine.UniversalNoncommutativeOneForms.differential A`. -/
def universalDifferentialHom (A : Type*) [Ring A] :
    A →+ PeirceSpine.UniversalNoncommutativeOneForms.OneForms A where
  toFun := PeirceSpine.UniversalNoncommutativeOneForms.differential A
  map_zero' := by
    apply Subtype.ext
    simp [PeirceSpine.UniversalNoncommutativeOneForms.differential_val]
  map_add' x y := by
    apply Subtype.ext
    simp [PeirceSpine.UniversalNoncommutativeOneForms.differential_val,
      TensorProduct.tmul_add, TensorProduct.add_tmul]
    abel

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: For any `a, b : A`, `d(ab - ba) ∈ [A, Ω¹(A)]`
because `d(ab - ba) = (a db - (db)a) - (b da - (da)b)`. -/
theorem differential_commutator_mem_karoubiCommutatorSubgroup1 {A : Type*} [Ring A] (a b : A) :
    PeirceSpine.UniversalNoncommutativeOneForms.differential A (a * b - b * a) ∈
      karoubiCommutatorSubgroup1 A := by
  change universalDifferentialHom A (a * b - b * a) ∈ karoubiCommutatorSubgroup1 A
  rw [map_sub]
  change PeirceSpine.UniversalNoncommutativeOneForms.differential A (a * b) -
      PeirceSpine.UniversalNoncommutativeOneForms.differential A (b * a) ∈
    karoubiCommutatorSubgroup1 A
  rw [PeirceSpine.UniversalNoncommutativeOneForms.differential_mul_bimodule (A := A) a b,
    PeirceSpine.UniversalNoncommutativeOneForms.differential_mul_bimodule (A := A) b a]
  have h1 : PeirceSpine.UniversalNoncommutativeOneForms.leftAction A a
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) -
      PeirceSpine.UniversalNoncommutativeOneForms.rightAction A a
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) ∈
      karoubiCommutatorSubgroup1 A :=
    AddSubgroup.subset_closure ⟨a, PeirceSpine.UniversalNoncommutativeOneForms.differential A b, rfl⟩
  have h2 : PeirceSpine.UniversalNoncommutativeOneForms.leftAction A b
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A a) -
      PeirceSpine.UniversalNoncommutativeOneForms.rightAction A b
        (PeirceSpine.UniversalNoncommutativeOneForms.differential A a) ∈
      karoubiCommutatorSubgroup1 A :=
    AddSubgroup.subset_closure ⟨b, PeirceSpine.UniversalNoncommutativeOneForms.differential A a, rfl⟩
  have hid :
      (PeirceSpine.UniversalNoncommutativeOneForms.leftAction A a
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) +
        PeirceSpine.UniversalNoncommutativeOneForms.rightAction A b
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A a)) -
      (PeirceSpine.UniversalNoncommutativeOneForms.leftAction A b
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A a) +
        PeirceSpine.UniversalNoncommutativeOneForms.rightAction A a
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A b)) =
      (PeirceSpine.UniversalNoncommutativeOneForms.leftAction A a
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A b) -
        PeirceSpine.UniversalNoncommutativeOneForms.rightAction A a
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A b)) -
      (PeirceSpine.UniversalNoncommutativeOneForms.leftAction A b
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A a) -
        PeirceSpine.UniversalNoncommutativeOneForms.rightAction A b
          (PeirceSpine.UniversalNoncommutativeOneForms.differential A a)) := by
    abel
  rw [hid]
  exact AddSubgroup.sub_mem _ h1 h2

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Induced universal Karoubi differential
`d₀ : DR⁰(A) →+ DR¹(A)`. -/
def karoubiD0 (A : Type*) [Ring A] : KaroubiDR0 A →+ KaroubiDR1 A :=
  QuotientAddGroup.lift (karoubiCommutatorSubgroup0 A)
    ((QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A)).comp (universalDifferentialHom A))
    (fun x hx => by
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, b, rfl⟩ := hy
        exact (QuotientAddGroup.eq_zero_iff _).2
          (differential_commutator_mem_karoubiCommutatorSubgroup1 a b)
      | zero => simp
      | add y z _ _ hy hz =>
        change (QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A))
            (universalDifferentialHom A (y + z)) = 0
        rw [map_add, map_add, show (QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A))
            (universalDifferentialHom A y) = 0 from hy,
          show (QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A))
            (universalDifferentialHom A z) = 0 from hz, add_zero]
      | neg y _ hy =>
        change (QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A))
            (universalDifferentialHom A (-y)) = 0
        rw [map_neg, map_neg, show (QuotientAddGroup.mk' (karoubiCommutatorSubgroup1 A))
            (universalDifferentialHom A y) = 0 from hy, neg_zero])

@[simp] theorem karoubiD0_mk (A : Type*) [Ring A] (a : A) :
    karoubiD0 A (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (PeirceSpine.UniversalNoncommutativeOneForms.differential A a) :=
  rfl

/-- `[S3-08]` Any `NCG.TracialFunctional R A` factors through the degree-0 Karoubi quotient
`KaroubiDR0 A →+ R`. -/
def tracialFunctionalToKaroubiDR0 {R A : Type*} [Ring R] [Ring A] [Module R A]
    (τ : InfoGeometry.NCG.TracialFunctional R A) : KaroubiDR0 A →+ R :=
  QuotientAddGroup.lift (karoubiCommutatorSubgroup0 A) τ.toLinearMap.toAddMonoidHom
    (fun x hx => by
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, b, rfl⟩ := hy
        change τ.toLinearMap (a * b - b * a) = 0
        rw [map_sub, τ.cyclic a b, sub_self]
      | zero => exact map_zero τ.toLinearMap
      | add y z _ _ hy hz =>
        change τ.toLinearMap (y + z) = 0
        rw [map_add, show τ.toLinearMap y = 0 from hy, show τ.toLinearMap z = 0 from hz, add_zero]
      | neg y _ hy =>
        change τ.toLinearMap (-y) = 0
        rw [map_neg, show τ.toLinearMap y = 0 from hy, neg_zero])

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Graded commutator
`[ω, η]_gr = ω ∧ η - (-1)^(p*q) • η ∧ ω` on `ActionOperatorForm K` (`R3.4` noncommutative sign). -/
def gradedWedgeCommutator {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    ActionOperatorForm K (p + q) :=
  actionWedge K ω η -
    ((-1 : R) ^ (p * q)) • reindexForm (Nat.add_comm q p) (actionWedge K η ω)

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Graded commutator submodule `[Ω^•, Ω^•]_n` in degree `n`
for any faithfulness-free `LieActionLane R A` (`R3.4`). -/
def karoubiCommSubmodule {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (n : ℕ) : Submodule R (ActionOperatorForm K n) :=
  Submodule.span R
    {γ : ActionOperatorForm K n |
      ∃ (p q : ℕ) (hpq : p + q = n)
        (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
        γ = reindexForm hpq (gradedWedgeCommutator K ω η)}

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Arbitrary-degree Karoubi noncommutative de Rham
quotient `Ω̄ⁿ(K) = Ωⁿ(K) / [Ω^•, Ω^•]_n`. -/
abbrev KaroubiForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (n : ℕ) :=
  ActionOperatorForm K n ⧸ karoubiCommSubmodule K n

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Graded Leibniz rule for the exterior derivative on
graded commutators: `d([ω_p, η_q]_gr) = [dω_p, η_q]_gr + (-1)^p [ω_p, dη_q]_gr`. -/
theorem actionExteriorDerivative_gradedWedgeCommutator {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (K : LieActionLane R A) (hK : IsLeibnizAction K) {p q : ℕ}
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q) :
    actionExteriorDerivative K (p + q) (gradedWedgeCommutator K ω η) =
      reindexForm (by omega : (p + 1) + q = p + q + 1)
        (gradedWedgeCommutator K (actionExteriorDerivative K p ω) η) +
      ((-1 : R) ^ p) •
        reindexForm (by omega : p + (q + 1) = p + q + 1)
          (gradedWedgeCommutator K ω (actionExteriorDerivative K q η)) := by
  dsimp [gradedWedgeCommutator]
  rw [map_sub, map_smul, actionExteriorDerivative_reindexForm,
    actionExteriorDerivative_actionWedge K hK p q ω η,
    actionExteriorDerivative_actionWedge K hK q p η ω,
    reindexForm_add, reindexForm_smul, reindexForm_trans, reindexForm_trans]
  have h1 : ((-1 : R) ^ (p * q)) •
      ((-1 : R) ^ q • reindexForm (by omega : q + (p + 1) = p + q + 1)
        (actionWedge K η (actionExteriorDerivative K p ω))) =
      ((-1 : R) ^ ((p + 1) * q)) • reindexForm (by omega : q + (p + 1) = p + q + 1)
        (actionWedge K η (actionExteriorDerivative K p ω)) := by
    rw [smul_smul, ← pow_add, show p * q + q = (p + 1) * q by ring]
  have h2 : ((-1 : R) ^ (p * q)) •
      reindexForm (by omega : (q + 1) + p = p + q + 1)
        (actionWedge K (actionExteriorDerivative K q η) ω) =
      ((-1 : R) ^ p) • (((-1 : R) ^ (p * (q + 1))) •
        reindexForm (by omega : (q + 1) + p = p + q + 1)
          (actionWedge K (actionExteriorDerivative K q η) ω)) := by
    rw [smul_smul, ← pow_add]
    congr 1
    have hpow : (-1 : R) ^ (p + p * (q + 1)) = (-1 : R) ^ (p * q) * ((-1 : R) ^ p * (-1 : R) ^ p) := by
      rw [← pow_add, ← pow_add, show p + p * (q + 1) = p * q + (p + p) by ring]
    have hp : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
      rw [← mul_pow]
      have hneg1 : (-1 : R) * -1 = 1 := by ring
      simp [hneg1]
    rw [hpow, hp, mul_one]
  simp only [reindexForm_sub, reindexForm_smul, reindexForm_trans, smul_sub, smul_add]
  rw [h1, h2]
  ext v
  simp only [AlternatingMap.add_apply, AlternatingMap.sub_apply, AlternatingMap.smul_apply,
    reindexForm_apply]
  abel

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: `actionExteriorDerivative` preserves the graded
commutator submodule `[Ω^•, Ω^•]`. -/
theorem actionExteriorDerivative_maps_karoubiCommSubmodule {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (K : LieActionLane R A) (hK : IsLeibnizAction K) (n : ℕ) :
    Submodule.map (actionExteriorDerivative K n) (karoubiCommSubmodule K n) ≤
      karoubiCommSubmodule K (n + 1) := by
  rw [karoubiCommSubmodule, Submodule.map_span_le]
  rintro _ ⟨p, q, hpq, ω, η, rfl⟩
  rw [actionExteriorDerivative_reindexForm]
  have heq : reindexForm (congrArg (· + 1) hpq)
      (actionExteriorDerivative K (p + q) (gradedWedgeCommutator K ω η)) =
      reindexForm (by omega : (p + 1) + q = n + 1)
        (gradedWedgeCommutator K (actionExteriorDerivative K p ω) η) +
      ((-1 : R) ^ p) • reindexForm (by omega : p + (q + 1) = n + 1)
        (gradedWedgeCommutator K ω (actionExteriorDerivative K q η)) := by
    rw [actionExteriorDerivative_gradedWedgeCommutator K hK ω η,
      reindexForm_add, reindexForm_smul, reindexForm_trans, reindexForm_trans]
  rw [heq]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨p + 1, q, by omega, actionExteriorDerivative K p ω, η, rfl⟩
  · exact Submodule.subset_span ⟨p, q + 1, by omega, ω, actionExteriorDerivative K q η, rfl⟩

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Induced arbitrary-degree Karoubi differential
`d̄_n : KaroubiForm K n →ₗ[R] KaroubiForm K (n + 1)`. -/
def karoubiD {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (n : ℕ) :
    KaroubiForm K n →ₗ[R] KaroubiForm K (n + 1) :=
  Submodule.mapQ (karoubiCommSubmodule K n) (karoubiCommSubmodule K (n + 1))
    (actionExteriorDerivative K n)
    (Submodule.map_le_iff_le_comap.mp (actionExteriorDerivative_maps_karoubiCommSubmodule K hK n))

/-- `[S3-08]` Karoubi (1987) Ch. I §1.3: Complex property `d̄_{n+1} ∘ d̄_n = 0` on `KaroubiForm K`. -/
theorem karoubiD_comp_eq_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (hK : IsLeibnizAction K) (n : ℕ) :
    (karoubiD K hK (n + 1)).comp (karoubiD K hK n) = 0 := by
  apply LinearMap.ext
  intro qω
  induction qω using Submodule.Quotient.induction_on with
  | H ω =>
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, karoubiD]
    change (Submodule.mapQ _ _ (actionExteriorDerivative K (n + 1)) _)
        ((Submodule.mapQ _ _ (actionExteriorDerivative K n) _) (Submodule.Quotient.mk ω)) = 0
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply,
      actionExteriorDerivative_succ_comp K n ω, Submodule.Quotient.mk_zero]

/-! ## Section 8: Connes (1985) Quantized Calculus & Closed Graded Traces (`S3-09`) -/

/-- `[S3-09]` Connes (1985) Part I §§1–4: Under an involution `F² = 1`, the quantized
1-form `d_F a = [F, a]` anticommutes with `F`, i.e., `F (d_F a) = -(d_F a) F`. -/
theorem connes_quantizedDiff_odd_of_sq_one {A : Type*} [Ring A] (F a : A) (hF : F * F = 1) :
    F * Canonical.ConnesNCGFormAlgebra.ncDeriv F a =
      -(Canonical.ConnesNCGFormAlgebra.ncDeriv F a * F) := by
  dsimp [Canonical.ConnesNCGFormAlgebra.ncDeriv]
  calc F * (F * a - a * F) = (F * F) * a - F * a * F := by noncomm_ring
    _ = a - F * a * F := by rw [hF, one_mul]
    _ = -(F * a * F - a * (F * F)) := by rw [hF, mul_one]; noncomm_ring
    _ = -((F * a - a * F) * F) := by noncomm_ring

/-- `[S3-09]` Connes (1985) Part I §§1–4: Double quantized differential identity
`[F, [F, a]] = 2 • (a - F a F)` when `F² = 1`. -/
theorem connes_quantizedDiff_double_commutator {A : Type*} [Ring A] (F a : A) (hF : F * F = 1) :
    Canonical.ConnesNCGFormAlgebra.ncDeriv F (Canonical.ConnesNCGFormAlgebra.ncDeriv F a) =
      (2 : ℤ) • (a - F * a * F) := by
  dsimp [Canonical.ConnesNCGFormAlgebra.ncDeriv]
  calc F * (F * a - a * F) - (F * a - a * F) * F
      = (F * F) * a - F * a * F - F * a * F + a * (F * F) := by noncomm_ring
    _ = a - F * a * F - F * a * F + a := by rw [hF, one_mul, mul_one]
    _ = (2 : ℤ) • (a - F * a * F) := by rw [two_zsmul]; abel

/-- `[S3-09]` Connes (1985) Part II §1 pp. 93–96: A closed graded trace `∫ : Ωⁿ(K) →ₗ[R] R`
of dimension `n` satisfying `∫ dω = 0` and `∫ ω_p ∧ η_q = (-1)^(pq) ∫ η_q ∧ ω_p`. -/
structure ConnesClosedGradedTrace {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (n : ℕ) where
  int : ActionOperatorForm K n →ₗ[R] R
  closed : ∀ {m : ℕ} (h : m + 1 = n) (ω : ActionOperatorForm K m),
    int (reindexForm h (actionExteriorDerivative K m ω)) = 0
  graded_trace : ∀ {p q : ℕ} (hpq : p + q = n)
    (ω : ActionOperatorForm K p) (η : ActionOperatorForm K q),
    int (reindexForm hpq (actionWedge K ω η)) =
      ((-1 : R) ^ (p * q)) *
        int (reindexForm (Nat.add_comm q p ▸ hpq) (actionWedge K η ω))

/-- Constructive T17 witness (plus nontrivial matrix trace witness below) for
`ConnesClosedGradedTrace`. -/
def zeroConnesClosedGradedTrace {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : LieActionLane R A) (n : ℕ) : ConnesClosedGradedTrace K n where
  int := 0
  closed _ _ := rfl
  graded_trace _ _ _ := by simp

/-- `[S3-08]` Connes (1985) Part I §1: Nontrivial degree-0 `ConnesClosedGradedTrace` witness over
`Matrix (Fin 2) (Fin 2) ℝ` given by the matrix trace. -/
def mat2TraceConnesCycle :
    ConnesClosedGradedTrace (MaurerCartanTower.innerAlgLieActionLane ℝ (Matrix (Fin 2) (Fin 2) ℝ)) 0 where
  int :=
    { toFun := fun ω => Matrix.trace (ω Fin.elim0)
      map_add' := fun ω₁ ω₂ => by simp [Matrix.trace_add]
      map_smul' := fun r ω => by
        simp only [AlternatingMap.smul_apply, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply] }
  closed {m} h _ := by omega
  graded_trace {p q} hpq ω η := by
    have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp; subst hq
    simp only [LinearMap.coe_mk, AddHom.coe_mk, reindexForm_apply, mul_zero, pow_zero, one_mul]
    change Matrix.trace (actionWedge _ ω η Fin.elim0) = Matrix.trace (actionWedge _ η ω Fin.elim0)
    rw [actionWedge_zero_zero_apply, actionWedge_zero_zero_apply, Matrix.trace_mul_comm]

/-- `[S3-09]` Every Connes closed graded trace annihilates the Karoubi graded commutator
submodule `[Ω^•, Ω^•]_n`. -/
theorem connesClosedGradedTrace_ker_contains_karoubi {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {K : LieActionLane R A} {n : ℕ} (T : ConnesClosedGradedTrace K n) :
    karoubiCommSubmodule K n ≤ LinearMap.ker T.int := by
  rw [karoubiCommSubmodule, Submodule.span_le]
  rintro _ ⟨p, q, hpq, ω, η, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, gradedWedgeCommutator, reindexForm_sub, reindexForm_smul,
    map_sub, map_smul, smul_eq_mul, T.graded_trace hpq ω η]
  have heq : reindexForm hpq (reindexForm (Nat.add_comm q p) (actionWedge K η ω)) =
      reindexForm (Nat.add_comm q p ▸ hpq) (actionWedge K η ω) := by
    rw [reindexForm_trans]
  rw [heq, sub_self]

/-- `[S3-09]` Factorization of any `ConnesClosedGradedTrace` through the Karoubi quotient
`KaroubiForm K n →ₗ[R] R`. -/
def connesClosedGradedTraceToKaroubi {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : LieActionLane R A} {n : ℕ} (T : ConnesClosedGradedTrace K n) :
    KaroubiForm K n →ₗ[R] R :=
  Submodule.liftQ (karoubiCommSubmodule K n) T.int (connesClosedGradedTrace_ker_contains_karoubi T)

/-- `[S3-09]` Compatibility between `TracialFunctional` + `D`-invariance, universal 1-forms,
and `Physics.connes_cyclic_cohomology_synthesis`. -/
theorem connes_cyclic1_cocycle_synthesis_compat {A : Type*} [Ring A] [Algebra ℝ A]
    (data : InfoGeometry.Physics.CyclicTraceData A)
    (D : InfoGeometry.NCG.CyclicAlgebraDerivation ℝ A)
    (phi : InfoGeometry.Physics.Cochain0 A) (a0 a1 a2 : A) :
    InfoGeometry.Physics.hochschild_b1 (InfoGeometry.Physics.hochschild_b0 phi) a0 a1 a2 = 0 ∧
    InfoGeometry.Physics.hochschild_b1
      (PeirceSpine.UniversalNoncommutativeOneForms.connesCochain1 data D) a0 a1 a2 = 0 ∧
    InfoGeometry.Physics.hochschild_b0 data.Tr a0 a1 = 0 :=
  ⟨(InfoGeometry.Physics.connes_cyclic_cohomology_synthesis phi data a0 a1 a2).1,
   PeirceSpine.UniversalNoncommutativeOneForms.hochschild_b1_connesCochain1 data D a0 a1 a2,
   (InfoGeometry.Physics.connes_cyclic_cohomology_synthesis phi data a0 a1 a2).2⟩

/-! ## Section 9: Dubois-Violette (1988–1999) $Z(A)$-Lie-Rinehart Calculus & Central Bimodules (`S3-10`, `R3.4`) -/

/-- `[S3-10]` Dubois-Violette (1999) §7: Any Leibniz action preserves the center
`Subalgebra.center R A`. -/
theorem isLeibnizAction_preserves_center {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : LieActionLane R A} (hK : IsLeibnizAction K) (x : K.L) {z : A}
    (hz : z ∈ Subalgebra.center R A) :
    K.operatorAction x z ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  intro a
  have hz' := (Subalgebra.mem_center_iff.mp hz) a
  have h1 := hK x a z
  have h2 := hK x z a
  rw [hz'] at h1
  have heq : a * K.operatorAction x z + K.operatorAction x a * z =
      K.operatorAction x z * a + z * K.operatorAction x a := by
    calc a * K.operatorAction x z + K.operatorAction x a * z
        = K.operatorAction x a * z + a * K.operatorAction x z := add_comm _ _
      _ = K.operatorAction x (z * a) := h1.symm
      _ = K.operatorAction x z * a + z * K.operatorAction x a := h2
  have hcomm : K.operatorAction x a * z = z * K.operatorAction x a :=
    Subalgebra.mem_center_iff.mp hz (K.operatorAction x a)
  rw [hcomm] at heq
  exact add_right_cancel heq

/-- `[S3-10]` Dubois-Violette (1999) §7: Pointwise left multiplication by a central element
`z ∈ Z(A)` preserves `NonAssocDerivation.derivations R A`. -/
def centerSmulDerivation {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (z : Subalgebra.center R A) (D : NonAssocDerivation.derivations R A) :
    NonAssocDerivation.derivations R A :=
  ⟨{ toFun := fun a => z.1 * (D : Module.End R A) a
     map_add' := fun a b => by simp only [map_add, mul_add]
     map_smul' := fun r a => by
       simp only [map_smul, RingHom.id_apply, mul_smul_comm] },
   fun a b => by
     simp only [LinearMap.coe_mk, AddHom.coe_mk, NonAssocDerivation.derivations_leibniz, mul_add]
     have hz : (D : Module.End R A) a * z.1 = z.1 * (D : Module.End R A) a :=
       Subalgebra.mem_center_iff.mp z.2 ((D : Module.End R A) a)
     calc z.1 * ((D : Module.End R A) a * b) + z.1 * (a * (D : Module.End R A) b)
         = (z.1 * (D : Module.End R A) a) * b + (z.1 * a) * (D : Module.End R A) b := by noncomm_ring
       _ = (z.1 * (D : Module.End R A) a) * b + (a * z.1) * (D : Module.End R A) b := by
         rw [Subalgebra.mem_center_iff.mp z.2 a]
       _ = (z.1 * (D : Module.End R A) a) * b + a * (z.1 * (D : Module.End R A) b) := by
         noncomm_ring⟩

/-- `[S3-10]` Dubois-Violette (1999) §7: `Z(A)`-module structure on `NonAssocDerivation.derivations R A`. -/
scoped instance instModuleCenterDerivations {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    Module (Subalgebra.center R A) (NonAssocDerivation.derivations R A) where
  smul := centerSmulDerivation
  one_smul D := by
    apply Subtype.ext; ext a
    change (1 : A) * (D : Module.End R A) a = (D : Module.End R A) a
    rw [one_mul]
  mul_smul z₁ z₂ D := by
    apply Subtype.ext; ext a
    change (z₁.1 * z₂.1) * (D : Module.End R A) a = z₁.1 * (z₂.1 * (D : Module.End R A) a)
    rw [mul_assoc]
  smul_zero z := by
    apply Subtype.ext; ext a
    change z.1 * (0 : A) = 0
    rw [mul_zero]
  smul_add z D E := by
    apply Subtype.ext; ext a
    change z.1 * ((D : Module.End R A) a + (E : Module.End R A) a) =
      z.1 * (D : Module.End R A) a + z.1 * (E : Module.End R A) a
    rw [mul_add]
  add_smul z₁ z₂ D := by
    apply Subtype.ext; ext a
    change (z₁.1 + z₂.1) * (D : Module.End R A) a =
      z₁.1 * (D : Module.End R A) a + z₂.1 * (D : Module.End R A) a
    rw [add_mul]
  zero_smul D := by
    apply Subtype.ext; ext a
    change (0 : A) * (D : Module.End R A) a = 0
    rw [zero_mul]

scoped instance instIsScalarTowerCenterDerivations {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    IsScalarTower R (Subalgebra.center R A) (NonAssocDerivation.derivations R A) where
  smul_assoc r z D := by
    apply Subtype.ext; ext a
    change (r • z.1) * (D : Module.End R A) a = r • (z.1 * (D : Module.End R A) a)
    rw [smul_mul_assoc]

/-- `[S3-10]` Dubois-Violette (1999) §7: `Z(A)`-Lie-Rinehart bracket identity
`⁅D, z • E⁆ = ⟨D z, ...⟩ • E + z • ⁅D, E⁆` on `NonAssocDerivation.derivations R A`. -/
theorem derivations_center_lie_bracket {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (D E : NonAssocDerivation.derivations R A) (z : Subalgebra.center R A) :
    ⁅D, z • E⁆ =
      (⟨(D : Module.End R A) z.1,
        isLeibnizAction_preserves_center (fullDerivationLieLane R A).isLeibnizAction D z.2⟩ :
          Subalgebra.center R A) • E +
        z • ⁅D, E⁆ := by
  apply Subtype.ext
  ext a
  change (D : Module.End R A) (z.1 * (E : Module.End R A) a) -
      z.1 * (E : Module.End R A) ((D : Module.End R A) a) =
    (D : Module.End R A) z.1 * (E : Module.End R A) a +
      z.1 * ((D : Module.End R A) ((E : Module.End R A) a) -
        (E : Module.End R A) ((D : Module.End R A) a))
  rw [NonAssocDerivation.derivations_leibniz]
  noncomm_ring

/-- `[S3-10]` Dubois-Violette (1999) §§7–8: Faithfulness-free central `Z(A)`-Lie-Rinehart
lane extending `LieActionLane R A` with a `Z(A)`-module structure (`R3.4`). -/
structure CentralLieRinehartLane.{u₁, u₂, u₃} (R : Type u₁) (A : Type u₂)
    [CommRing R] [Ring A] [Algebra R A] where
  lane : LieActionLane.{u₁, u₂, u₃} R A
  isLeibniz : IsLeibnizAction lane
  moduleZ : Module (Subalgebra.center R A) lane.L
  isScalarTowerZ : IsScalarTower R (Subalgebra.center R A) lane.L
  act_smul_center : ∀ (z : Subalgebra.center R A) (x : lane.L) (a : A),
    lane.operatorAction (z • x) a = z.1 * lane.operatorAction x a
  bracket_smul_center : ∀ (x y : lane.L) (z : Subalgebra.center R A),
    ⁅x, z • y⁆ =
      (⟨lane.operatorAction x z.1,
        isLeibnizAction_preserves_center isLeibniz x z.2⟩ : Subalgebra.center R A) • y +
        z • ⁅x, y⁆

attribute [instance] CentralLieRinehartLane.moduleZ CentralLieRinehartLane.isScalarTowerZ

/-- `[S3-10]` Canonical `CentralLieRinehartLane R A` on `NonAssocDerivation.derivations R A`. -/
def fullCentralLieRinehartLane (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : CentralLieRinehartLane R A where
  lane := (fullDerivationLieLane R A).toLieActionLane
  isLeibniz := (fullDerivationLieLane R A).isLeibnizAction
  moduleZ := instModuleCenterDerivations
  isScalarTowerZ := instIsScalarTowerCenterDerivations
  act_smul_center _ _ _ := rfl
  bracket_smul_center D E z := derivations_center_lie_bracket D E z

/-- Constructive T17 witness for `CentralLieRinehartLane` on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def concreteMat2CentralLieRinehartLane :
    CentralLieRinehartLane ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  fullCentralLieRinehartLane ℝ (Matrix (Fin 2) (Fin 2) ℝ)

/-- `[S3-10]` Left `Z(A)`-linearity of the Lie bracket on `CentralLieRinehartLane`:
`⁅z • x, y⁆ = z • ⁅x, y⁆ - ⟨y z, ...⟩ • x`. -/
theorem CentralLieRinehartLane.bracket_smul_center_left {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) (x y : K.lane.L) :
    ⁅z • x, y⁆ =
      z • ⁅x, y⁆ -
        (⟨K.lane.operatorAction y z.1,
          isLeibnizAction_preserves_center K.isLeibniz y z.2⟩ : Subalgebra.center R A) • x := by
  rw [← lie_skew (z • x) y, K.bracket_smul_center y x z, neg_add, ← lie_skew x y]
  simp only [smul_neg, sub_eq_add_neg, add_comm]

/-- `[S3-10]` Dubois-Violette (1999) §7: Central `Z(A)`-multilinearity predicate on
`ActionOperatorForm K.lane n`. -/
def IsCentralMultilinear {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : CentralLieRinehartLane R A} {n : ℕ} (ω : ActionOperatorForm K.lane n) : Prop :=
  ∀ (z : Subalgebra.center R A) (v : Fin n → K.lane.L) (i : Fin n),
    ω (Function.update v i (z • v i)) = z.1 * ω v

/-- `[S3-10]` Left multiplication of an `ActionOperatorForm K.lane n` by a central element
`z ∈ Z(A)`. -/
def centralSmulForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) {n : ℕ}
    (ω : ActionOperatorForm K.lane n) : ActionOperatorForm K.lane n where
  toFun v := z.1 * ω v
  map_update_add' v i x y := by simp [ω.map_update_add, mul_add]
  map_update_smul' v i r x := by simp [ω.map_update_smul, Algebra.mul_smul_comm]
  map_eq_zero_of_eq' v {i j} hv hij := by rw [ω.map_eq_zero_of_eq v hv hij, mul_zero]

@[simp] theorem centralSmulForm_apply {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) {n : ℕ}
    (ω : ActionOperatorForm K.lane n) (v : Fin n → K.lane.L) :
    centralSmulForm K z ω v = z.1 * ω v :=
  rfl

/-- `[S3-10]` Dubois-Violette (1999) §7: Left contraction commutes with central scalar multiplication
`z ∈ Z(A)` on `ActionOperatorForm`. -/
theorem centralSmulForm_curryLeft {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) {n : ℕ}
    (ω : ActionOperatorForm K.lane (n + 1)) (x : K.lane.L) :
    (centralSmulForm K z ω).curryLeft x = centralSmulForm K z (ω.curryLeft x) := by
  ext v
  rfl

/-- `[S3-10]` Dubois-Violette (1999) §7: Left contraction of a central-multilinear form at `z • x`
equals central multiplication by `z` applied to contraction at `x`. -/
theorem isCentralMultilinear_curryLeft_center_smul {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {K : CentralLieRinehartLane R A} {n : ℕ}
    {ω : ActionOperatorForm K.lane (n + 1)} (hω : IsCentralMultilinear ω)
    (z : Subalgebra.center R A) (x : K.lane.L) :
    ω.curryLeft (z • x) = centralSmulForm K z (ω.curryLeft x) := by
  ext v
  have hupd : Matrix.vecCons (z • x) v = Function.update (Matrix.vecCons x v) 0 (z • x) := by
    ext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl
  change ω (Matrix.vecCons (z • x) v) = z.1 * ω (Matrix.vecCons x v)
  rw [hupd]
  exact hω z (Matrix.vecCons x v) 0

/-- `[S3-10]` Dubois-Violette (1999) §7: Left contraction preserves `IsCentralMultilinear`. -/
theorem isCentralMultilinear_curryLeft {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : CentralLieRinehartLane R A} {n : ℕ} {ω : ActionOperatorForm K.lane (n + 1)}
    (hω : IsCentralMultilinear ω) (x : K.lane.L) :
    IsCentralMultilinear (ω.curryLeft x) := by
  intro z v i
  have hupd : Matrix.vecCons x (Function.update v i (z • v i)) =
      Function.update (Matrix.vecCons x v) i.succ (z • (Matrix.vecCons x v) i.succ) := by
    ext j
    induction j using Fin.cases with
    | zero => rfl
    | succ k =>
      change Function.update v i (z • v i) k =
        Function.update (Matrix.vecCons x v) i.succ (z • v i) k.succ
      by_cases hki : k = i
      · subst hki; simp
      · have hne : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
        simp [Function.update_of_ne hki, Function.update_of_ne hne, Matrix.vecCons]
  change ω (Matrix.vecCons x (Function.update v i (z • v i))) =
    z.1 * ω (Matrix.vecCons x v)
  rw [hupd]
  exact hω z (Matrix.vecCons x v) i.succ

/-- `[S3-10]` Dubois-Violette (1999) §7: Lie derivative preserves `IsCentralMultilinear` on a
`CentralLieRinehartLane`. -/
theorem isCentralMultilinear_lieDeriv {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {K : CentralLieRinehartLane R A} {n : ℕ} {ω : ActionOperatorForm K.lane n}
    (hω : IsCentralMultilinear ω) (x : K.lane.L) :
    IsCentralMultilinear (lieDeriv K.lane x ω) := by
  intro z v i
  simp only [lieDeriv_apply]
  have hupdate : ω (Function.update v i (z • v i)) = z.1 * ω v := hω z v i
  rw [hupdate, K.isLeibniz x z.1 (ω v), mul_sub]
  have hsum : ∑ j : Fin n, ω (Function.update (Function.update v i (z • v i)) j
        ⁅x, Function.update v i (z • v i) j⁆) =
      K.lane.operatorAction x z.1 * ω v +
        z.1 * ∑ j : Fin n, ω (Function.update v j ⁅x, v j⁆) := by
    rw [Finset.mul_sum]
    have hsplit : ∀ j : Fin n,
        ω (Function.update (Function.update v i (z • v i)) j
          ⁅x, Function.update v i (z • v i) j⁆) =
        z.1 * ω (Function.update v j ⁅x, v j⁆) +
          (if j = i then K.lane.operatorAction x z.1 * ω v else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_idem, Function.update_self, ↓reduceIte]
        rw [K.bracket_smul_center x (v j) z]
        have hadd := ω.map_update_add v j
          ((⟨K.lane.operatorAction x z.1,
            isLeibnizAction_preserves_center K.isLeibniz x z.2⟩ :
              Subalgebra.center R A) • v j) (z • ⁅x, v j⁆)
        rw [hadd,
          hω ⟨K.lane.operatorAction x z.1,
            isLeibnizAction_preserves_center K.isLeibniz x z.2⟩ v j]
        have hz2 : ω (Function.update v j (z • ⁅x, v j⁆)) =
            z.1 * ω (Function.update v j ⁅x, v j⁆) := by
          have h := hω z (Function.update v j ⁅x, v j⁆) j
          simpa using h
        rw [hz2, add_comm]
      · have hij : i ≠ j := Ne.symm hji
        have hne : Function.update v i (z • v i) j = v j := Function.update_of_ne hji _ v
        rw [hne, Function.update_comm hij, ite_eq_right_iff.mpr (fun h => absurd h hji), add_zero]
        have hsub_u : Function.update (Function.update v j ⁅x, v j⁆) i (z • v i) =
            Function.update (Function.update v j ⁅x, v j⁆) i
              (z • (Function.update v j ⁅x, v j⁆) i) := by
          rw [Function.update_of_ne hij]
        rw [hsub_u]
        exact hω z (Function.update v j ⁅x, v j⁆) i
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hite : (∑ j : Fin n, if j = i then K.lane.operatorAction x z.1 * ω v else 0) =
        K.lane.operatorAction x z.1 * ω v := by
      simp
    rw [hite, add_comm]
  rw [hsum]
  abel

private theorem lieDeriv_centralSmulForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) {n : ℕ}
    (y : K.lane.L) (α : ActionOperatorForm K.lane n) :
    lieDeriv K.lane y (centralSmulForm K z α) =
      centralSmulForm K ⟨K.lane.operatorAction y z.1,
        isLeibnizAction_preserves_center K.isLeibniz y z.2⟩ α +
        centralSmulForm K z (lieDeriv K.lane y α) := by
  ext v
  simp only [lieDeriv_apply, centralSmulForm_apply, AlternatingMap.add_apply]
  rw [K.isLeibniz y z.1 (α v), ← Finset.mul_sum, mul_sub]
  abel

private theorem curryLeft_curryLeft_skew {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    {K : LieActionLane R A} {n : ℕ} (ω : ActionOperatorForm K (n + 2)) (x y : K.L) :
    (ω.curryLeft x).curryLeft y = -((ω.curryLeft y).curryLeft x) := by
  ext v
  simp only [AlternatingMap.curryLeft_apply_apply, AlternatingMap.neg_apply]
  have hswap : Matrix.vecCons x (Matrix.vecCons y v) =
      (Matrix.vecCons y (Matrix.vecCons x v)) ∘ Equiv.swap (0 : Fin (n + 2)) 1 := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
      induction j using Fin.cases with
      | zero => simp
      | succ k =>
        change v k = Matrix.vecCons y (Matrix.vecCons x v)
          (Equiv.swap (0 : Fin (n + 2)) 1 k.succ.succ)
        have h0 : k.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
        have h1 : k.succ.succ ≠ (1 : Fin (n + 2)) := by
          intro h
          have := congrArg Fin.val h
          simp at this
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
        rfl
  rw [hswap, ω.map_swap (Matrix.vecCons y (Matrix.vecCons x v)) Fin.zero_ne_one]

private theorem actionExteriorDerivative_central_residual_aux
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (z : Subalgebra.center R A) :
    ∀ (n : ℕ) (x : K.lane.L) (ω : ActionOperatorForm K.lane (n + 1)),
      IsCentralMultilinear ω →
      lieDeriv K.lane (z • x) ω -
          actionExteriorDerivative K.lane n (centralSmulForm K z (ω.curryLeft x)) =
        centralSmulForm K z
          (lieDeriv K.lane x ω - actionExteriorDerivative K.lane n (ω.curryLeft x))
  | 0, x, ω, hω => by
    ext v
    have hv : v = ![v 0] := by ext i; fin_cases i; rfl
    rw [hv]
    simp only [AlternatingMap.sub_apply, lieDeriv_apply, centralSmulForm_apply,
      actionExteriorDerivative_zero_apply, AlternatingMap.curryLeft_apply_apply]
    have hcons : Matrix.vecCons x (Fin.elim0 : Fin 0 → K.lane.L) = ![x] := by
      ext i; fin_cases i; rfl
    have hsum1 : (∑ i : Fin 1, ω (Function.update ![v 0] i ⁅z • x, ![v 0] i⁆)) =
        ω ![⁅z • x, v 0⁆] := by
      rw [Fin.sum_univ_one]
      congr 1; ext i; fin_cases i; rfl
    have hsum2 : (∑ i : Fin 1, ω (Function.update ![v 0] i ⁅x, ![v 0] i⁆)) =
        ω ![⁅x, v 0⁆] := by
      rw [Fin.sum_univ_one]
      congr 1; ext i; fin_cases i; rfl
    rw [hcons, hsum1, hsum2, K.act_smul_center z x (ω ![v 0]),
      K.bracket_smul_center_left z x (v 0)]
    let wZ : Subalgebra.center R A :=
      ⟨K.lane.operatorAction (v 0) z.1,
        isLeibnizAction_preserves_center K.isLeibniz (v 0) z.2⟩
    have hsub_form : ω ![z • ⁅x, v 0⁆ - wZ • x] = ω ![z • ⁅x, v 0⁆] - ω ![wZ • x] := by
      have hupd3 : ![z • ⁅x, v 0⁆ - wZ • x] =
          Function.update ![x] 0 (z • ⁅x, v 0⁆ + -(wZ • x)) := by
        ext i; fin_cases i; exact sub_eq_add_neg _ _
      have hupd4 : ![z • ⁅x, v 0⁆] = Function.update ![x] 0 (z • ⁅x, v 0⁆) := by
        ext i; fin_cases i; rfl
      have hupd5 : ![wZ • x] = Function.update ![x] 0 (wZ • x) := by
        ext i; fin_cases i; rfl
      rw [hupd3, ω.map_update_add, ω.map_update_neg, ← hupd4, ← hupd5, ← sub_eq_add_neg]
    have h1 : ω ![z • ⁅x, v 0⁆] = z.1 * ω ![⁅x, v 0⁆] := by
      have h := hω z ![⁅x, v 0⁆] 0
      have hupd : Function.update ![⁅x, v 0⁆] 0 (z • ![⁅x, v 0⁆] 0) = ![z • ⁅x, v 0⁆] := by
        ext i; fin_cases i; rfl
      rwa [hupd] at h
    have h2 : ω ![wZ • x] = wZ.1 * ω ![x] := by
      have h := hω wZ ![x] 0
      have hupd : Function.update ![x] 0 (wZ • ![x] 0) = ![wZ • x] := by
        ext i; fin_cases i; rfl
      rwa [hupd] at h
    rw [hsub_form, h1, h2]
    simp only [Matrix.cons_val_zero]
    rw [K.isLeibniz (v 0) z.1 (ω ![x]), mul_sub]
    dsimp only [wZ]
    noncomm_ring
  | m + 1, x, ω, hω => by
    apply alternating_ext_curryLeft
    intro y
    have hcl_sub1 : (lieDeriv K.lane (z • x) ω -
        actionExteriorDerivative K.lane (m + 1) (centralSmulForm K z (ω.curryLeft x))).curryLeft y =
        (lieDeriv K.lane (z • x) ω).curryLeft y -
          (actionExteriorDerivative K.lane (m + 1) (centralSmulForm K z (ω.curryLeft x))).curryLeft y :=
      rfl
    have hcl_sub2 : (centralSmulForm K z
        (lieDeriv K.lane x ω - actionExteriorDerivative K.lane (m + 1) (ω.curryLeft x))).curryLeft y =
        centralSmulForm K z ((lieDeriv K.lane x ω).curryLeft y -
          (actionExteriorDerivative K.lane (m + 1) (ω.curryLeft x)).curryLeft y) :=
      rfl
    rw [hcl_sub1, hcl_sub2, lieDeriv_curryLeft,
      actionExteriorDerivative_succ_curryLeft, centralSmulForm_curryLeft,
      lieDeriv_curryLeft, actionExteriorDerivative_succ_curryLeft]
    rw [K.bracket_smul_center_left z x y]
    let wZ : Subalgebra.center R A :=
      ⟨K.lane.operatorAction y z.1,
        isLeibnizAction_preserves_center K.isLeibniz y z.2⟩
    have hcur_sub : ω.curryLeft (z • ⁅x, y⁆ - wZ • x) =
        centralSmulForm K z (ω.curryLeft ⁅x, y⁆) - centralSmulForm K wZ (ω.curryLeft x) := by
      ext w
      have hupd : Matrix.vecCons (z • ⁅x, y⁆ - wZ • x) w =
          Function.update (Matrix.vecCons x w) 0 (z • ⁅x, y⁆ + -(wZ • x)) := by
        ext i; induction i using Fin.cases with
        | zero => exact sub_eq_add_neg _ _
        | succ _ => rfl
      change ω (Matrix.vecCons _ w) = z.1 * ω (Matrix.vecCons ⁅x, y⁆ w) -
        wZ.1 * ω (Matrix.vecCons x w)
      rw [hupd, ω.map_update_add, ω.map_update_neg]
      have ha : ω (Function.update (Matrix.vecCons x w) 0 (z • ⁅x, y⁆)) =
          z.1 * ω (Matrix.vecCons ⁅x, y⁆ w) := by
        have h := hω z (Matrix.vecCons ⁅x, y⁆ w) 0
        have hupd' : Function.update (Matrix.vecCons ⁅x, y⁆ w) 0
            (z • Matrix.vecCons ⁅x, y⁆ w 0) =
            Function.update (Matrix.vecCons x w) 0 (z • ⁅x, y⁆) := by
          ext i; induction i using Fin.cases <;> rfl
        rwa [hupd'] at h
      have hb : ω (Function.update (Matrix.vecCons x w) 0 (wZ • x)) =
          wZ.1 * ω (Matrix.vecCons x w) := by
        have h := hω wZ (Matrix.vecCons x w) 0
        simpa using h
      rw [ha, hb, sub_eq_add_neg]
    rw [hcur_sub, lieDeriv_centralSmulForm K z y (ω.curryLeft x)]
    have hskew : (ω.curryLeft x).curryLeft y = -((ω.curryLeft y).curryLeft x) :=
      curryLeft_curryLeft_skew ω x y
    have hsmul_neg : centralSmulForm K z ((ω.curryLeft x).curryLeft y) =
        -centralSmulForm K z ((ω.curryLeft y).curryLeft x) := by
      rw [hskew]
      ext w
      simp [centralSmulForm]
    rw [hsmul_neg, map_neg, sub_neg_eq_add]
    have ih := actionExteriorDerivative_central_residual_aux K z m x (ω.curryLeft y)
      (isCentralMultilinear_curryLeft hω y)
    ext w
    have ihw := AlternatingMap.congr_fun ih w
    simp only [AlternatingMap.sub_apply, AlternatingMap.add_apply,
      centralSmulForm_apply] at ihw ⊢
    have hw_neg : actionExteriorDerivative K.lane m ((ω.curryLeft x).curryLeft y) w =
        -(actionExteriorDerivative K.lane m ((ω.curryLeft y).curryLeft x) w) := by
      rw [hskew, map_neg, AlternatingMap.neg_apply]
    rw [hw_neg]
    dsimp only [wZ]
    calc (lieDeriv K.lane (z • x) (ω.curryLeft y) w -
            (z.1 * ω.curryLeft ⁅x, y⁆ w - K.lane.operatorAction y z.1 * ω.curryLeft x w)) -
          (K.lane.operatorAction y z.1 * ω.curryLeft x w +
            z.1 * lieDeriv K.lane y (ω.curryLeft x) w +
            actionExteriorDerivative K.lane m (centralSmulForm K z ((ω.curryLeft y).curryLeft x)) w)
        = (lieDeriv K.lane (z • x) (ω.curryLeft y) w -
            actionExteriorDerivative K.lane m (centralSmulForm K z ((ω.curryLeft y).curryLeft x)) w) -
            z.1 * ω.curryLeft ⁅x, y⁆ w - z.1 * lieDeriv K.lane y (ω.curryLeft x) w := by abel
      _ = z.1 * (lieDeriv K.lane x (ω.curryLeft y) w -
            actionExteriorDerivative K.lane m ((ω.curryLeft y).curryLeft x) w) -
            z.1 * ω.curryLeft ⁅x, y⁆ w - z.1 * lieDeriv K.lane y (ω.curryLeft x) w := by rw [ihw]
      _ = z.1 * (lieDeriv K.lane x (ω.curryLeft y) w - ω.curryLeft ⁅x, y⁆ w -
            (lieDeriv K.lane y (ω.curryLeft x) w -
              -(actionExteriorDerivative K.lane m ((ω.curryLeft y).curryLeft x) w))) := by
          noncomm_ring

/-- `[S3-10]` Dubois-Violette (1999) §7: For every degree `n : ℕ`, `actionExteriorDerivative K.lane n`
preserves `IsCentralMultilinear`, making `DuboisVioletteForm K n` a subcomplex `Ω^•_Der(A)`. -/
theorem isCentralMultilinear_actionExteriorDerivative {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {K : CentralLieRinehartLane R A} :
    ∀ (n : ℕ) (ω : ActionOperatorForm K.lane n),
      IsCentralMultilinear ω → IsCentralMultilinear (actionExteriorDerivative K.lane n ω)
  | 0, ω, _ => by
    intro z v i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have hupd : Function.update v 0 (z • v 0) = ![z • v 0] := by
      ext j; fin_cases j; rfl
    have hv : v = ![v 0] := by
      ext j; fin_cases j; rfl
    rw [hupd, hv]
    simp only [actionExteriorDerivative_zero_apply, Matrix.cons_val_zero]
    exact K.act_smul_center z (v 0) (ω Fin.elim0)
  | m + 1, ω, hω => by
    intro z v i
    induction i using Fin.cases with
    | zero =>
      have hupd : Function.update v 0 (z • v 0) = Matrix.vecCons (z • v 0) (Fin.tail v) := by
        ext j
        induction j using Fin.cases with
        | zero => rfl
        | succ k => rfl
      have hv : v = Matrix.vecCons (v 0) (Fin.tail v) := by
        ext j
        induction j using Fin.cases with
        | zero => rfl
        | succ k => rfl
      rw [hupd]
      conv_rhs => rw [hv]
      rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply]
      rw [actionExteriorDerivative_succ_curryLeft, actionExteriorDerivative_succ_curryLeft,
        isCentralMultilinear_curryLeft_center_smul hω z (v 0)]
      have hres := congrArg (fun α : ActionOperatorForm K.lane (m + 1) => α (Fin.tail v))
        (actionExteriorDerivative_central_residual_aux K z m (v 0) ω hω)
      exact hres
    | succ j =>
      have hupd : Function.update v j.succ (z • v j.succ) =
          Matrix.vecCons (v 0) (Function.update (Fin.tail v) j (z • (Fin.tail v) j)) := by
        ext k
        induction k using Fin.cases with
        | zero => rfl
        | succ l =>
          change Function.update v j.succ (z • v j.succ) l.succ =
            Function.update (Fin.tail v) j (z • (Fin.tail v) j) l
          by_cases hlj : l = j
          · subst hlj; simp [Fin.tail]
          · have hne : l.succ ≠ j.succ := fun h => hlj (Fin.succ_inj.mp h)
            simp [Function.update_of_ne hne, Function.update_of_ne hlj, Fin.tail]
      have hv : v = Matrix.vecCons (v 0) (Fin.tail v) := by
        ext k
        induction k using Fin.cases <;> rfl
      rw [hupd]
      conv_rhs => rw [hv]
      rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply,
        actionExteriorDerivative_succ_curryLeft]
      have hlie := isCentralMultilinear_lieDeriv hω (v 0) z (Fin.tail v) j
      have hd := isCentralMultilinear_actionExteriorDerivative m (ω.curryLeft (v 0))
        (isCentralMultilinear_curryLeft hω (v 0)) z (Fin.tail v) j
      simp only [AlternatingMap.sub_apply] at hlie hd ⊢
      rw [hlie, hd, mul_sub]

/-- `[S3-10]` Dubois-Violette (1999) §§7–8: The `Z(A)`-multilinear derivation differential
forms submodule `Ω^n_Der(A) ⊆ ActionOperatorForm K.lane n`. -/
def DuboisVioletteForm {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (n : ℕ) : Submodule R (ActionOperatorForm K.lane n) where
  carrier := {ω | IsCentralMultilinear ω}
  zero_mem' _ _ _ := by simp
  add_mem' {ω₁ ω₂} h₁ h₂ z v i := by
    simp only [AlternatingMap.add_apply, h₁ z v i, h₂ z v i, mul_add]
  smul_mem' r {ω} h z v i := by
    simp only [AlternatingMap.smul_apply, h z v i, Algebra.mul_smul_comm]

/-- `[S3-10]` Dubois-Violette (1999) §§7–8: Arbitrary-degree exterior derivative
`d_Der : DuboisVioletteForm K n →ₗ[R] DuboisVioletteForm K (n + 1)` with `d_Der² = 0`. -/
def duboisVioletteD {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (n : ℕ) :
    DuboisVioletteForm K n →ₗ[R] DuboisVioletteForm K (n + 1) where
  toFun ω := ⟨actionExteriorDerivative K.lane n ω.1,
    isCentralMultilinear_actionExteriorDerivative n ω.1 ω.2⟩
  map_add' ω₁ ω₂ := by apply Subtype.ext; simp
  map_smul' r ω := by apply Subtype.ext; simp

/-- `[S3-10]` Complex property `d_Der ∘ d_Der = 0` on `DuboisVioletteForm`. -/
theorem duboisVioletteD_comp_eq_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) (n : ℕ) :
    (duboisVioletteD K (n + 1)).comp (duboisVioletteD K n) = 0 := by
  ext ω v
  exact AlternatingMap.congr_fun (actionExteriorDerivative_succ_comp K.lane n ω.1) v

/-- `[S3-10]` Dubois-Violette (1999) Prop. 5 & Prop. 11: Canonical universal comparison map
`Ω¹_univ(A) →+ Ω¹_Der(A)` landing in `DuboisVioletteForm`. -/
def universalOneFormToDuboisViolette {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [IsScalarTower R A A] [SMulCommClass R A A] :
    PeirceSpine.UniversalNoncommutativeOneForms.OneForms A →+
      DuboisVioletteForm (fullCentralLieRinehartLane R A) 1 where
  toFun ω :=
    ⟨PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
        (fullDerivationLieLane R A) ω,
      by
        intro z v i
        have hi : i = 0 := Fin.eq_zero i
        subst hi
        let zv : (fullDerivationLieLane R A).L := z • v 0
        let v' : Fin 1 → (fullDerivationLieLane R A).L := v
        let f1 : PeirceSpine.UniversalNoncommutativeOneForms.OneForms A →+ A :=
          { toFun := fun η =>
              PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
                (fullDerivationLieLane R A) η (Function.update v' 0 zv)
            map_zero' := by simp
            map_add' := fun η₁ η₂ => by simp }
        let f2 : PeirceSpine.UniversalNoncommutativeOneForms.OneForms A →+ A :=
          { toFun := fun η => z.1 *
              PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
                (fullDerivationLieLane R A) η v'
            map_zero' := by simp
            map_add' := fun η₁ η₂ => by
              simp only [map_add, AlternatingMap.add_apply, mul_add] }
        have heq : f1 = f2 := by
          apply PeirceSpine.UniversalNoncommutativeOneForms.oneForms_addHom_ext A
          intro a b
          change PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
              (fullDerivationLieLane R A)
              (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm A a b)
              (Function.update v' 0 zv) =
            z.1 * PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
              (fullDerivationLieLane R A)
              (PeirceSpine.UniversalNoncommutativeOneForms.leftDifferentialForm A a b) v'
          simp only [PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm_leftDifferentialForm,
            Function.update_self]
          have hzv : (fullDerivationLieLane R A).operatorAction zv b =
              z.1 * (fullDerivationLieLane R A).operatorAction (v' 0) b :=
            (fullCentralLieRinehartLane R A).act_smul_center z (v 0) b
          rw [hzv, ← mul_assoc, Subalgebra.mem_center_iff.mp z.2 a, mul_assoc]
        exact DFunLike.congr_fun heq ω⟩
  map_zero' := by
    apply Subtype.ext
    ext v
    rfl
  map_add' ω₁ ω₂ := by
    apply Subtype.ext
    ext v
    let v' : Fin 1 → (fullDerivationLieLane R A).L := v
    change (PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
        (fullDerivationLieLane R A) (ω₁ + ω₂)) v' =
      (PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
        (fullDerivationLieLane R A) ω₁ +
       PeirceSpine.UniversalNoncommutativeOneForms.universalOneFormToDerivationForm
        (fullDerivationLieLane R A) ω₂) v'
    rw [map_add]

/-- `[S3-10]` Dubois-Violette & Michor (1996) §2: A central `A`-bimodule `M` satisfies
`z • m = m • z` for all central elements `z ∈ Z(A)`. -/
structure CentralBimodule (R A M : Type*) [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] where
  lsmul : A → M → M
  rsmul : M → A → M
  lsmul_add_right : ∀ a m n, lsmul a (m + n) = lsmul a m + lsmul a n
  lsmul_add_left : ∀ a b m, lsmul (a + b) m = lsmul a m + lsmul b m
  lsmul_mul : ∀ a b m, lsmul (a * b) m = lsmul a (lsmul b m)
  one_lsmul : ∀ m, lsmul 1 m = m
  rsmul_add_left : ∀ m n a, rsmul (m + n) a = rsmul m a + rsmul n a
  rsmul_add_right : ∀ m a b, rsmul m (a + b) = rsmul m a + rsmul m b
  rsmul_mul : ∀ m a b, rsmul m (a * b) = rsmul (rsmul m a) b
  rsmul_one : ∀ m, rsmul m 1 = m
  lsmul_rsmul_assoc : ∀ a m b, lsmul a (rsmul m b) = rsmul (lsmul a m) b
  central_comm : ∀ (z : Subalgebra.center R A) (m : M), lsmul z.1 m = rsmul m z.1

/-- `[S3-10]` Dubois-Violette & Michor (1996) §2: Canonical self-bimodule structure on `A`. -/
def algebraSelfCentralBimodule (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    CentralBimodule R A A where
  lsmul a b := a * b
  rsmul a b := a * b
  lsmul_add_right _ _ _ := mul_add _ _ _
  lsmul_add_left _ _ _ := add_mul _ _ _
  lsmul_mul _ _ _ := mul_assoc _ _ _
  one_lsmul _ := one_mul _
  rsmul_add_left _ _ _ := add_mul _ _ _
  rsmul_add_right _ _ _ := mul_add _ _ _
  rsmul_mul _ _ _ := (mul_assoc _ _ _).symm
  rsmul_one _ := mul_one _
  lsmul_rsmul_assoc _ _ _ := (mul_assoc _ _ _).symm
  central_comm z m := (Subalgebra.mem_center_iff.mp z.2 m).symm

/-- Constructive T17 witness for `CentralBimodule` on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def concreteMat2CentralBimodule :
    CentralBimodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) (Matrix (Fin 2) (Fin 2) ℝ) :=
  algebraSelfCentralBimodule ℝ (Matrix (Fin 2) (Fin 2) ℝ)

/-- `[S3-10]` Dubois-Violette & Michor (1996) §§2–4: Central bimodule connection over a
faithfulness-free `CentralLieRinehartLane R A` (`R3.4`) satisfying `Z(A)`-linearity in `X` and
both left and right Leibniz rules. -/
structure CentralBimoduleConnection {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (K : CentralLieRinehartLane R A) (B : CentralBimodule R A M) where
  nabla : K.lane.L → M → M
  nabla_add_left : ∀ X Y m, nabla (X + Y) m = nabla X m + nabla Y m
  nabla_add_right : ∀ X m n, nabla X (m + n) = nabla X m + nabla X n
  nabla_smul_R : ∀ (r : R) X m, nabla X (r • m) = r • nabla X m
  nabla_central_left : ∀ (z : Subalgebra.center R A) X m,
    nabla (z • X) m = B.lsmul z.1 (nabla X m)
  leibniz_left : ∀ (a : A) X m,
    nabla X (B.lsmul a m) = B.lsmul (K.lane.operatorAction X a) m + B.lsmul a (nabla X m)
  leibniz_right : ∀ X m (b : A),
    nabla X (B.rsmul m b) = B.rsmul (nabla X m) b + B.rsmul m (K.lane.operatorAction X b)

/-- `[S3-10]` Canonical flat central bimodule connection on `A` induced by `K.lane.operatorAction`. -/
def canonicalCentralBimoduleConnection {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : CentralLieRinehartLane R A) :
    CentralBimoduleConnection K (algebraSelfCentralBimodule R A) where
  nabla X a := K.lane.operatorAction X a
  nabla_add_left _ _ _ := by simp
  nabla_add_right _ _ _ := by simp
  nabla_smul_R _ _ _ := by simp
  nabla_central_left z X a := K.act_smul_center z X a
  leibniz_left a X b := K.isLeibniz X a b
  leibniz_right X a b := K.isLeibniz X a b

/-- Constructive T17 witness for `CentralBimoduleConnection` on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def concreteMat2CentralBimoduleConnection :
    CentralBimoduleConnection concreteMat2CentralLieRinehartLane concreteMat2CentralBimodule :=
  canonicalCentralBimoduleConnection concreteMat2CentralLieRinehartLane

/-- `[S3-10]` Dubois-Violette & Michor (1996) §3: Two-sided Leibniz rule
`∇_X(a · m · b) = (X a) · m · b + a · ∇_X(m) · b + a · m · (X b)`. -/
theorem centralBimoduleConnection_leibniz_both {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    {K : CentralLieRinehartLane R A} {B : CentralBimodule R A M}
    (D : CentralBimoduleConnection K B) (X : K.lane.L) (a b : A) (m : M) :
    D.nabla X (B.rsmul (B.lsmul a m) b) =
      B.rsmul (B.lsmul (K.lane.operatorAction X a) m) b +
      B.rsmul (B.lsmul a (D.nabla X m)) b +
      B.rsmul (B.lsmul a m) (K.lane.operatorAction X b) := by
  rw [D.leibniz_right, D.leibniz_left, B.rsmul_add_left]

/-- `[S3-10]` Curvature `R(X, Y) m = ∇_X ∇_Y m - ∇_Y ∇_X m - ∇_{[X, Y]} m` of a central
bimodule connection. -/
def dvCurvature {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    {K : CentralLieRinehartLane R A} {B : CentralBimodule R A M}
    (D : CentralBimoduleConnection K B) (X Y : K.lane.L) (m : M) : M :=
  D.nabla X (D.nabla Y m) - D.nabla Y (D.nabla X m) - D.nabla ⁅X, Y⁆ m

/-- `[S3-10]` Two-sided `A`-bimodule bilinearity of `dvCurvature` in `m`, plus `Z(A)`-linearity in `X`. -/
theorem dvCurvature_bimodule_and_central {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    {K : CentralLieRinehartLane R A} {B : CentralBimodule R A M}
    (D : CentralBimoduleConnection K B) (a b : A) (z : Subalgebra.center R A)
    (X Y : K.lane.L) (m : M) :
    dvCurvature D X Y (B.lsmul a m) = B.lsmul a (dvCurvature D X Y m) ∧
    dvCurvature D X Y (B.rsmul m b) = B.rsmul (dvCurvature D X Y m) b ∧
    dvCurvature D (z • X) Y m = B.lsmul z.1 (dvCurvature D X Y m) := by
  have hnabla_sub_left : ∀ U V n, D.nabla (U - V) n = D.nabla U n - D.nabla V n := by
    intro U V n
    have h := D.nabla_add_left (U - V) V n
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hsub_l : ∀ u v : M, B.lsmul a (u - v) = B.lsmul a u - B.lsmul a v := by
    intro u v
    have h := B.lsmul_add_right a (u - v) v
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hsub_r : ∀ u v : M, B.rsmul (u - v) b = B.rsmul u b - B.rsmul v b := by
    intro u v
    have h := B.rsmul_add_left (u - v) v b
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hsub_z : ∀ u v : M, B.lsmul z.1 (u - v) = B.lsmul z.1 u - B.lsmul z.1 v := by
    intro u v
    have h := B.lsmul_add_right z.1 (u - v) v
    rw [sub_add_cancel] at h
    exact eq_sub_of_add_eq h.symm
  refine ⟨?_, ?_, ?_⟩
  · dsimp [dvCurvature]
    rw [D.leibniz_left a Y m, D.nabla_add_right, D.leibniz_left, D.leibniz_left,
      D.leibniz_left a X m, D.nabla_add_right, D.leibniz_left, D.leibniz_left,
      D.leibniz_left a ⁅X, Y⁆ m, K.lane.operatorAction_commutator_apply X Y a,
      hsub_l, hsub_l]
    have hsub_a : ∀ c d : A, B.lsmul (c - d) m = B.lsmul c m - B.lsmul d m := by
      intro c d
      have h := B.lsmul_add_left (c - d) d m
      rw [sub_add_cancel] at h
      exact eq_sub_of_add_eq h.symm
    rw [hsub_a]
    abel
  · dsimp [dvCurvature]
    rw [D.leibniz_right Y m b, D.nabla_add_right, D.leibniz_right, D.leibniz_right,
      D.leibniz_right X m b, D.nabla_add_right, D.leibniz_right, D.leibniz_right,
      D.leibniz_right ⁅X, Y⁆ m b, K.lane.operatorAction_commutator_apply X Y b,
      hsub_r, hsub_r]
    have hsub_b : ∀ c d : A, B.rsmul m (c - d) = B.rsmul m c - B.rsmul m d := by
      intro c d
      have h := B.rsmul_add_right m (c - d) d
      rw [sub_add_cancel] at h
      exact eq_sub_of_add_eq h.symm
    rw [hsub_b]
    abel
  · dsimp [dvCurvature]
    rw [D.nabla_central_left z X (D.nabla Y m), D.nabla_central_left z X m,
      D.leibniz_left z.1 Y (D.nabla X m), K.bracket_smul_center_left z X Y,
      hnabla_sub_left, D.nabla_central_left z ⁅X, Y⁆ m,
      D.nabla_central_left _ X m, hsub_z, hsub_z]
    abel

/-- `[S3-10]` Dubois-Violette (1999) §8 Matrix Edge Case: For `A := Matrix (Fin n) (Fin n) ℝ`,
every central element `z ∈ Z(A)` is a scalar matrix (`Matrix.center_eq_range`), hence is
annihilated by every `ℝ`-derivation `D : NonAssocDerivation.derivations ℝ A`. -/
theorem matrix_center_killed_by_derivations (n : ℕ)
    (D : NonAssocDerivation.derivations ℝ (Matrix (Fin n) (Fin n) ℝ))
    {z : Matrix (Fin n) (Fin n) ℝ}
    (hz : z ∈ Subalgebra.center ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    (D : Module.End ℝ (Matrix (Fin n) (Fin n) ℝ)) z = 0 := by
  have hz_mem : z ∈ Set.center (Matrix (Fin n) (Fin n) ℝ) := hz
  rw [Matrix.center_eq_range] at hz_mem
  obtain ⟨r, rfl⟩ := hz_mem
  have h1 : (D : Module.End ℝ (Matrix (Fin n) (Fin n) ℝ)) (1 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
    MaurerCartanTower.lieAction_operatorAction_one
      (fullDerivationLieLane ℝ (Matrix (Fin n) (Fin n) ℝ)).toLieActionLane
      (fullDerivationLieLane ℝ (Matrix (Fin n) (Fin n) ℝ)).isLeibnizAction D
  have hsc : Matrix.scalar (Fin n) r = r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  rw [hsc, map_smul, h1, smul_zero]

end InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary

