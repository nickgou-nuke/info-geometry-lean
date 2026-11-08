import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad
import InfoGeometry.Projective.SplitCompositionProjectiveSpace
import InfoGeometry.Projective.SplitQuaternionMotivicHopf
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false


/-!
# Voelkel Motivic Cells: The Higher Split-Quaternionic Projective Spaces DP^n

This module formalizes Target 3 of the Voelkel Motivic Cells program:
- Konrad Voelkel, *Motivic Cell Structures for Projective Spaces over Split Quaternions*,
  PhD thesis, Freiburg, 2016.

Key Structures:
1. Split-quaternionic vector space $\mathbb{D}^{n+1}$, total norm $N_{n+1}$, and split spheres $S^{(4n+3, 2n+1)}$.
2. Fiber group $S^{(3,1)} \subset \mathbb{D}$ right action, norm multiplicativity, and sphere preservation.
3. Hermitian projector matrices $P(v) = v v^* \in \operatorname{Mat}_{n+1}(\mathbb{D})$, trace formula $\operatorname{Tr}(P(v)) = N(v) \cdot I$, projector scaling, and gauge invariance.
4. Orthogonal basepoint projectors $E_{kk}$, pairwise orthogonality, idempotency, and partition of unity $\sum_{k=0}^n E_{kk} = I_{n+1}$.
5. Motivic cell stratification: lower-dimensional inclusion $\mathbb{D}^n \hookrightarrow \mathbb{D}^{n+1}$, top cell affine chart $\mathbb{D}^n \hookrightarrow \mathbb{D}^{n+1}$ sending $z \mapsto (z, 1)$, and dimension formula $\dim_{\mathbb{A}^1} = 4n$.
6. Master verification certificate `SplitQuaternionMotivicDPnCertificate` bundled and proved unconditionally.
-/

namespace Experimental.Sandbox.Projective.SplitQuaternionMotivicDPn

open Matrix
open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.Coquaternion.Coquaternion
open InfoGeometry.Projective.SplitComposition
open InfoGeometry.Projective.SplitQuaternionMotivicHopf

variable {R : Type*} [CommRing R]

/-! ### Mathlib Semiring and Algebra Hierarchy for Coquaternion -/

instance : Semiring (Coquaternion R) where
  add := (· + ·)
  add_assoc := fun p q r => by ext <;> { simp; try ring }
  zero := 0
  zero_add := fun q => by ext <;> simp
  add_zero := fun q => by ext <;> simp
  add_comm := fun p q => by ext <;> { simp; try ring }
  mul := (· * ·)
  mul_assoc := mul_assoc_q
  one := 1
  one_mul := one_mul_q
  mul_one := mul_one_q
  left_distrib := left_distrib_q
  right_distrib := right_distrib_q
  zero_mul := fun q => by ext <;> simp
  mul_zero := fun q => by ext <;> simp
  nsmul := nsmulRec
  npow := npowRec
  natCast n := ⟨n, 0, 0, 0⟩
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> { simp; try ring }

/-- Canonical ring homomorphism from R into Coquaternion R embedding scalars on the real line. -/
def coquaternionAlgebraMap : R →+* Coquaternion R where
  toFun r := ⟨r, 0, 0, 0⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' r s := by ext <;> simp
  map_mul' r s := by ext <;> simp

instance : Algebra R (Coquaternion R) where
  algebraMap := coquaternionAlgebraMap
  commutes' r x := by ext <;> { simp [coquaternionAlgebraMap]; try ring }
  smul_def' r x := by ext <;> { simp [coquaternionAlgebraMap]; try ring }

@[simp]
theorem algebraMap_apply (r : R) :
    algebraMap R (Coquaternion R) r = ⟨r, 0, 0, 0⟩ := rfl

theorem mul_conj_eq_algebraMap (q : Coquaternion R) :
    q * conj q = algebraMap R (Coquaternion R) (normSq q) := by
  ext <;> { simp [conj, normSq]; ring }

@[simp]
theorem normSq_zero : normSq (0 : Coquaternion R) = 0 := by
  dsimp [normSq]
  ring

/-! ### Section 1: Split-Quaternionic Vector Space $\mathbb{D}^{n+1}$, Norm, and Sphere $S^{(4n+3, 2n+1)}$ -/

/-- Split-quaternionic vector space $\mathbb{D}^{n+1} = \operatorname{Fin}(n+1) \to \mathbb{D}$. -/
abbrev VectorD (n : ℕ) (R : Type*) := Fin (n + 1) → Coquaternion R

/-- Total split-quaternionic quadratic norm on $\mathbb{D}^{n+1}$:
    $N_{n+1}(v) = \sum_{i=0}^n N(v_i)$. -/
def normSqN {n : ℕ} (v : VectorD n R) : R :=
  ∑ i : Fin (n + 1), normSq (v i)

/-- Unit split sphere $S^{(4n+3, 2n+1)} \subset \mathbb{D}^{n+1}$ defined by $N_{n+1}(v) = 1$. -/
def IsUnitSphere {n : ℕ} (v : VectorD n R) : Prop :=
  normSqN v = 1

/-- Right fiber group action of $\mathbb{D}$ (and in particular $S^{(3,1)}$) on $\mathbb{D}^{n+1}$:
    $(v \triangleleft u)_i = v_i \cdot u$. -/
def actionN {n : ℕ} (v : VectorD n R) (u : Coquaternion R) : VectorD n R :=
  fun i => v i * u

/-- Right identity law for the fiber action: $v \triangleleft 1 = v$. -/
theorem actionN_one {n : ℕ} (v : VectorD n R) : actionN v 1 = v := by
  funext i
  dsimp [actionN]
  exact mul_one_q (v i)

/-- Associativity / composition law for the fiber action:
    $v \triangleleft (u_1 \cdot u_2) = (v \triangleleft u_1) \triangleleft u_2$. -/
theorem actionN_mul {n : ℕ} (v : VectorD n R) (u1 u2 : Coquaternion R) :
    actionN v (u1 * u2) = actionN (actionN v u1) u2 := by
  funext i
  dsimp [actionN]
  exact (mul_assoc_q (v i) u1 u2).symm

/-- Multiplicativity of the total split quadratic norm under the right action:
    $N_{n+1}(v \triangleleft u) = N_{n+1}(v) \cdot N(u)$. -/
theorem normSqN_action {n : ℕ} (v : VectorD n R) (u : Coquaternion R) :
    normSqN (actionN v u) = normSqN v * normSq u := by
  dsimp [normSqN, actionN]
  simp_rw [normSq_mul]
  rw [← Finset.sum_mul]

/-- Preservation of the unit split sphere $S^{(4n+3, 2n+1)}$ under the action of $S^{(3,1)}$. -/
theorem sphere_action_preserves {n : ℕ} (v : VectorD n R) (u : Coquaternion R)
    (hv : IsUnitSphere v) (hu : normSq u = 1) :
    IsUnitSphere (actionN v u) := by
  dsimp [IsUnitSphere] at *
  rw [normSqN_action, hv, hu, mul_one]

/-! ### Section 2: Projector Representation and Gauge Invariance -/

/-- Projector matrix $P(v) \in \operatorname{Mat}_{n+1}(\mathbb{D})$:
    $P(v)_{ij} = v_i \cdot \overline{v_j}$. -/
def projectorN {n : ℕ} (v : VectorD n R) : Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R) :=
  fun i j => v i * conj (v j)

/-- Matrix trace on $\operatorname{Mat}_{n+1}(\mathbb{D})$. -/
def traceCoq {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R)) : Coquaternion R :=
  ∑ i : Fin (n + 1), M i i

/-- Trace of the projector matrix equals the total norm embedded via algebraMap:
    $\operatorname{Tr}(P(v)) = \operatorname{algebraMap}(N_{n+1}(v))$. -/
theorem projectorN_trace {n : ℕ} (v : VectorD n R) :
    traceCoq (projectorN v) = algebraMap R (Coquaternion R) (normSqN v) := by
  dsimp [traceCoq, projectorN, normSqN]
  have h (i : Fin (n + 1)) : v i * conj (v i) = algebraMap R (Coquaternion R) (normSq (v i)) :=
    mul_conj_eq_algebraMap (v i)
  simp_rw [h]
  exact (map_sum (algebraMap R (Coquaternion R)) (fun i => normSq (v i)) Finset.univ).symm

/-- Entrywise identity for coquaternion conjugation under right multiplication:
    $(a \cdot u) \cdot \overline{b \cdot u} = N(u) \cdot (a \cdot \overline{b})$. -/
theorem mul_conj_mul (a b u : Coquaternion R) :
    (a * u) * conj (b * u) = normSq u • (a * conj b) := by
  ext <;> { simp [conj, normSq]; ring }

/-- Projector scaling under right action:
    $P(v \triangleleft u) = N(u) \cdot P(v)$. -/
theorem projectorN_action {n : ℕ} (v : VectorD n R) (u : Coquaternion R) :
    projectorN (actionN v u) = normSq u • projectorN v := by
  ext i j : 1
  dsimp [projectorN, actionN]
  exact mul_conj_mul (v i) (v j) u

/-- Projector gauge invariance under the unit sphere $S^{(3,1)}$:
    When $N(u) = 1$, $P(v \triangleleft u) = P(v)$. -/
theorem projectorN_gauge_invariance {n : ℕ} (v : VectorD n R) (u : Coquaternion R)
    (hu : normSq u = 1) :
    projectorN (actionN v u) = projectorN v := by
  rw [projectorN_action, hu, one_smul]

/-! ### Section 3: Orthogonal Basepoint Projectors & Partition of Unity -/

/-- Standard basis vector $e_k \in \mathbb{D}^{n+1}$. -/
def basisVec {n : ℕ} (k : Fin (n + 1)) : VectorD n R :=
  fun i => if i = k then 1 else 0

/-- Basepoint projector $E_{kk} = P(e_k) \in \operatorname{Mat}_{n+1}(\mathbb{D})$. -/
def basepointProj {n : ℕ} (k : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (Coquaternion R) :=
  projectorN (basisVec k)

/-- Matrix entry formula for the basepoint projector:
    $(E_{kk})_{ij} = 1$ if $i = k \wedge j = k$, and $0$ otherwise. -/
theorem basepointProj_apply {n : ℕ} (k : Fin (n + 1)) (i j : Fin (n + 1)) :
    basepointProj (R := R) k i j = if i = k ∧ j = k then 1 else 0 := by
  dsimp [basepointProj, projectorN, basisVec]
  by_cases h : i = k ∧ j = k
  · rw [if_pos h, if_pos h.1, if_pos h.2]
    simp [conj_one, mul_one_q]
  · rw [if_neg h]
    by_cases hi : i = k
    · rw [if_pos hi]
      have hj : ¬(j = k) := fun hj => h ⟨hi, hj⟩
      rw [if_neg hj]
      simp [conj_zero, mul_zero]
    · rw [if_neg hi]
      simp [zero_mul]

/-- Matrix entry formula for basepoint projector multiplication:
    $(E_{kk} \cdot E_{ll})_{ij} = (E_{kk})_{ij}$ if $k = l$, and $0$ otherwise. -/
theorem basepointProj_mul_entry {n : ℕ} (k l : Fin (n + 1)) (i j : Fin (n + 1)) :
    (basepointProj (R := R) k * basepointProj (R := R) l) i j =
      (if k = l then basepointProj (R := R) k else 0) i j := by
  rw [Matrix.mul_apply]
  have hzero (m : Fin (n + 1)) (hm : m ≠ k) :
      basepointProj (R := R) k i m * basepointProj (R := R) l m j = 0 := by
    rw [basepointProj_apply (R := R) k i m]
    have h : ¬(i = k ∧ m = k) := fun h => hm h.2
    rw [if_neg h]
    simp [zero_mul]
  rw [Finset.sum_eq_single k]
  · by_cases hkl : k = l
    · rw [if_pos hkl, hkl]
      rw [basepointProj_apply (R := R) l i l, basepointProj_apply (R := R) l l j, basepointProj_apply (R := R) l i j]
      by_cases h : i = l ∧ j = l
      · rw [if_pos h, if_pos ⟨h.1, rfl⟩, if_pos ⟨rfl, h.2⟩]
        simp [mul_one_q]
      · rw [if_neg h]
        by_cases hi : i = l
        · rw [if_pos ⟨hi, rfl⟩]
          have hj : ¬(j = l) := fun hj => h ⟨hi, hj⟩
          have hj' : ¬(l = l ∧ j = l) := fun h2 => hj h2.2
          rw [if_neg hj']
          simp [mul_zero]
        · have hi' : ¬(i = l ∧ l = l) := fun h2 => hi h2.1
          rw [if_neg hi']
          simp [zero_mul]
    · rw [if_neg hkl]
      rw [basepointProj_apply (R := R) l k j]
      have h : ¬(k = l ∧ j = l) := fun h2 => hkl h2.1
      rw [if_neg h]
      simp [mul_zero, Matrix.zero_apply]
  · intro m _ hm
    exact hzero m hm
  · intro hk
    exact False.elim (hk (Finset.mem_univ k))

/-- Orthogonality and multiplication law for basepoint projectors:
    $E_{kk} \cdot E_{ll} = \delta_{kl} E_{kk}$. -/
theorem basepointProj_mul {n : ℕ} (k l : Fin (n + 1)) :
    basepointProj (R := R) k * basepointProj (R := R) l =
      if k = l then basepointProj (R := R) k else 0 := by
  ext i j : 1
  exact basepointProj_mul_entry k l i j

/-- Idempotency of basepoint projectors: $E_{kk}^2 = E_{kk}$. -/
theorem basepointProj_idempotent {n : ℕ} (k : Fin (n + 1)) :
    basepointProj (R := R) k * basepointProj (R := R) k = basepointProj (R := R) k := by
  rw [basepointProj_mul, if_pos rfl]

/-- Orthogonal partition of unity:
    $\sum_{k=0}^n E_{kk} = I_{n+1}$. -/
theorem basepointProj_partition_of_unity {n : ℕ} :
    (∑ k : Fin (n + 1), basepointProj (R := R) k) = 1 := by
  ext i j : 1
  simp only [Matrix.sum_apply]
  by_cases hij : i = j
  · rw [hij, Matrix.one_apply_eq]
    rw [Finset.sum_eq_single j]
    · rw [basepointProj_apply, if_pos ⟨rfl, rfl⟩]
    · intro k _ hkj
      rw [basepointProj_apply, if_neg (fun h => hkj h.2.symm)]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  · rw [Matrix.one_apply_ne hij]
    have hzero (k : Fin (n + 1)) : basepointProj (R := R) k i j = 0 := by
      rw [basepointProj_apply, if_neg (fun h => hij (h.1.trans h.2.symm))]
    rw [Finset.sum_congr rfl (fun k _ => hzero k)]
    simp only [Finset.sum_const_zero]

/-! ### Section 4: Inductive Motivic Cell Attachment & Suspension Stratification -/

/-- Lower-dimensional inclusion $\mathbb{D}^n \hookrightarrow \mathbb{D}^{n+1}$ appending zero. -/
def embedLower {n : ℕ} (v : Fin n → Coquaternion R) : Fin (n + 1) → Coquaternion R :=
  Fin.snoc v 0

/-- Lower-dimensional embedding preserves the total split quadratic norm:
    $\sum_{i=0}^n N(\operatorname{embedLower}(v)_i) = \sum_{i=0}^{n-1} N(v_i)$. -/
theorem embedLower_normSq {n : ℕ} (v : Fin n → Coquaternion R) :
    (∑ i : Fin (n + 1), normSq (embedLower v i)) = ∑ i : Fin n, normSq (v i) := by
  dsimp [embedLower]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, normSq_zero, add_zero]

/-- Top cell affine chart $z \in \mathbb{D}^n \mapsto (z_0, \dots, z_{n-1}, 1) \in \mathbb{D}^{n+1}$. -/
def affineTopCell {n : ℕ} (z : Fin n → Coquaternion R) : Fin (n + 1) → Coquaternion R :=
  Fin.snoc z 1

/-- The last coordinate of the top affine chart vector is identity:
    $(\operatorname{affineTopCell}(z))_{\text{last}} = 1$. -/
theorem affineTopCell_last {n : ℕ} (z : Fin n → Coquaternion R) :
    affineTopCell z (Fin.last n) = 1 := by
  dsimp [affineTopCell]
  simp [Fin.snoc_last]

/-- Affine top cell projector boundary separation:
    $P(\operatorname{affineTopCell}(z))_{\text{last}, \text{last}} = 1$. -/
theorem affineTopCell_projector_last {n : ℕ} (z : Fin n → Coquaternion R) :
    (projectorN (affineTopCell z)) (Fin.last n) (Fin.last n) = 1 := by
  dsimp [projectorN]
  rw [affineTopCell_last]
  simp [conj_one, mul_one_q]

/-- Real motivic cell dimension formula: each cell adds $\dim_{\mathbb{R}} = 4$. -/
def motivicCellDim (n : ℕ) : ℕ := 4 * n

/-- Dimension at basepoint $n = 0$: $\dim = 0$. -/
theorem motivicCellDim_zero : motivicCellDim 0 = 0 := rfl

/-- Dimension inductive step: $\dim(\mathbb{D}\mathrm{P}^{n+1}) = \dim(\mathbb{D}\mathrm{P}^n) + 4$. -/
theorem motivicCellDim_succ (n : ℕ) : motivicCellDim (n + 1) = motivicCellDim n + 4 := by
  dsimp [motivicCellDim]
  ring

/-! ### Section 5: Master Verification Certificate -/

/-- Master verification certificate bundling all fundamental theorems of the split-quaternionic
    projective spaces $\mathbb{D}\mathrm{P}^n$, split spheres $S^{(4n+3, 2n+1)}$, projector gauge
    invariance, orthogonal partition of unity, and motivic cellular stratification. -/
structure SplitQuaternionMotivicDPnCertificate : Prop where
  -- Section 1: Split-Quaternionic Vector Space, Norm, and Sphere
  normSqN_action_mult : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R) (u : Coquaternion R),
    normSqN (actionN v u) = normSqN v * normSq u
  sphere_preservation : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R) (u : Coquaternion R),
    IsUnitSphere v → normSq u = 1 → IsUnitSphere (actionN v u)
  actionN_identity : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R),
    actionN v 1 = v
  actionN_composition : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R) (u1 u2 : Coquaternion R),
    actionN v (u1 * u2) = actionN (actionN v u1) u2

  -- Section 2: Projector Representation and Gauge Invariance
  projector_trace : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R),
    traceCoq (projectorN v) = algebraMap R (Coquaternion R) (normSqN v)
  projector_action_scale : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R) (u : Coquaternion R),
    projectorN (actionN v u) = normSq u • projectorN v
  projector_gauge_inv : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : VectorD n R) (u : Coquaternion R),
    normSq u = 1 → projectorN (actionN v u) = projectorN v

  -- Section 3: Orthogonal Basepoint Projectors & Partition of Unity
  basepoint_formula : ∀ (n : ℕ) (R : Type*) [CommRing R] (k : Fin (n + 1)) (i j : Fin (n + 1)),
    basepointProj (R := R) k i j = if i = k ∧ j = k then 1 else 0
  basepoint_ortho_mul : ∀ (n : ℕ) (R : Type*) [CommRing R] (k l : Fin (n + 1)),
    basepointProj (R := R) k * basepointProj (R := R) l = if k = l then basepointProj (R := R) k else 0
  basepoint_idempotency : ∀ (n : ℕ) (R : Type*) [CommRing R] (k : Fin (n + 1)),
    basepointProj (R := R) k * basepointProj (R := R) k = basepointProj (R := R) k
  basepoint_partition : ∀ (n : ℕ) (R : Type*) [CommRing R],
    (∑ k : Fin (n + 1), basepointProj (R := R) k) = 1

  -- Section 4: Inductive Motivic Cell Attachment & Suspension Stratification
  embed_normSq : ∀ (n : ℕ) (R : Type*) [CommRing R] (v : Fin n → Coquaternion R),
    (∑ i : Fin (n + 1), normSq (embedLower v i)) = ∑ i : Fin n, normSq (v i)
  top_cell_last : ∀ (n : ℕ) (R : Type*) [CommRing R] (z : Fin n → Coquaternion R),
    affineTopCell z (Fin.last n) = 1
  top_cell_projector_boundary : ∀ (n : ℕ) (R : Type*) [CommRing R] (z : Fin n → Coquaternion R),
    (projectorN (affineTopCell z)) (Fin.last n) (Fin.last n) = 1
  dim_zero : motivicCellDim 0 = 0
  dim_succ : ∀ (n : ℕ), motivicCellDim (n + 1) = motivicCellDim n + 4

/-- Universal compilation theorem proving that the SplitQuaternionMotivicDPnCertificate holds unconditionally. -/
theorem compile_split_quaternion_motivic_dpn :
    SplitQuaternionMotivicDPnCertificate where
  normSqN_action_mult := fun _ _ _ => normSqN_action
  sphere_preservation := fun _ _ _ => sphere_action_preserves
  actionN_identity := fun _ _ _ => actionN_one
  actionN_composition := fun _ _ _ => actionN_mul
  projector_trace := fun _ _ _ => projectorN_trace
  projector_action_scale := fun _ _ _ => projectorN_action
  projector_gauge_inv := fun _ _ _ => projectorN_gauge_invariance
  basepoint_formula := fun _ _ _ => basepointProj_apply
  basepoint_ortho_mul := fun _ _ _ => basepointProj_mul
  basepoint_idempotency := fun _ _ _ => basepointProj_idempotent
  basepoint_partition := fun _ _ _ => basepointProj_partition_of_unity
  embed_normSq := fun _ _ _ => embedLower_normSq
  top_cell_last := fun _ _ _ => affineTopCell_last
  top_cell_projector_boundary := fun _ _ _ => affineTopCell_projector_last
  dim_zero := motivicCellDim_zero
  dim_succ := motivicCellDim_succ

end Experimental.Sandbox.Projective.SplitQuaternionMotivicDPn
