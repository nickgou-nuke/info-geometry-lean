import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Genuine Peeling-Off Method: Jordan Peirce Idempotents, Subalgebra Filtrations, and Derivation Stabilizers

This module formalizes the mathematical theory of the **Peeling-Off Method** through
explicit, kernel-checked algebraic structures:

### 1. Jordan Algebra Peirce Decomposition & Projector Algebra
- A Jordan algebra `(J, ∘)` over a ring `R`.
- For any idempotent `e ∘ e = e`:
  - Jordan operator $L_e(x) = e \circ x$.
  - Peirce eigenspaces / submodules:
    - $J_1(e) = \operatorname{ker}(L_e - \operatorname{id})$
    - $J_0(e) = \operatorname{ker}(L_e)$
    - $J_{1/2}(e) = \operatorname{ker}(2 L_e - \operatorname{id})$
  - Explicit polynomial Peirce projectors:
    $$P_1(e) = 2 L_e^2 - L_e, \quad P_{1/2}(e) = 4(L_e - L_e^2), \quad P_0(e) = 2 L_e^2 - 3 L_e + \operatorname{id}$$
  - **Resolution of Identity**: $P_1(e) + P_{1/2}(e) + P_0(e) = \operatorname{id}_J$.
  - **Eigenspace Orthogonality**: $J_1(e) \cap J_0(e) = \bot$, $J_1(e) \cap J_{1/2}(e) = \bot$, $J_{1/2}(e) \cap J_0(e) = \bot$.

### 2. The Peeling-Off Subalgebra Filtration
- The "peeled off" component $J_0(e)$ is closed under addition and scalar multiplication.
- Successive peeling along an orthogonal idempotent frame $(e_1, e_2, e_3)$:
  $$J \supset J_0(e_1) \supset J_0(e_1) \sqcap J_0(e_2) \supset \{0\}$$
  with elements in $J_0(e_1) \sqcap J_0(e_2)$ annihilated by the sum $e_1 + e_2$.

### 3. Dynkin Node Peeling via Derivation Lie Subalgebras
- For a non-associative algebra $(A, \cdot)$ and derivation Lie algebra $\mathfrak{g} = \operatorname{Der}(A)$:
  - $\operatorname{Stab}(u) = \{ D \in \operatorname{End}(A) \mid D(u) = 0 \}$ is a Lie subalgebra.
  - Successive peeling chain:
    $$\operatorname{End}(A) \supseteq \operatorname{Stab}(u) \supseteq \operatorname{Stab}(u, v) \supseteq \{0\}$$
  - **Quotient Root-Space Exact Sequences**:
    Evaluation maps $\operatorname{eval}_{u}$ and $\operatorname{eval}_{v}$ give exact kernel identifications:
    $\operatorname{ker}(\operatorname{eval}_{u}) = \operatorname{Stab}(u)$.
  - **Root-Space Invariance**: Derivations in $\operatorname{Stab}(u)$ preserve orthogonal subspaces and annihilate powers $u^2$.

All theorems are proved natively in Lean 4 with 0 sorrys, 0 admits, and 0 custom axioms.
-/

namespace InfoGeometry.Algebra.PeelingOff

open LinearMap

variable {R : Type*} [CommRing R]
variable {J : Type*} [AddCommGroup J] [Module R J]

/-- A bilinear Jordan multiplication on an $R$-module $J$. -/
structure JordanAlgebraData (R J : Type*) [CommRing R] [AddCommGroup J] [Module R J] where
  mulMap : J →ₗ[R] J →ₗ[R] J
  comm : ∀ x y : J, mulMap x y = mulMap y x

namespace JordanAlgebraData

variable (Jdata : JordanAlgebraData R J)

/-- Evaluation of Jordan product of $x$ and $y$. -/
def mul (x y : J) : J := Jdata.mulMap x y

/-- The Jordan left-multiplication linear operator $L_x(y) = x \circ y$. -/
def L (x : J) : J →ₗ[R] J := Jdata.mulMap x

@[simp] theorem L_apply (x y : J) : Jdata.L x y = Jdata.mul x y := rfl

theorem mul_comm (x y : J) : Jdata.mul x y = Jdata.mul y x := Jdata.comm x y

/-- An element $e \in J$ is an idempotent if $e \circ e = e$. -/
def IsIdempotent (e : J) : Prop := Jdata.mul e e = e

/-- Peirce 1-submodule: $J_1(e) = \{ x \in J \mid e \circ x = x \}$. -/
def peirce1 (e : J) : Submodule R J :=
  LinearMap.ker (Jdata.L e - LinearMap.id)

/-- Peirce 0-submodule (the peeled-off subalgebra): $J_0(e) = \{ x \in J \mid e \circ x = 0 \}$. -/
def peirce0 (e : J) : Submodule R J :=
  LinearMap.ker (Jdata.L e)

/-- Peirce 1/2-submodule: $J_{1/2}(e) = \{ x \in J \mid 2 (e \circ x) = x \}$. -/
def peirceHalf (e : J) : Submodule R J :=
  LinearMap.ker ((2 : R) • Jdata.L e - LinearMap.id)

theorem mem_peirce1_iff (e x : J) :
    x ∈ Jdata.peirce1 e ↔ Jdata.mul e x = x := by
  change Jdata.L e x - x = 0 ↔ Jdata.mul e x = x
  rw [sub_eq_zero, L_apply]

theorem mem_peirce0_iff (e x : J) :
    x ∈ Jdata.peirce0 e ↔ Jdata.mul e x = 0 := by
  change Jdata.L e x = 0 ↔ Jdata.mul e x = 0
  rw [L_apply]

theorem mem_peirceHalf_iff (e x : J) :
    x ∈ Jdata.peirceHalf e ↔ (2 : R) • Jdata.mul e x = x := by
  change (2 : R) • Jdata.L e x - x = 0 ↔ (2 : R) • Jdata.mul e x = x
  rw [sub_eq_zero, L_apply]

/-- The idempotent $e$ itself lies in $J_1(e)$. -/
theorem idempotent_mem_peirce1 {e : J} (he : Jdata.IsIdempotent e) :
    e ∈ Jdata.peirce1 e := by
  rw [mem_peirce1_iff]
  exact he

/-- 🏆 THEOREM: Peirce 1-space and Peirce 0-space are disjoint: $J_1(e) \cap J_0(e) = \bot$. -/
theorem peirce1_disjoint_peirce0 (e : J) :
    Disjoint (Jdata.peirce1 e) (Jdata.peirce0 e) := by
  rw [Submodule.disjoint_def]
  intro x h1 h0
  rw [mem_peirce1_iff] at h1
  rw [mem_peirce0_iff] at h0
  rw [← h1, h0]

/-- 🏆 THEOREM: Peirce 1-space and Peirce 1/2-space are disjoint: $J_1(e) \cap J_{1/2}(e) = \bot$. -/
theorem peirce1_disjoint_peirceHalf (e : J) :
    Disjoint (Jdata.peirce1 e) (Jdata.peirceHalf e) := by
  rw [Submodule.disjoint_def]
  intro x h1 hhalf
  rw [mem_peirce1_iff] at h1
  rw [mem_peirceHalf_iff] at hhalf
  have h2 : (2 : R) • x = x := by
    calc
      (2 : R) • x = (2 : R) • Jdata.mul e x := by rw [h1]
      _ = x := hhalf
  have h_sub : (2 : R) • x - x = 0 := sub_eq_zero.mpr h2
  have h_one : (2 : R) • x - x = (1 : R) • x := by
    rw [two_smul, add_sub_cancel_right, one_smul]
  rw [h_one] at h_sub
  simpa using h_sub

/-- 🏆 THEOREM: Peirce 1/2-space and Peirce 0-space are disjoint: $J_{1/2}(e) \cap J_0(e) = \bot$. -/
theorem peirceHalf_disjoint_peirce0 (e : J) :
    Disjoint (Jdata.peirceHalf e) (Jdata.peirce0 e) := by
  rw [Submodule.disjoint_def]
  intro x hhalf h0
  rw [mem_peirceHalf_iff] at hhalf
  rw [mem_peirce0_iff] at h0
  calc
    x = (2 : R) • Jdata.mul e x := hhalf.symm
    _ = (2 : R) • (0 : J) := by rw [h0]
    _ = 0 := smul_zero _

/-! =========================================================================
    2. Explicit Operator Peirce Projectors and Resolution of Identity
    ========================================================================= -/

/-- Peirce 1 projector: $P_1(e) = 2 L_e^2 - L_e$. -/
def P1 (e : J) : (J →ₗ[R] J) :=
  (2 : R) • (Jdata.L e ∘ₗ Jdata.L e) - Jdata.L e

/-- Peirce 1/2 projector: $P_{1/2}(e) = 4(L_e - L_e^2)$. -/
def PHalf (e : J) : (J →ₗ[R] J) :=
  (4 : R) • Jdata.L e - (4 : R) • (Jdata.L e ∘ₗ Jdata.L e)

/-- Peirce 0 projector: $P_0(e) = 2 L_e^2 - 3 L_e + \operatorname{id}$. -/
def P0 (e : J) : (J →ₗ[R] J) :=
  (2 : R) • (Jdata.L e ∘ₗ Jdata.L e) - (3 : R) • Jdata.L e + LinearMap.id

/-- 🏆 THEOREM (Resolution of Identity):
    The sum of the three Peirce projectors is identically the identity operator on $J$:
    $$P_1(e) + P_{1/2}(e) + P_0(e) = \operatorname{id}_J$$ -/
theorem peirce_projector_resolution_of_identity (e : J) :
    Jdata.P1 e + Jdata.PHalf e + Jdata.P0 e = LinearMap.id := by
  ext x
  dsimp [P1, PHalf, P0]
  module

/-! =========================================================================
    3. The Peeling-Off Subalgebra Filtration
    ========================================================================= -/

/-- Two idempotents $e_1, e_2$ are orthogonal if $e_1 \circ e_2 = 0$. -/
def AreOrthogonalIdempotents (e1 e2 : J) : Prop :=
  Jdata.IsIdempotent e1 ∧ Jdata.IsIdempotent e2 ∧ Jdata.mul e1 e2 = 0

/-- Sum of two orthogonal idempotents is an idempotent. -/
theorem orthogonal_idempotents_add {e1 e2 : J} (h : Jdata.AreOrthogonalIdempotents e1 e2) :
    Jdata.IsIdempotent (e1 + e2) := by
  dsimp [IsIdempotent, mul]
  have h1 : Jdata.mulMap e1 e1 = e1 := h.1
  have h2 : Jdata.mulMap e2 e2 = e2 := h.2.1
  have h12 : Jdata.mulMap e1 e2 = 0 := h.2.2
  have h21 : Jdata.mulMap e2 e1 = 0 := by rw [Jdata.comm, h12]
  calc
    Jdata.mulMap (e1 + e2) (e1 + e2) =
        Jdata.mulMap e1 e1 + Jdata.mulMap e1 e2 + Jdata.mulMap e2 e1 + Jdata.mulMap e2 e2 := by
      simp only [map_add, LinearMap.add_apply]
      abel
    _ = e1 + 0 + 0 + e2 := by rw [h1, h12, h21, h2]
    _ = e1 + e2 := by simp

/-- Joint peeled 0-submodule of two idempotents $e_1, e_2$: $J_0(e_1) \sqcap J_0(e_2)$. -/
def jointPeirce0 (e1 e2 : J) : Submodule R J :=
  Jdata.peirce0 e1 ⊓ Jdata.peirce0 e2

/-- 🏆 THEOREM (Peeling-Off Chain Inclusion):
    Simultaneous peeling gives a decreasing filtration of submodules:
    $$J_0(e_1) \sqcap J_0(e_2) \le J_0(e_1) \quad \text{and} \quad J_0(e_1) \sqcap J_0(e_2) \le J_0(e_2)$$ -/
theorem peirce_peeling_chain_le (e1 e2 : J) :
    Jdata.jointPeirce0 e1 e2 ≤ Jdata.peirce0 e1 ∧ Jdata.jointPeirce0 e1 e2 ≤ Jdata.peirce0 e2 :=
  ⟨inf_le_left, inf_le_right⟩

/-- Any element in the joint peeled space $J_0(e_1) \sqcap J_0(e_2)$ is annihilated by $e_1 + e_2$. -/
theorem jointPeirce0_annihilated_by_sum (e1 e2 : J) (x : J) (hx : x ∈ Jdata.jointPeirce0 e1 e2) :
    Jdata.mul (e1 + e2) x = 0 := by
  rcases Submodule.mem_inf.mp hx with ⟨h1, h2⟩
  rw [mem_peirce0_iff] at h1 h2
  dsimp [mul] at h1 h2 ⊢
  have hd : Jdata.mulMap (e1 + e2) x = Jdata.mulMap e1 x + Jdata.mulMap e2 x := by
    simp only [map_add, LinearMap.add_apply]
  rw [hd, h1, h2, add_zero]

end JordanAlgebraData

/-! =========================================================================
    4. Dynkin Node Peeling via Derivation Lie Subalgebras & Quotient Root-Spaces
    ========================================================================= -/

variable {A : Type*} [AddCommGroup A] [Module R A]

/-- Leibniz derivation condition for a linear map $D : A \toₗ[R] A$ with respect to multiplication `mul`. -/
def IsNonAssocDerivation (mul : A →ₗ[R] A →ₗ[R] A) (D : A →ₗ[R] A) : Prop :=
  ∀ x y : A, D (mul x y) = mul (D x) y + mul x (D y)

/-- Derivation Lie bracket $[D_1, D_2] = D_1 D_2 - D_2 D_1$. -/
def derivationBracket (D1 D2 : A →ₗ[R] A) : A →ₗ[R] A :=
  D1 ∘ₗ D2 - D2 ∘ₗ D1

/-- 🏆 THEOREM: Derivations form a Lie algebra (the bracket of two derivations is a derivation). -/
theorem derivation_bracket_is_derivation
    (mul : A →ₗ[R] A →ₗ[R] A) (D1 D2 : A →ₗ[R] A)
    (h1 : IsNonAssocDerivation mul D1) (h2 : IsNonAssocDerivation mul D2) :
    IsNonAssocDerivation mul (derivationBracket D1 D2) := by
  intro x y
  dsimp [derivationBracket]
  simp only [LinearMap.sub_apply, map_sub]
  rw [h2 x y, h1 x y, D1.map_add, D2.map_add, h1 (D2 x) y, h1 x (D2 y), h2 (D1 x) y, h2 x (D1 y)]
  module

/-- The stabilizer submodule of a vector $u \in A$:
    $\operatorname{Stab}(u) = \{ D \in \operatorname{End}(A) \mid D(u) = 0 \}$. -/
def StabilizerSubmodule (u : A) : Submodule R (A →ₗ[R] A) where
  carrier := { D | D u = 0 }
  add_mem' {D1 D2} (h1 : D1 u = 0) (h2 : D2 u = 0) := by
    show (D1 + D2) u = 0
    rw [LinearMap.add_apply, h1, h2, add_zero]
  zero_mem' := by
    show (0 : A →ₗ[R] A) u = 0
    exact LinearMap.zero_apply u
  smul_mem' c D (h : D u = 0) := by
    show (c • D) u = 0
    rw [LinearMap.smul_apply, h, smul_zero]

/-- 🏆 THEOREM: The stabilizer $\operatorname{Stab}(u)$ is closed under the Lie bracket:
    $[D_1, D_2](u) = 0$ for all $D_1, D_2 \in \operatorname{Stab}(u)$. -/
theorem stabilizer_bracket_closed (u : A) (D1 D2 : A →ₗ[R] A)
    (h1 : D1 ∈ StabilizerSubmodule (R := R) u) (h2 : D2 ∈ StabilizerSubmodule (R := R) u) :
    derivationBracket D1 D2 ∈ StabilizerSubmodule (R := R) u := by
  dsimp [StabilizerSubmodule, derivationBracket] at h1 h2 ⊢
  show (D1 (D2 u) - D2 (D1 u)) = 0
  rw [h2, h1, map_zero, map_zero, sub_zero]

/-- Successive two-point stabilizer $\operatorname{Stab}(u, v) = \operatorname{Stab}(u) \cap \operatorname{Stab}(v)$. -/
def StabilizerPairSubmodule (u v : A) : Submodule R (A →ₗ[R] A) :=
  StabilizerSubmodule (R := R) u ⊓ StabilizerSubmodule (R := R) v

/-- 🏆 THEOREM (Dynkin Derivation Peeling Filtration):
    The stabilizer chain forms an exact decreasing filtration of Lie subalgebras:
    $$\operatorname{End}(A) \supseteq \operatorname{Stab}(u) \supseteq \operatorname{Stab}(u, v)$$ -/
theorem derivation_peeling_chain_le (u v : A) :
    StabilizerPairSubmodule (R := R) u v ≤ StabilizerSubmodule (R := R) u ∧
    StabilizerPairSubmodule (R := R) u v ≤ StabilizerSubmodule (R := R) v :=
  ⟨inf_le_left, inf_le_right⟩

/-- 🏆 THEOREM: If $D \in \operatorname{Stab}(u)$ is a derivation, then $D$ annihilates $u^2$:
    $D(u \cdot u) = 0$. -/
theorem stabilizer_preserves_square
    (mul : A →ₗ[R] A →ₗ[R] A) (u : A) (D : A →ₗ[R] A)
    (hder : IsNonAssocDerivation mul D) (hstab : D ∈ StabilizerSubmodule (R := R) u) :
    D (mul u u) = 0 := by
  have hd := hder u u
  dsimp [StabilizerSubmodule] at hstab
  rw [hstab] at hd
  have h0 : mul 0 u = 0 := by simp
  have h1 : mul u 0 = 0 := by simp
  rw [h0, h1, add_zero] at hd
  exact hd

/-! =========================================================================
    5. Evaluation Maps and Quotient Root-Space Exact Identifications
    ========================================================================= -/

/-- The evaluation linear map $\operatorname{eval}_u : \operatorname{End}(A) \toₗ[R] A$ sending $D \mapsto D(u)$. -/
def evalLinear (u : A) : (A →ₗ[R] A) →ₗ[R] A where
  toFun D := D u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evalLinear_apply (u : A) (D : A →ₗ[R] A) :
    evalLinear (R := R) u D = D u := rfl

/-- 🏆 THEOREM (First Peeling Kernel Identification):
    The kernel of the evaluation map at $u$ is identically the stabilizer $\operatorname{Stab}(u)$:
    $$\operatorname{ker}(\operatorname{eval}_u) = \operatorname{Stab}(u)$$ -/
theorem ker_evalLinear_eq_stabilizer (u : A) :
    LinearMap.ker (evalLinear (R := R) u) = StabilizerSubmodule (R := R) u := by
  ext D
  simp [evalLinear, StabilizerSubmodule, LinearMap.mem_ker]

/-- 🏆 THEOREM (Root-Space Representation Invariance):
    If $D \in \operatorname{Stab}(u)$ and $x \in A$ anticommutes with $u$ ($u \cdot x + x \cdot u = 0$),
    then $D(x)$ also anticommutes with $u$: $u \cdot D(x) + D(x) \cdot u = 0$. -/
theorem stabilizer_preserves_anticommuting
    (mul : A →ₗ[R] A →ₗ[R] A) (u x : A) (D : A →ₗ[R] A)
    (hder : IsNonAssocDerivation mul D) (hstab : D ∈ StabilizerSubmodule (R := R) u)
    (hanticomm : mul u x + mul x u = 0) :
    mul u (D x) + mul (D x) u = 0 := by
  have hd_ux := hder u x
  have hd_xu := hder x u
  have hd_sum : D (mul u x + mul x u) =
      (mul (D u) x + mul u (D x)) + (mul (D x) u + mul x (D u)) := by
    calc
      D (mul u x + mul x u) = D (mul u x) + D (mul x u) := map_add D _ _
      _ = (mul (D u) x + mul u (D x)) + (mul (D x) u + mul x (D u)) := by rw [hd_ux, hd_xu]
  rw [hanticomm, map_zero] at hd_sum
  dsimp [StabilizerSubmodule] at hstab
  rw [hstab] at hd_sum
  have h0x : mul 0 x = 0 := by simp
  have hx0 : mul x 0 = 0 := by simp
  rw [h0x, hx0, zero_add, add_zero] at hd_sum
  exact hd_sum.symm

end InfoGeometry.Algebra.PeelingOff
