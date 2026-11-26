/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.JordanInnerDerivations
import InfoGeometry.Exceptional.GenericGradedJacobiClosure
import Mathlib.Algebra.Jordan.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generic 3-Graded Tits–Kantor–Koecher Lie Algebra of a Commutative Jordan Algebra

This module constructs the generic 3-graded Tits–Kantor–Koecher (TKK) Lie algebra
`𝔓(J) = J₋ ⊕ str(J) ⊕ J₊` over any linear commutative Jordan algebra `J` equipped with
a structure operator submodule `str(J) ⊆ End_R(J)` and an involution-adjoint map
`adj : End_R(J) →ₗ[R] End_R(J)` satisfying `(A ∘ B)† = B† ∘ A†`, `L_a† = L_a`, and
`D† = -D` for derivations `D`.

## Main Results
1. Generic Jordan triple product `JordanTKK.triple` and structure operator
   `JordanTKK.tripleD R x y = L_{x*y} + [L_x, L_y]`.
2. Commutator identities:
   - `JordanTKK.derivation_comm_tripleD`: `[D, D_{x,y}] = D_{D x, y} + D_{x, D y}`.
   - `JordanTKK.jordanLmul_comm_tripleD`: `[L_a, D_{x,y}] = D_{a*x, y} - D_{x, a*y}`.
   - `JordanTKKDatum.adj_tripleD`: `(D_{x,y})† = D_{y,x}`.
   - `JordanTKKDatum.str_comm_tripleD`: `[T, D_{x,y}] = D_{T x, y} - D_{x, T† y}`.
3. 3-graded carrier `JordanTKK J S` with `LieRing` / `LieAlgebra R` instances proved
   via `GenericGradedJacobiClosure.global_leibniz_of_homogeneous`, `finrank` theorem,
   constructors/projections (`negLM`, `zeroLM`, `posLM`), and homogeneous bracket rules.
-/

noncomputable section

namespace InfoGeometry.Algebra

namespace JordanTKK

section JordanTriple

variable {R J : Type*} [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J] [IsScalarTower R J J]

/-- The generic Jordan triple product `{x, y, z} = (x * y) * z + (z * y) * x - (x * z) * y`. -/
def triple (x y z : J) : J :=
  (x * y) * z + (z * y) * x - (x * z) * y

theorem triple_outer_symm (x y z : J) : triple x y z = triple z y x := by
  simp only [triple, mul_comm z x]
  abel

@[simp] theorem triple_add_left (x₁ x₂ y z : J) :
    triple (x₁ + x₂) y z = triple x₁ y z + triple x₂ y z := by
  simp only [triple, add_mul, mul_add]
  abel

@[simp] theorem triple_add_middle (x y₁ y₂ z : J) :
    triple x (y₁ + y₂) z = triple x y₁ z + triple x y₂ z := by
  simp only [triple, add_mul, mul_add]
  abel

@[simp] theorem triple_add_right (x y z₁ z₂ : J) :
    triple x y (z₁ + z₂) = triple x y z₁ + triple x y z₂ := by
  simp only [triple, add_mul, mul_add]
  abel

@[simp] theorem triple_smul_left (r : R) (x y z : J) :
    triple (r • x) y z = r • triple x y z := by
  simp only [triple, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

@[simp] theorem triple_smul_middle (r : R) (x y z : J) :
    triple x (r • y) z = r • triple x y z := by
  simp only [triple, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

@[simp] theorem triple_smul_right (r : R) (x y z : J) :
    triple x y (r • z) = r • triple x y z := by
  simp only [triple, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

variable (R) in
/-- The Jordan triple structure operator `D_{x,y}(z) = {x, y, z}`. -/
def tripleD (x y : J) : Module.End R J where
  toFun z := triple x y z
  map_add' := triple_add_right x y
  map_smul' r z := triple_smul_right r x y z

@[simp] theorem tripleD_apply (x y z : J) :
    tripleD R x y z = triple x y z := rfl

@[simp] theorem tripleD_add_left (x₁ x₂ y : J) :
    tripleD R (x₁ + x₂) y = tripleD R x₁ y + tripleD R x₂ y := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, LinearMap.add_apply, triple_add_left]

@[simp] theorem tripleD_add_right (x y₁ y₂ : J) :
    tripleD R x (y₁ + y₂) = tripleD R x y₁ + tripleD R x y₂ := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, LinearMap.add_apply, triple_add_middle]

@[simp] theorem tripleD_smul_left (r : R) (x y : J) :
    tripleD R (r • x) y = r • tripleD R x y := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, LinearMap.smul_apply, triple_smul_left]

@[simp] theorem tripleD_smul_right (r : R) (x y : J) :
    tripleD R x (r • y) = r • tripleD R x y := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, LinearMap.smul_apply, triple_smul_middle]

@[simp] theorem tripleD_zero_left (y : J) : tripleD R (0 : J) y = 0 := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, triple, zero_mul, mul_zero, add_zero, sub_self, LinearMap.zero_apply]

@[simp] theorem tripleD_zero_right (x : J) : tripleD R x (0 : J) = 0 := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, triple, zero_mul, mul_zero, add_zero, sub_self, LinearMap.zero_apply]

theorem tripleD_eq_jordanLmul_add_innerDerivation (x y : J) :
    tripleD R x y = jordanLmul (R := R) (x * y) + jordanInnerDerivation (R := R) x y := by
  apply LinearMap.ext
  intro z
  simp only [tripleD_apply, triple, LinearMap.add_apply, jordanLmul_apply,
    jordanInnerDerivation_apply]
  rw [mul_comm (z * y) x, mul_comm z y, mul_comm (x * z) y]
  abel

theorem tripleD_eq_left_add_inner [IsCommJordan J] [Invertible (2 : R)] (x y : J) :
    tripleD R x y = jordanLmul (R := R) (x * y) +
      (jordanInnerDerivationBundled (R := R) x y : Module.End R J) :=
  tripleD_eq_jordanLmul_add_innerDerivation x y

theorem derivation_triple (D : NonAssocDerivation.derivations R J) (x y z : J) :
    (D : Module.End R J) (triple x y z) =
      triple ((D : Module.End R J) x) y z +
        triple x ((D : Module.End R J) y) z +
        triple x y ((D : Module.End R J) z) := by
  have hD : ∀ u v : J, (D : Module.End R J) (u * v) =
      (D : Module.End R J) u * v + u * (D : Module.End R J) v := D.property
  simp only [triple, map_add, map_sub, hD, add_mul]
  abel

theorem derivation_comm_tripleD (D : NonAssocDerivation.derivations R J) (x y : J) :
    (D : Module.End R J) ∘ₗ tripleD R x y - tripleD R x y ∘ₗ (D : Module.End R J) =
      tripleD R ((D : Module.End R J) x) y + tripleD R x ((D : Module.End R J) y) := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, tripleD_apply]
  rw [derivation_triple D x y z]
  abel

/-- Fundamental Jordan-TKK commutation identity: `[L_a, D_{x,y}] = D_{a*x, y} - D_{x, a*y}`. -/
theorem jordanLmul_comm_tripleD [IsCommJordan J] [Invertible (2 : R)] (a x y : J) :
    jordanLmul (R := R) a ∘ₗ tripleD R x y - tripleD R x y ∘ₗ jordanLmul (R := R) a =
      tripleD R (a * x) y - tripleD R x (a * y) := by
  apply LinearMap.ext
  intro z
  have h1_step := two_nsmul_lie_lmul_lmul_add_add_eq_zero a x y
  rw [two_nsmul] at h1_step
  have h1_raw := congrArg (fun f : AddMonoid.End J => f z) h1_step
  have h_nsmul : 2 •
      ((a * ((x * y) * z) - (x * y) * (a * z)) +
       (x * ((y * a) * z) - (y * a) * (x * z)) +
       (y * ((a * x) * z) - (a * x) * (y * z))) = 0 := by
    rw [two_nsmul]
    exact h1_raw
  rw [← Nat.cast_smul_eq_nsmul R] at h_nsmul
  have h_lin :
      (a * ((x * y) * z) - (x * y) * (a * z)) +
        (x * ((y * a) * z) - (y * a) * (x * z)) +
        (y * ((a * x) * z) - (a * x) * (y * z)) = 0 :=
    (isUnit_of_invertible (2 : R)).smul_left_cancel.mp (by simpa using h_nsmul)
  have h_left_comm :
      a * ((x * y) * z) - (x * y) * (a * z) =
        ((a * x) * (y * z) - y * ((a * x) * z)) -
          (x * ((a * y) * z) - (a * y) * (x * z)) := by
    rw [mul_comm y a] at h_lin
    rw [← sub_eq_zero, ← h_lin]
    abel
  have h_inner_eval :
      a * (x * (y * z) - y * (x * z)) - (x * (y * (a * z)) - y * (x * (a * z))) =
        ((a * x) * y) * z - (x * (a * y)) * z := by
    have h_inner_z := congrArg (fun f : Module.End R J => f z)
      (lie_derivation_jordanLmul (jordanInnerDerivation (R := R) x y)
        (jordanInnerDerivation_isLeibniz (R := R) x y) a)
    simp only [Ring.lie_def, Module.End.mul_apply, LinearMap.sub_apply,
      jordanLmul_apply, jordanInnerDerivation_apply] at h_inner_z
    have h_neg := congrArg Neg.neg h_inner_z
    rw [mul_comm x (y * a), mul_comm y (x * a), mul_comm y a, mul_comm x a,
      mul_comm (a * y) x] at h_neg
    simp only [neg_sub, sub_mul] at h_neg
    exact h_neg
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, jordanLmul_apply, tripleD_apply, triple]
  have h_expand :
      a * ((x * y) * z + (z * y) * x - (x * z) * y) -
        ((x * y) * (a * z) + ((a * z) * y) * x - (x * (a * z)) * y) =
      (a * ((x * y) * z) - (x * y) * (a * z)) +
        (a * (x * (y * z) - y * (x * z)) - (x * (y * (a * z)) - y * (x * (a * z)))) := by
    rw [mul_comm (z * y) x, mul_comm z y, mul_comm (x * z) y,
      mul_comm ((a * z) * y) x, mul_comm (a * z) y, mul_comm (x * (a * z)) y]
    simp only [mul_sub, mul_add]
    abel
  rw [h_expand, h_left_comm, h_inner_eval]
  rw [mul_comm (z * y) (a * x), mul_comm z y, mul_comm ((a * x) * z) y,
    mul_comm (z * (a * y)) x, mul_comm z (a * y), mul_comm (x * z) (a * y)]
  abel

end JordanTriple

end JordanTKK

section Datum

/-- Algebraic datum required to construct the 3-graded TKK Lie algebra of a commutative
Jordan algebra `J` over `R`. -/
structure JordanTKKDatum (R J : Type*) [CommRing R] [Invertible (2 : R)]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
    [IsScalarTower R J J] [IsCommJordan J] where
  str : Submodule R (Module.End R J)
  adj : Module.End R J →ₗ[R] Module.End R J
  adj_comp : ∀ A B : Module.End R J, adj (A ∘ₗ B) = adj B ∘ₗ adj A
  adj_jordanLmul : ∀ a : J, adj (jordanLmul (R := R) a) = jordanLmul (R := R) a
  adj_derivation : ∀ D : NonAssocDerivation.derivations R J,
    adj (D : Module.End R J) = -(D : Module.End R J)
  str_decomp : ∀ T ∈ str, ∃ D : NonAssocDerivation.derivations R J, ∃ a : J,
    T = (D : Module.End R J) + jordanLmul (R := R) a
  jordanLmul_mem_str : ∀ a : J, jordanLmul (R := R) a ∈ str
  innerDeriv_mem_str : ∀ x y : J,
    (jordanInnerDerivationBundled (R := R) x y : Module.End R J) ∈ str
  str_lie_mem : ∀ {T U : Module.End R J}, T ∈ str → U ∈ str → T ∘ₗ U - U ∘ₗ T ∈ str

namespace JordanTKKDatum

variable {R J : Type*} [CommRing R] [Invertible (2 : R)]
  [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
  [IsScalarTower R J J] [IsCommJordan J]

theorem tripleD_mem_str (D : JordanTKKDatum R J) (x y : J) :
    JordanTKK.tripleD R x y ∈ D.str := by
  rw [JordanTKK.tripleD_eq_left_add_inner]
  exact D.str.add_mem (D.jordanLmul_mem_str (x * y)) (D.innerDeriv_mem_str x y)

theorem adj_tripleD (D : JordanTKKDatum R J) (x y : J) :
    D.adj (JordanTKK.tripleD R x y) = JordanTKK.tripleD R y x := by
  rw [JordanTKK.tripleD_eq_left_add_inner, JordanTKK.tripleD_eq_left_add_inner]
  rw [map_add, D.adj_jordanLmul, D.adj_derivation, mul_comm x y]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply]
  change (y * x) * z + -(x * (y * z) - y * (x * z)) =
    (y * x) * z + (y * (x * z) - x * (y * z))
  abel

theorem adj_mem_str (D : JordanTKKDatum R J) {T : Module.End R J} (hT : T ∈ D.str) :
    D.adj T ∈ D.str := by
  rcases D.str_decomp T hT with ⟨E, a, rfl⟩
  rw [map_add, D.adj_derivation, D.adj_jordanLmul]
  have hE : (E : Module.End R J) ∈ D.str := by
    have ha := D.jordanLmul_mem_str a
    have hsub := D.str.sub_mem hT ha
    simpa [add_sub_cancel_right] using hsub
  exact D.str.add_mem (D.str.neg_mem hE) (D.jordanLmul_mem_str a)

theorem str_comm_tripleD (D : JordanTKKDatum R J) (T : D.str) (x y : J) :
    T.1 ∘ₗ JordanTKK.tripleD R x y - JordanTKK.tripleD R x y ∘ₗ T.1 =
      JordanTKK.tripleD R (T.1 x) y - JordanTKK.tripleD R x (D.adj T.1 y) := by
  rcases D.str_decomp T.1 T.2 with ⟨E, a, hT⟩
  have h_adj : D.adj T.1 = -(E : Module.End R J) + jordanLmul (R := R) a := by
    rw [hT, map_add, D.adj_derivation, D.adj_jordanLmul]
  rw [h_adj, hT]
  have h_deriv := JordanTKK.derivation_comm_tripleD E x y
  have h_lmul := JordanTKK.jordanLmul_comm_tripleD (R := R) a x y
  apply LinearMap.ext
  intro z
  have h_dz := congrArg (fun f : Module.End R J => f z) h_deriv
  have h_lz := congrArg (fun f : Module.End R J => f z) h_lmul
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, JordanTKK.tripleD_apply] at h_dz h_lz ⊢
  rw [JordanTKK.triple_add_left, JordanTKK.triple_add_middle]
  have h_neg : JordanTKK.triple x (-(E : Module.End R J) y) z =
      -JordanTKK.triple x ((E : Module.End R J) y) z := by
    simpa using JordanTKK.triple_smul_middle (R := R) (-1 : R) x ((E : Module.End R J) y) z
  rw [h_neg]
  simp only [JordanTKK.triple_add_right]
  have hsum :
      ((E : Module.End R J) (JordanTKK.triple x y z) +
          (jordanLmul (R := R) a) (JordanTKK.triple x y z)) -
        (JordanTKK.triple x y ((E : Module.End R J) z) +
          JordanTKK.triple x y ((jordanLmul (R := R) a) z)) =
      ((E : Module.End R J) (JordanTKK.triple x y z) -
          JordanTKK.triple x y ((E : Module.End R J) z)) +
        ((jordanLmul (R := R) a) (JordanTKK.triple x y z) -
          JordanTKK.triple x y ((jordanLmul (R := R) a) z)) := by
    abel
  rw [hsum, h_dz, h_lz]
  abel

end JordanTKKDatum

end Datum

/-- Constructive T17 model witness for `JordanTKKDatum` over `ℝ`. -/
def realJordanTKKDatum : JordanTKKDatum ℝ ℝ where
  str := ⊤
  adj := LinearMap.id
  adj_comp A B := by
    apply LinearMap.ext
    intro x
    have hA : A x = x * A 1 := by
      have hx := congrArg (fun y => A y) (mul_one x).symm
      rw [← smul_eq_mul, map_smul, smul_eq_mul] at hx
      exact hx
    have hB : B x = x * B 1 := by
      have hx := congrArg (fun y => B y) (mul_one x).symm
      rw [← smul_eq_mul, map_smul, smul_eq_mul] at hx
      exact hx
    simp only [LinearMap.id_apply, LinearMap.comp_apply]
    have hAB : A (B x) = B x * A 1 := by
      have hx := congrArg (fun y => A y) (mul_one (B x)).symm
      rw [← smul_eq_mul, map_smul, smul_eq_mul] at hx
      exact hx
    have hBA : B (A x) = A x * B 1 := by
      have hx := congrArg (fun y => B y) (mul_one (A x)).symm
      rw [← smul_eq_mul, map_smul, smul_eq_mul] at hx
      exact hx
    rw [hAB, hBA, hA, hB]
    exact mul_right_comm x (B 1) (A 1)
  adj_jordanLmul a := rfl
  adj_derivation D := by
    apply LinearMap.ext
    intro x
    have h1 : (D : Module.End ℝ ℝ) 1 = 0 := by
      have h := D.property (1 : ℝ) 1
      rw [mul_one, one_mul] at h
      have h2 : (D : Module.End ℝ ℝ) 1 + 0 =
          (D : Module.End ℝ ℝ) 1 + (D : Module.End ℝ ℝ) 1 := by
        simpa using h
      exact (add_left_cancel h2).symm
    have hx : (D : Module.End ℝ ℝ) x = 0 := by
      have hsmul : (D : Module.End ℝ ℝ) x = x * (D : Module.End ℝ ℝ) 1 := by
        have hx1 := congrArg (fun y => (D : Module.End ℝ ℝ) y) (mul_one x).symm
        rw [← smul_eq_mul, map_smul, smul_eq_mul] at hx1
        exact hx1
      rw [hsmul, h1, mul_zero]
    simp [hx]
  str_decomp T _ := by
    refine ⟨0, T 1, ?_⟩
    apply LinearMap.ext
    intro x
    change T x = (0 : Module.End ℝ ℝ) x + T 1 * x
    rw [LinearMap.zero_apply, zero_add]
    have hx := congrArg (fun y => T y) (mul_one x).symm
    rw [← smul_eq_mul, map_smul, smul_eq_mul, mul_comm] at hx
    exact hx
  jordanLmul_mem_str _ := Submodule.mem_top
  innerDeriv_mem_str _ _ := Submodule.mem_top
  str_lie_mem _ _ := Submodule.mem_top

/-- Carrier of the 3-graded Tits–Kantor–Koecher algebra `J ⊕ S ⊕ J`. -/
@[ext]
structure JordanTKK (J S : Type*) where
  neg : J
  zero : S
  pos : J

instance instInhabitedJordanTKK {J S : Type*} [Zero J] [Zero S] :
    Inhabited (JordanTKK J S) :=
  ⟨⟨0, 0, 0⟩⟩

/-- Constructive T17 ground witness for `JordanTKK`. -/
def realJordanTKKZero : JordanTKK ℝ ℝ := ⟨0, 0, 0⟩

namespace JordanTKK

section ModuleStructure

variable {R J S : Type*}

instance [SMul R J] [SMul R S] : SMul R (JordanTKK J S) :=
  ⟨fun r X => ⟨r • X.neg, r • X.zero, r • X.pos⟩⟩

@[simp] theorem smul_neg_comp [SMul R J] [SMul R S] (r : R) (X : JordanTKK J S) :
    (r • X).neg = r • X.neg := rfl
@[simp] theorem smul_zero_comp [SMul R J] [SMul R S] (r : R) (X : JordanTKK J S) :
    (r • X).zero = r • X.zero := rfl
@[simp] theorem smul_pos_comp [SMul R J] [SMul R S] (r : R) (X : JordanTKK J S) :
    (r • X).pos = r • X.pos := rfl

instance [AddCommGroup J] [AddCommGroup S] : AddCommGroup (JordanTKK J S) where
  add X Y := ⟨X.neg + Y.neg, X.zero + Y.zero, X.pos + Y.pos⟩
  add_assoc X Y Z := by ext <;> exact add_assoc _ _ _
  zero := ⟨0, 0, 0⟩
  zero_add X := by ext <;> exact zero_add _
  add_zero X := by ext <;> exact add_zero _
  nsmul n X := ⟨n • X.neg, n • X.zero, n • X.pos⟩
  nsmul_zero X := by ext <;> exact zero_nsmul _
  nsmul_succ n X := by ext <;> exact succ_nsmul _ _
  zsmul n X := ⟨n • X.neg, n • X.zero, n • X.pos⟩
  zsmul_zero' X := by ext <;> exact zero_zsmul _
  zsmul_succ' n X := by
    ext
    · change ((n + 1 : ℕ) : ℤ) • X.neg = (n : ℤ) • X.neg + X.neg
      rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
    · change ((n + 1 : ℕ) : ℤ) • X.zero = (n : ℤ) • X.zero + X.zero
      rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
    · change ((n + 1 : ℕ) : ℤ) • X.pos = (n : ℤ) • X.pos + X.pos
      rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
  zsmul_neg' n X := by
    ext
    · change Int.negSucc n • X.neg = -(((n + 1 : ℕ) : ℤ) • X.neg)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
    · change Int.negSucc n • X.zero = -(((n + 1 : ℕ) : ℤ) • X.zero)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
    · change Int.negSucc n • X.pos = -(((n + 1 : ℕ) : ℤ) • X.pos)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
  neg X := ⟨-X.neg, -X.zero, -X.pos⟩
  sub X Y := ⟨X.neg - Y.neg, X.zero - Y.zero, X.pos - Y.pos⟩
  sub_eq_add_neg X Y := by ext <;> exact sub_eq_add_neg _ _
  neg_add_cancel X := by ext <;> exact neg_add_cancel _
  add_comm X Y := by ext <;> exact add_comm _ _

@[simp] theorem zero_neg [AddCommGroup J] [AddCommGroup S] :
    (0 : JordanTKK J S).neg = 0 := rfl
@[simp] theorem zero_zero [AddCommGroup J] [AddCommGroup S] :
    (0 : JordanTKK J S).zero = 0 := rfl
@[simp] theorem zero_pos [AddCommGroup J] [AddCommGroup S] :
    (0 : JordanTKK J S).pos = 0 := rfl

@[simp] theorem add_neg [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X + Y).neg = X.neg + Y.neg := rfl
@[simp] theorem add_zero_comp [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X + Y).zero = X.zero + Y.zero := rfl
@[simp] theorem add_pos [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X + Y).pos = X.pos + Y.pos := rfl

@[simp] theorem neg_neg_comp [AddCommGroup J] [AddCommGroup S] (X : JordanTKK J S) :
    (-X).neg = -X.neg := rfl
@[simp] theorem neg_zero_comp [AddCommGroup J] [AddCommGroup S] (X : JordanTKK J S) :
    (-X).zero = -X.zero := rfl
@[simp] theorem neg_pos_comp [AddCommGroup J] [AddCommGroup S] (X : JordanTKK J S) :
    (-X).pos = -X.pos := rfl

@[simp] theorem sub_neg_comp [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X - Y).neg = X.neg - Y.neg := rfl
@[simp] theorem sub_zero_comp [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X - Y).zero = X.zero - Y.zero := rfl
@[simp] theorem sub_pos_comp [AddCommGroup J] [AddCommGroup S] (X Y : JordanTKK J S) :
    (X - Y).pos = X.pos - Y.pos := rfl

instance [CommRing R] [AddCommGroup J] [Module R J] [AddCommGroup S] [Module R S] :
    Module R (JordanTKK J S) where
  smul := (· • ·)
  one_smul X := by ext <;> exact one_smul _ _
  mul_smul r s X := by ext <;> exact mul_smul _ _ _
  smul_zero r := by ext <;> exact smul_zero _
  smul_add r X Y := by ext <;> exact smul_add _ _ _
  add_smul r s X := by ext <;> exact add_smul _ _ _
  zero_smul X := by ext <;> exact zero_smul _ _

variable [CommRing R] [AddCommGroup J] [Module R J] [AddCommGroup S] [Module R S]

/-- Linear equivalence identifying `JordanTKK J S` with `J × S × J`. -/
def toProdEquiv : JordanTKK J S ≃ₗ[R] J × S × J where
  toFun X := (X.neg, X.zero, X.pos)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv X := by ext <;> rfl
  right_inv p := by rcases p with ⟨x, T, y⟩; rfl
  map_add' X Y := rfl
  map_smul' r X := rfl

instance [Module.Finite R J] [Module.Finite R S] : Module.Finite R (JordanTKK J S) :=
  Module.Finite.equiv (toProdEquiv (R := R) (J := J) (S := S)).symm

theorem finrank_jordanTKK {F : Type*} [Field F] [Module F J] [Module F S]
    [Module.Finite F J] [Module.Finite F S] :
    Module.finrank F (JordanTKK J S) =
      Module.finrank F J + Module.finrank F S + Module.finrank F J := by
  rw [LinearEquiv.finrank_eq (toProdEquiv (R := F) (J := J) (S := S))]
  rw [Module.finrank_prod, Module.finrank_prod]
  abel

theorem finrank_jordanTKK_two_mul {F : Type*} [Field F] [Module F J] [Module F S]
    [Module.Finite F J] [Module.Finite F S] :
    Module.finrank F (JordanTKK J S) = 2 * Module.finrank F J + Module.finrank F S := by
  rw [finrank_jordanTKK (F := F) (J := J) (S := S)]
  omega

/-- Linear injection of grade `-1` into `JordanTKK J S`. -/
def negLM : J →ₗ[R] JordanTKK J S where
  toFun x := ⟨x, 0, 0⟩
  map_add' x₁ x₂ := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Linear injection of grade `0` into `JordanTKK J S`. -/
def zeroLM : S →ₗ[R] JordanTKK J S where
  toFun T := ⟨0, T, 0⟩
  map_add' T₁ T₂ := by ext <;> simp
  map_smul' r T := by ext <;> simp

/-- Linear injection of grade `+1` into `JordanTKK J S`. -/
def posLM : J →ₗ[R] JordanTKK J S where
  toFun y := ⟨0, 0, y⟩
  map_add' y₁ y₂ := by ext <;> simp
  map_smul' r y := by ext <;> simp

/-- Linear projection onto grade `-1`. -/
def projNeg : JordanTKK J S →ₗ[R] J where
  toFun X := X.neg
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear projection onto grade `0`. -/
def projZero : JordanTKK J S →ₗ[R] S where
  toFun X := X.zero
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear projection onto grade `+1`. -/
def projPos : JordanTKK J S →ₗ[R] J where
  toFun X := X.pos
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem negLM_neg (x : J) : (negLM (R := R) (S := S) x).neg = x := rfl
@[simp] theorem negLM_zero (x : J) : (negLM (R := R) (S := S) x).zero = 0 := rfl
@[simp] theorem negLM_pos (x : J) : (negLM (R := R) (S := S) x).pos = 0 := rfl

@[simp] theorem zeroLM_neg (T : S) : (zeroLM (R := R) (J := J) T).neg = 0 := rfl
@[simp] theorem zeroLM_zero (T : S) : (zeroLM (R := R) (J := J) T).zero = T := rfl
@[simp] theorem zeroLM_pos (T : S) : (zeroLM (R := R) (J := J) T).pos = 0 := rfl

@[simp] theorem posLM_neg (y : J) : (posLM (R := R) (S := S) y).neg = 0 := rfl
@[simp] theorem posLM_zero (y : J) : (posLM (R := R) (S := S) y).zero = 0 := rfl
@[simp] theorem posLM_pos (y : J) : (posLM (R := R) (S := S) y).pos = y := rfl

@[simp] theorem projNeg_apply (X : JordanTKK J S) : projNeg (R := R) X = X.neg := rfl
@[simp] theorem projZero_apply (X : JordanTKK J S) : projZero (R := R) X = X.zero := rfl
@[simp] theorem projPos_apply (X : JordanTKK J S) : projPos (R := R) X = X.pos := rfl

theorem negLM_injective : Function.Injective (negLM (R := R) (J := J) (S := S)) := by
  intro x₁ x₂ h
  exact congrArg JordanTKK.neg h

theorem zeroLM_injective : Function.Injective (zeroLM (R := R) (J := J) (S := S)) := by
  intro T₁ T₂ h
  exact congrArg JordanTKK.zero h

theorem posLM_injective : Function.Injective (posLM (R := R) (J := J) (S := S)) := by
  intro y₁ y₂ h
  exact congrArg JordanTKK.pos h

theorem eq_neg_add_zero_add_pos (X : JordanTKK J S) :
    X = negLM (R := R) X.neg + zeroLM (R := R) X.zero + posLM (R := R) X.pos := by
  ext <;> simp

end ModuleStructure

section BracketAndJacobi

variable {R J : Type*} [CommRing R] [Invertible (2 : R)]
  [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
  [IsScalarTower R J J] [IsCommJordan J]

/-- The raw bilinear TKK bracket on `JordanTKK J D.str`, matching `H3ZornTKKNative.tkkBracket`. -/
def bracketBilin (D : JordanTKKDatum R J) :
    JordanTKK J D.str →ₗ[R] JordanTKK J D.str →ₗ[R] JordanTKK J D.str where
  toFun X :=
    { toFun := fun Y =>
        { neg := X.zero.1 Y.neg - Y.zero.1 X.neg
          zero := ⟨(X.zero.1 ∘ₗ Y.zero.1 - Y.zero.1 ∘ₗ X.zero.1) +
              (tripleD R X.neg Y.pos - tripleD R Y.neg X.pos),
            D.str.add_mem (D.str_lie_mem X.zero.2 Y.zero.2)
              (D.str.sub_mem (D.tripleD_mem_str X.neg Y.pos) (D.tripleD_mem_str Y.neg X.pos))⟩
          pos := -D.adj X.zero.1 Y.pos + D.adj Y.zero.1 X.pos }
      map_add' Y₁ Y₂ := by
        apply JordanTKK.ext
        · change X.zero.1 (Y₁.neg + Y₂.neg) - (Y₁.zero.1 + Y₂.zero.1) X.neg =
            (X.zero.1 Y₁.neg - Y₁.zero.1 X.neg) + (X.zero.1 Y₂.neg - Y₂.zero.1 X.neg)
          simp only [map_add, LinearMap.add_apply]
          abel
        · apply Subtype.ext
          apply LinearMap.ext
          intro z
          simp only [add_neg, add_zero_comp, add_pos, Submodule.coe_add, LinearMap.comp_add,
            LinearMap.add_comp, tripleD_add_right, tripleD_add_left,
            LinearMap.add_apply, LinearMap.sub_apply]
          abel
        · change -D.adj X.zero.1 (Y₁.pos + Y₂.pos) + D.adj (Y₁.zero.1 + Y₂.zero.1) X.pos =
            (-D.adj X.zero.1 Y₁.pos + D.adj Y₁.zero.1 X.pos) +
            (-D.adj X.zero.1 Y₂.pos + D.adj Y₂.zero.1 X.pos)
          simp only [map_add, LinearMap.add_apply]
          abel
      map_smul' r Y := by
        apply JordanTKK.ext
        · change X.zero.1 (r • Y.neg) - (r • Y.zero.1) X.neg =
            r • (X.zero.1 Y.neg - Y.zero.1 X.neg)
          simp only [map_smul, LinearMap.smul_apply, smul_sub]
        · apply Subtype.ext
          apply LinearMap.ext
          intro z
          simp only [smul_neg_comp, smul_zero_comp, smul_pos_comp, Submodule.coe_smul,
            LinearMap.comp_smul, LinearMap.smul_comp, tripleD_smul_right, tripleD_smul_left,
            LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, RingHom.id_apply]
          simp only [smul_add, smul_sub]
        · change -D.adj X.zero.1 (r • Y.pos) + D.adj (r • Y.zero.1) X.pos =
            r • (-D.adj X.zero.1 Y.pos + D.adj Y.zero.1 X.pos)
          rw [map_smul, map_smul, LinearMap.smul_apply, smul_add, ← _root_.smul_neg] }
  map_add' X₁ X₂ := by
    apply LinearMap.ext
    intro Y
    apply JordanTKK.ext
    · change (X₁.zero.1 + X₂.zero.1) Y.neg - Y.zero.1 (X₁.neg + X₂.neg) =
        (X₁.zero.1 Y.neg - Y.zero.1 X₁.neg) + (X₂.zero.1 Y.neg - Y.zero.1 X₂.neg)
      simp only [LinearMap.add_apply, map_add]
      abel
    · apply Subtype.ext
      apply LinearMap.ext
      intro z
      simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, add_neg, add_zero_comp,
        add_pos, Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp,
        tripleD_add_left, tripleD_add_right, LinearMap.sub_apply]
      abel
    · change -D.adj (X₁.zero.1 + X₂.zero.1) Y.pos + D.adj Y.zero.1 (X₁.pos + X₂.pos) =
        (-D.adj X₁.zero.1 Y.pos + D.adj Y.zero.1 X₁.pos) +
        (-D.adj X₂.zero.1 Y.pos + D.adj Y.zero.1 X₂.pos)
      simp only [map_add, LinearMap.add_apply]
      abel
  map_smul' r X := by
    apply LinearMap.ext
    intro Y
    apply JordanTKK.ext
    · change (r • X.zero.1) Y.neg - Y.zero.1 (r • X.neg) =
        r • (X.zero.1 Y.neg - Y.zero.1 X.neg)
      simp only [LinearMap.smul_apply, map_smul, smul_sub]
    · apply Subtype.ext
      apply LinearMap.ext
      intro z
      simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_neg_comp,
        smul_zero_comp, smul_pos_comp, Submodule.coe_smul, LinearMap.comp_smul,
        LinearMap.smul_comp, tripleD_smul_left, tripleD_smul_right, LinearMap.add_apply,
        LinearMap.sub_apply, RingHom.id_apply]
      simp only [smul_add, smul_sub]
    · change -D.adj (r • X.zero.1) Y.pos + D.adj Y.zero.1 (r • X.pos) =
        r • (-D.adj X.zero.1 Y.pos + D.adj Y.zero.1 X.pos)
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_add, ← _root_.smul_neg]

theorem bracketBilin_self (D : JordanTKKDatum R J) (X : JordanTKK J D.str) :
    bracketBilin D X X = 0 := by
  apply JordanTKK.ext
  · simp [bracketBilin]
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [bracketBilin]
  · simp [bracketBilin]

theorem bracketBilin_antisymm (D : JordanTKKDatum R J) (X Y : JordanTKK J D.str) :
    bracketBilin D Y X = -bracketBilin D X Y := by
  apply JordanTKK.ext
  · simp only [bracketBilin, LinearMap.coe_mk, AddHom.coe_mk, neg_neg_comp]
    abel
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp only [bracketBilin, LinearMap.coe_mk, AddHom.coe_mk, neg_zero_comp,
      Submodule.coe_neg, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sub_apply]
    abel
  · simp only [bracketBilin, LinearMap.coe_mk, AddHom.coe_mk, neg_pos_comp]
    abel

omit [Invertible (2 : R)] in
private theorem leibnizDefect_swap₁₂ {V : Type*} [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] V) (h_anti : ∀ u v, B v u = -B u v) (x y z : V) :
    InfoGeometry.Exceptional.leibnizDefect B y x z =
      -InfoGeometry.Exceptional.leibnizDefect B x y z := by
  simp only [InfoGeometry.Exceptional.leibnizDefect]
  rw [h_anti y x, map_neg, LinearMap.neg_apply]
  abel

omit [Invertible (2 : R)] in
private theorem leibnizDefect_swap₂₃ {V : Type*} [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] V) (h_anti : ∀ u v, B v u = -B u v) (x y z : V) :
    InfoGeometry.Exceptional.leibnizDefect B x z y =
      -InfoGeometry.Exceptional.leibnizDefect B x y z := by
  simp only [InfoGeometry.Exceptional.leibnizDefect]
  rw [h_anti z y, map_neg, h_anti (B x z) y, h_anti z (B x y)]
  abel

omit [Invertible (2 : R)] in
private theorem leibnizDefect_cycle {V : Type*} [AddCommGroup V] [Module R V]
    (B : V →ₗ[R] V →ₗ[R] V) (h_anti : ∀ u v, B v u = -B u v) (x y z : V) :
    InfoGeometry.Exceptional.leibnizDefect B y z x =
      InfoGeometry.Exceptional.leibnizDefect B x y z := by
  rw [leibnizDefect_swap₂₃ B h_anti y x z, leibnizDefect_swap₁₂ B h_anti x y z, neg_neg]

/-- The three grading labels `{-1, 0, +1}` of the TKK Lie algebra. -/
inductive TKKGrade : Type
  | neg
  | zero
  | pos
  deriving DecidableEq, Inhabited

instance : Fintype TKKGrade where
  elems := {TKKGrade.neg, TKKGrade.zero, TKKGrade.pos}
  complete := by
    intro g
    cases g <;> simp

/-- Homogeneous projectors onto the `-1`, `0`, and `+1` grade spaces. -/
def gradeProj {S : Type*} [AddCommGroup S] [Module R S] :
    TKKGrade → JordanTKK J S →ₗ[R] JordanTKK J S
  | .neg => (negLM (R := R)).comp (projNeg (R := R))
  | .zero => (zeroLM (R := R)).comp (projZero (R := R))
  | .pos => (posLM (R := R)).comp (projPos (R := R))

omit [Invertible (2 : R)] [SMulCommClass R J J] [IsScalarTower R J J] [IsCommJordan J] in
theorem gradeProj_sum {S : Type*} [AddCommGroup S] [Module R S] (X : JordanTKK J S) :
    (∑ i : TKKGrade, gradeProj (R := R) i X) = X := by
  have h_univ : (Finset.univ : Finset TKKGrade) = {.neg, .zero, .pos} := by
    ext g
    cases g <;> simp
  rw [h_univ]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, not_false_eq_true, or_self, Finset.sum_singleton, gradeProj,
    LinearMap.comp_apply, projNeg_apply, projZero_apply, projPos_apply]
  rw [← add_assoc]
  exact (eq_neg_add_zero_add_pos (R := R) X).symm

private lemma bracket_neg_neg (D : JordanTKKDatum R J) (x₁ x₂ : J) :
    bracketBilin D (negLM (R := R) x₁) (negLM (R := R) x₂) = 0 := by
  apply JordanTKK.ext <;> simp [bracketBilin]

private lemma bracket_pos_pos (D : JordanTKKDatum R J) (y₁ y₂ : J) :
    bracketBilin D (posLM (R := R) y₁) (posLM (R := R) y₂) = 0 := by
  apply JordanTKK.ext <;> simp [bracketBilin]

private lemma bracket_zero_zero (D : JordanTKKDatum R J) (T₁ T₂ : D.str) :
    bracketBilin D (zeroLM (R := R) T₁) (zeroLM (R := R) T₂) =
      zeroLM (R := R) ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, D.str_lie_mem T₁.2 T₂.2⟩ := by
  apply JordanTKK.ext
  · simp [bracketBilin]
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [bracketBilin]
  · simp [bracketBilin]

private lemma bracket_zero_neg (D : JordanTKKDatum R J) (T : D.str) (x : J) :
    bracketBilin D (zeroLM (R := R) T) (negLM (R := R) x) = negLM (R := R) (T.1 x) := by
  apply JordanTKK.ext
  · simp [bracketBilin]
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [bracketBilin]
  · simp [bracketBilin]

private lemma bracket_zero_pos (D : JordanTKKDatum R J) (T : D.str) (y : J) :
    bracketBilin D (zeroLM (R := R) T) (posLM (R := R) y) = posLM (R := R) (-D.adj T.1 y) := by
  apply JordanTKK.ext
  · simp [bracketBilin]
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [bracketBilin]
  · simp [bracketBilin]

private lemma bracket_neg_pos (D : JordanTKKDatum R J) (x y : J) :
    bracketBilin D (negLM (R := R) x) (posLM (R := R) y) =
      zeroLM (R := R) ⟨tripleD R x y, D.tripleD_mem_str x y⟩ := by
  apply JordanTKK.ext
  · simp [bracketBilin]
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp [bracketBilin]
  · simp [bracketBilin]

private lemma bracket_neg_zero (D : JordanTKKDatum R J) (x : J) (T : D.str) :
    bracketBilin D (negLM (R := R) x) (zeroLM (R := R) T) = negLM (R := R) (-(T.1 x)) := by
  rw [bracketBilin_antisymm, bracket_zero_neg]
  ext <;> simp

private lemma bracket_pos_zero (D : JordanTKKDatum R J) (y : J) (T : D.str) :
    bracketBilin D (posLM (R := R) y) (zeroLM (R := R) T) = posLM (R := R) (D.adj T.1 y) := by
  rw [bracketBilin_antisymm, bracket_zero_pos]
  ext <;> simp

private lemma bracket_pos_neg (D : JordanTKKDatum R J) (y x : J) :
    bracketBilin D (posLM (R := R) y) (negLM (R := R) x) =
      zeroLM (R := R) ⟨-tripleD R x y, D.str.neg_mem (D.tripleD_mem_str x y)⟩ := by
  rw [bracketBilin_antisymm, bracket_neg_pos]
  ext <;> simp

private lemma defect_neg_neg_neg (D : JordanTKKDatum R J) (x₁ x₂ x₃ : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x₁) (negLM (R := R) x₂) (negLM (R := R) x₃) = 0 := by
  simp [InfoGeometry.Exceptional.leibnizDefect, bracket_neg_neg]

private lemma defect_neg_neg_zero (D : JordanTKKDatum R J) (x₁ x₂ : J) (T : D.str) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x₁) (negLM (R := R) x₂) (zeroLM (R := R) T) = 0 := by
  simp [InfoGeometry.Exceptional.leibnizDefect, bracket_neg_neg, bracket_neg_zero]

private lemma defect_neg_neg_pos (D : JordanTKKDatum R J) (x₁ x₂ y : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x₁) (negLM (R := R) x₂) (posLM (R := R) y) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_neg_pos, bracket_neg_neg,
    map_zero, LinearMap.zero_apply, bracket_neg_zero]
  apply JordanTKK.ext
  · simp only [sub_neg_comp, negLM_neg, zero_neg, tripleD_apply, sub_zero, sub_eq_zero]
    rw [neg_inj]
    exact triple_outer_symm x₂ y x₁
  · simp
  · simp

private lemma defect_neg_zero_zero (D : JordanTKKDatum R J) (x : J) (T₁ T₂ : D.str) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x) (zeroLM (R := R) T₁) (zeroLM (R := R) T₂) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_zero_zero, bracket_neg_zero,
    bracket_zero_neg]
  apply JordanTKK.ext
  · simp only [sub_neg_comp, neg_neg_comp, negLM_neg, LinearMap.sub_apply, LinearMap.comp_apply,
      zero_neg, map_neg]
    abel
  · simp
  · simp

private lemma defect_neg_zero_pos (D : JordanTKKDatum R J) (x : J) (T : D.str) (y : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x) (zeroLM (R := R) T) (posLM (R := R) y) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_zero_pos, bracket_neg_pos,
    bracket_neg_zero, bracket_zero_zero]
  apply JordanTKK.ext
  · simp
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    have hcomm := congrArg (fun f : Module.End R J => f z) (D.str_comm_tripleD T x y)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, tripleD_apply] at hcomm
    simp only [sub_zero_comp, Submodule.coe_sub, zeroLM_zero, LinearMap.sub_apply,
      LinearMap.comp_apply, tripleD_apply, zero_zero, ZeroMemClass.coe_zero,
      LinearMap.zero_apply]
    have h_t1 : triple (-(T.1 x)) y z = -triple (T.1 x) y z := by
      simpa using triple_smul_left (R := R) (-1 : R) (T.1 x) y z
    have h_t2 : triple x (-D.adj T.1 y) z = -triple x (D.adj T.1 y) z := by
      simpa using triple_smul_middle (R := R) (-1 : R) x (D.adj T.1 y) z
    rw [h_t1, h_t2, hcomm]
    abel
  · simp

private lemma defect_neg_pos_pos (D : JordanTKKDatum R J) (x y₁ y₂ : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (negLM (R := R) x) (posLM (R := R) y₁) (posLM (R := R) y₂) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_pos_pos, map_zero,
    bracket_neg_pos, bracket_zero_pos, bracket_pos_zero, zero_sub]
  apply JordanTKK.ext
  · simp
  · simp
  · simp only [neg_pos_comp, sub_pos_comp, posLM_pos, zero_pos, D.adj_tripleD,
      tripleD_apply, neg_neg, sub_eq_zero]
    exact triple_outer_symm y₁ x y₂

private lemma defect_zero_zero_zero (D : JordanTKKDatum R J) (T₁ T₂ T₃ : D.str) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (zeroLM (R := R) T₁) (zeroLM (R := R) T₂) (zeroLM (R := R) T₃) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_zero_zero]
  apply JordanTKK.ext
  · simp
  · apply Subtype.ext
    apply LinearMap.ext
    intro z
    simp only [sub_zero_comp, Submodule.coe_sub, zeroLM_zero, LinearMap.sub_apply,
      LinearMap.comp_apply, map_sub, zero_zero, ZeroMemClass.coe_zero,
      LinearMap.zero_apply]
    abel
  · simp

private lemma defect_zero_zero_pos (D : JordanTKKDatum R J) (T₁ T₂ : D.str) (y : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (zeroLM (R := R) T₁) (zeroLM (R := R) T₂) (posLM (R := R) y) = 0 := by
  simp only [InfoGeometry.Exceptional.leibnizDefect, bracket_zero_pos, bracket_zero_zero]
  apply JordanTKK.ext
  · simp
  · simp
  · simp only [sub_pos_comp, neg_pos_comp, posLM_pos, map_sub, D.adj_comp,
      LinearMap.sub_apply, LinearMap.comp_apply, map_neg, zero_pos]
    abel

private lemma defect_zero_pos_pos (D : JordanTKKDatum R J) (T : D.str) (y₁ y₂ : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (zeroLM (R := R) T) (posLM (R := R) y₁) (posLM (R := R) y₂) = 0 := by
  simp [InfoGeometry.Exceptional.leibnizDefect, bracket_pos_pos, bracket_zero_pos]

private lemma defect_pos_pos_pos (D : JordanTKKDatum R J) (y₁ y₂ y₃ : J) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (posLM (R := R) y₁) (posLM (R := R) y₂) (posLM (R := R) y₃) = 0 := by
  simp [InfoGeometry.Exceptional.leibnizDefect, bracket_pos_pos]

private lemma defect_all_cells (D : JordanTKKDatum R J)
    (i j k : TKKGrade) (X Y Z : JordanTKK J D.str) :
    InfoGeometry.Exceptional.leibnizDefect (bracketBilin D)
      (gradeProj (R := R) i X) (gradeProj (R := R) j Y) (gradeProj (R := R) k Z) = 0 := by
  have h_anti := bracketBilin_antisymm D
  cases i <;> cases j <;> cases k <;>
    simp only [gradeProj, LinearMap.comp_apply, projNeg_apply, projZero_apply, projPos_apply]
  · exact defect_neg_neg_neg D X.neg Y.neg Z.neg
  · exact defect_neg_neg_zero D X.neg Y.neg Z.zero
  · exact defect_neg_neg_pos D X.neg Y.neg Z.pos
  · rw [leibnizDefect_swap₂₃ (bracketBilin D) h_anti,
      defect_neg_neg_zero D X.neg Z.neg Y.zero, neg_zero]
  · exact defect_neg_zero_zero D X.neg Y.zero Z.zero
  · exact defect_neg_zero_pos D X.neg Y.zero Z.pos
  · rw [leibnizDefect_swap₂₃ (bracketBilin D) h_anti,
      defect_neg_neg_pos D X.neg Z.neg Y.pos, neg_zero]
  · rw [leibnizDefect_swap₂₃ (bracketBilin D) h_anti,
      defect_neg_zero_pos D X.neg Z.zero Y.pos, neg_zero]
  · exact defect_neg_pos_pos D X.neg Y.pos Z.pos
  · rw [← leibnizDefect_cycle (bracketBilin D) h_anti
        (zeroLM (R := R) X.zero) (negLM (R := R) Y.neg) (negLM (R := R) Z.neg)]
    exact defect_neg_neg_zero D Y.neg Z.neg X.zero
  · rw [leibnizDefect_swap₁₂ (bracketBilin D) h_anti,
      defect_neg_zero_zero D Y.neg X.zero Z.zero, neg_zero]
  · rw [leibnizDefect_swap₁₂ (bracketBilin D) h_anti,
      defect_neg_zero_pos D Y.neg X.zero Z.pos, neg_zero]
  · rw [leibnizDefect_cycle (bracketBilin D) h_anti
        (negLM (R := R) Z.neg) (zeroLM (R := R) X.zero) (zeroLM (R := R) Y.zero)]
    exact defect_neg_zero_zero D Z.neg X.zero Y.zero
  · exact defect_zero_zero_zero D X.zero Y.zero Z.zero
  · exact defect_zero_zero_pos D X.zero Y.zero Z.pos
  · rw [leibnizDefect_cycle (bracketBilin D) h_anti
        (negLM (R := R) Z.neg) (zeroLM (R := R) X.zero) (posLM (R := R) Y.pos)]
    exact defect_neg_zero_pos D Z.neg X.zero Y.pos
  · rw [leibnizDefect_swap₂₃ (bracketBilin D) h_anti,
      defect_zero_zero_pos D X.zero Z.zero Y.pos, neg_zero]
  · exact defect_zero_pos_pos D X.zero Y.pos Z.pos
  · rw [← leibnizDefect_cycle (bracketBilin D) h_anti
        (posLM (R := R) X.pos) (negLM (R := R) Y.neg) (negLM (R := R) Z.neg)]
    exact defect_neg_neg_pos D Y.neg Z.neg X.pos
  · rw [← leibnizDefect_cycle (bracketBilin D) h_anti
        (posLM (R := R) X.pos) (negLM (R := R) Y.neg) (zeroLM (R := R) Z.zero)]
    exact defect_neg_zero_pos D Y.neg Z.zero X.pos
  · rw [leibnizDefect_swap₁₂ (bracketBilin D) h_anti,
      defect_neg_pos_pos D Y.neg X.pos Z.pos, neg_zero]
  · rw [leibnizDefect_swap₁₂ (bracketBilin D) h_anti,
      leibnizDefect_cycle (bracketBilin D) h_anti
        (negLM (R := R) Z.neg) (zeroLM (R := R) Y.zero) (posLM (R := R) X.pos),
      defect_neg_zero_pos D Z.neg Y.zero X.pos, neg_zero]
  · rw [← leibnizDefect_cycle (bracketBilin D) h_anti
        (posLM (R := R) X.pos) (zeroLM (R := R) Y.zero) (zeroLM (R := R) Z.zero)]
    exact defect_zero_zero_pos D Y.zero Z.zero X.pos
  · rw [leibnizDefect_swap₁₂ (bracketBilin D) h_anti,
      defect_zero_pos_pos D Y.zero X.pos Z.pos, neg_zero]
  · rw [leibnizDefect_cycle (bracketBilin D) h_anti
        (negLM (R := R) Z.neg) (posLM (R := R) X.pos) (posLM (R := R) Y.pos)]
    exact defect_neg_pos_pos D Z.neg X.pos Y.pos
  · rw [leibnizDefect_cycle (bracketBilin D) h_anti
        (zeroLM (R := R) Z.zero) (posLM (R := R) X.pos) (posLM (R := R) Y.pos)]
    exact defect_zero_pos_pos D Z.zero X.pos Y.pos
  · exact defect_pos_pos_pos D X.pos Y.pos Z.pos

theorem bracketBilin_leibniz (D : JordanTKKDatum R J) (X Y Z : JordanTKK J D.str) :
    bracketBilin D X (bracketBilin D Y Z) =
      bracketBilin D (bracketBilin D X Y) Z + bracketBilin D Y (bracketBilin D X Z) := by
  have h_def : InfoGeometry.Exceptional.leibnizDefect (bracketBilin D) X Y Z = 0 :=
    InfoGeometry.Exceptional.global_leibniz_of_homogeneous
      (bracketBilin D) (gradeProj (R := R)) (gradeProj_sum (R := R))
      (defect_all_cells D) X Y Z
  dsimp [InfoGeometry.Exceptional.leibnizDefect] at h_def
  have h1 : bracketBilin D X (bracketBilin D Y Z) - bracketBilin D (bracketBilin D X Y) Z =
      bracketBilin D Y (bracketBilin D X Z) := sub_eq_zero.mp h_def
  rw [eq_add_of_sub_eq h1, add_comm]

/-- Constructive `LieRing` structure on `JordanTKK J D.str`. -/
@[instance_reducible]
def lieRing (D : JordanTKKDatum R J) : LieRing (JordanTKK J D.str) where
  toAddCommGroup := inferInstance
  bracket X Y := bracketBilin D X Y
  add_lie X Y Z := by simp
  lie_add X Y Z := by simp
  lie_self X := bracketBilin_self D X
  leibniz_lie X Y Z := bracketBilin_leibniz D X Y Z

/-- Constructive `LieAlgebra R` structure on `JordanTKK J D.str`. -/
@[instance_reducible]
def lieAlgebra (D : JordanTKKDatum R J) :
    @LieAlgebra R (JordanTKK J D.str) _ (lieRing D) :=
  letI : LieRing (JordanTKK J D.str) := lieRing D
  { toModule := inferInstance
    lie_smul := fun r X Y => by
      change bracketBilin D X (r • Y) = r • bracketBilin D X Y
      simp }

section HomogeneousBrackets

variable (D : JordanTKKDatum R J)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The grade-0 submodule `D.str` packaged as a `LieSubalgebra R (Module.End R J)`. -/
def _root_.InfoGeometry.Algebra.JordanTKKDatum.strLieSubalgebra :
    LieSubalgebra R (Module.End R J) where
  toSubmodule := D.str
  lie_mem' hT hU := D.str_lie_mem hT hU

private local instance instLocalLieRing : LieRing (JordanTKK J D.str) := lieRing D
private local instance instLocalLieAlgebra : LieAlgebra R (JordanTKK J D.str) := lieAlgebra D

@[simp] theorem neg_bracket_neg (x₁ x₂ : J) :
    ⁅negLM (R := R) (S := D.str) x₁, negLM (R := R) (S := D.str) x₂⁆ = 0 :=
  bracket_neg_neg D x₁ x₂

@[simp] theorem pos_bracket_pos (y₁ y₂ : J) :
    ⁅posLM (R := R) (S := D.str) y₁, posLM (R := R) (S := D.str) y₂⁆ = 0 :=
  bracket_pos_pos D y₁ y₂

@[simp] theorem zero_bracket_zero (T₁ T₂ : D.str) :
    ⁅zeroLM (R := R) (J := J) T₁, zeroLM (R := R) (J := J) T₂⁆ =
      zeroLM (R := R) (J := J) ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, D.str_lie_mem T₁.2 T₂.2⟩ :=
  bracket_zero_zero D T₁ T₂

@[simp] theorem zero_bracket_neg (T : D.str) (x : J) :
    ⁅zeroLM (R := R) (J := J) T, negLM (R := R) (S := D.str) x⁆ =
      negLM (R := R) (S := D.str) (T.1 x) :=
  bracket_zero_neg D T x

@[simp] theorem neg_bracket_zero (x : J) (T : D.str) :
    ⁅negLM (R := R) (S := D.str) x, zeroLM (R := R) (J := J) T⁆ =
      negLM (R := R) (S := D.str) (-(T.1 x)) :=
  bracket_neg_zero D x T

@[simp] theorem zero_bracket_pos (T : D.str) (y : J) :
    ⁅zeroLM (R := R) (J := J) T, posLM (R := R) (S := D.str) y⁆ =
      posLM (R := R) (S := D.str) (-D.adj T.1 y) :=
  bracket_zero_pos D T y

@[simp] theorem pos_bracket_zero (y : J) (T : D.str) :
    ⁅posLM (R := R) (S := D.str) y, zeroLM (R := R) (J := J) T⁆ =
      posLM (R := R) (S := D.str) (D.adj T.1 y) :=
  bracket_pos_zero D y T

@[simp] theorem neg_bracket_pos (x y : J) :
    ⁅negLM (R := R) (S := D.str) x, posLM (R := R) (S := D.str) y⁆ =
      zeroLM (R := R) (J := J) ⟨tripleD R x y, D.tripleD_mem_str x y⟩ :=
  bracket_neg_pos D x y

@[simp] theorem pos_bracket_neg (y x : J) :
    ⁅posLM (R := R) (S := D.str) y, negLM (R := R) (S := D.str) x⁆ =
      zeroLM (R := R) (J := J) ⟨-tripleD R x y, D.str.neg_mem (D.tripleD_mem_str x y)⟩ :=
  bracket_pos_neg D y x

/-- Canonical Lie-algebra embedding of the grade-0 structure subalgebra into `JordanTKK`. -/
def zeroLieHom : D.strLieSubalgebra →ₗ⁅R⁆ JordanTKK J D.str where
  toFun T := zeroLM (R := R) (J := J) (⟨T.1, T.2⟩ : D.str)
  map_add' T₁ T₂ := by
    change zeroLM (R := R) (J := J) ((⟨T₁.1, T₁.2⟩ : D.str) + ⟨T₂.1, T₂.2⟩) = _
    rw [map_add]
  map_smul' r T := by
    change zeroLM (R := R) (J := J) (r • (⟨T.1, T.2⟩ : D.str)) = _
    rw [map_smul]
    rfl
  map_lie' {T₁ T₂} := by
    change zeroLM (R := R) (J := J) ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, D.str_lie_mem T₁.2 T₂.2⟩ =
      ⁅zeroLM (R := R) (J := J) (⟨T₁.1, T₁.2⟩ : D.str),
        zeroLM (R := R) (J := J) (⟨T₂.1, T₂.2⟩ : D.str)⁆
    exact (zero_bracket_zero D ⟨T₁.1, T₁.2⟩ ⟨T₂.1, T₂.2⟩).symm

theorem zeroLieHom_injective : Function.Injective (zeroLieHom D) := by
  intro T₁ T₂ h
  apply Subtype.ext
  exact congrArg (fun X => X.zero.1) h

end HomogeneousBrackets

end BracketAndJacobi

end JordanTKK

end InfoGeometry.Algebra
