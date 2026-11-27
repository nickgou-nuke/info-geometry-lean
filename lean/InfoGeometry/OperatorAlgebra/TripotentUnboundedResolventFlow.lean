/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.C0GroupGenerator
import InfoGeometry.Core.TripotentIntegerGrading
import InfoGeometry.OperatorAlgebra.TripotentGradeTransport
import InfoGeometry.OperatorAlgebra.TripotentExponentialFlow
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Unbounded Resolvent Flows & Tripotent 5-Grading

This module formalizes Archetype 7:
1. Algebraic resolvent and Cayley transform 5-grade preservation.
2. Domain intertwining equivalent to commutation with a bounded two-sided resolvent.
3. Derivative-based domain intertwining and eigenspace invariance through the
   imported `C0GroupGenerator` interface.
4. Coordinate sequence formulas for the real `ℓ²` block model:
   - Pairwise constant tripotent coefficients.
   - The finitely supported sequence submodule `D_fin`.
   - Weighted skew-symmetric rotation blocks and their pairwise resolvent identity.
   - Rotation formulas preserving the Euclidean norm of each pair.
5. OpenGauss Trap T16 non-commutativity witness.

The actual Hilbert-space density, maximal domain `D_max`, unbounded operator
`K_max`, bounded resolvent and isometric group are proved in
`UnboundedHilbertResolventAndC0GroupWitness`. The companion
`UnboundedHilbertStrongGenerator` proves strong continuity and identifies
`D_max` exactly with the domain of the Hilbert-norm derivative at zero, whose
value is `K_max`. A native partial-adjoint identity is not inferred from the
legacy name of the pairwise skew-symmetry lemma.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow

open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Physics.Algebra

set_option linter.unusedSectionVars false

/-! ### Section 1: Algebraic Resolvent & Cayley 5-Grade Preservation -/

section Algebraic

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem commute_resolvent_of_commute {S K : A} (hK : Commute K S) (u : Aˣ) (hu : (u : A) = 1 - K) :
    Commute (↑u⁻¹ : A) S := by
  have hu_comm : Commute (u : A) S := by
    rw [hu]
    exact Commute.sub_left (Commute.one_left S) hK
  exact Commute.units_inv_left hu_comm

theorem commute_cayley_of_commute {S K : A} (hK : Commute K S) (u : Aˣ) (hu : (u : A) = 1 - K) :
    Commute ((1 + K) * (↑u⁻¹ : A)) S := by
  have h_plus : Commute (1 + K) S := Commute.add_left (Commute.one_left S) hK
  have h_inv := commute_resolvent_of_commute hK u hu
  exact Commute.mul_left h_plus h_inv

theorem left_mul_mem_adGrade_of_commute {S R X : A} (hR : Commute R S) {k : ℤ}
    (hX : X ∈ adGrade S k) : R * X ∈ adGrade S k := by
  rw [mem_adGrade_iff] at hX ⊢
  unfold adOp at hX ⊢
  calc
    S * (R * X) - (R * X) * S = R * (S * X) - R * (X * S) := by
      rw [← mul_assoc, ← mul_assoc, ← hR.eq, mul_assoc R X S]
    _ = R * (S * X - X * S) := by
      rw [mul_sub]
    _ = R * ((k : ℝ) • X) := by
      rw [hX]
    _ = (k : ℝ) • (R * X) := by
      rw [mul_smul_comm]

theorem right_mul_mem_adGrade_of_commute {S R X : A} (hR : Commute R S) {k : ℤ}
    (hX : X ∈ adGrade S k) : X * R ∈ adGrade S k := by
  rw [mem_adGrade_iff] at hX ⊢
  unfold adOp at hX ⊢
  calc
    S * (X * R) - (X * R) * S = (S * X) * R - (X * S) * R := by
      rw [mul_assoc, mul_assoc, hR.eq, ← mul_assoc X S R]
    _ = (S * X - X * S) * R := by
      rw [sub_mul]
    _ = ((k : ℝ) • X) * R := by
      rw [hX]
    _ = (k : ℝ) • (X * R) := by
      rw [smul_mul_assoc]

/-- Algebraic resolvent and Cayley transform commute with S and preserve all five grades. -/
theorem resolvent_and_cayley_commute_and_preserve_fiveGrades
    {S K : A} (hS : S * S * S = S) (hK : Commute K S)
    (u : Aˣ) (hu : (u : A) = 1 - K) :
    let R := (↑u⁻¹ : A)
    let C := (1 + K) * R
    Commute R S ∧
    Commute C S ∧
    (∀ (k : ℤ) (X : A), X ∈ adGrade S k → R * X ∈ adGrade S k ∧ C * X ∈ adGrade S k) ∧
    (∀ (k : FiveGrade) (X : A), X ∈ fiveGradeRange S k → R * X ∈ fiveGradeRange S k ∧ C * X ∈ fiveGradeRange S k) := by
  intro R C
  have hR : Commute R S := commute_resolvent_of_commute hK u hu
  have hC : Commute C S := commute_cayley_of_commute hK u hu
  refine ⟨hR, hC, ?_, ?_⟩
  · intro k X hX
    exact ⟨left_mul_mem_adGrade_of_commute hR hX, left_mul_mem_adGrade_of_commute hC hX⟩
  · intro k X hX
    rw [fiveGradeRange_eq_adGrade hS] at hX ⊢
    exact ⟨left_mul_mem_adGrade_of_commute hR hX, left_mul_mem_adGrade_of_commute hC hX⟩

end Algebraic

/-! ### Section 2: Domain Intertwining and Bounded Resolvent Commutation -/

section KatoTrotter

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

structure ResolventData (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  D_K : Submodule ℝ H
  K : D_K →ₗ[ℝ] H
  R : H →L[ℝ] H
  R_in_domain : ∀ x : H, R x ∈ D_K
  sub_K_R_apply : ∀ x : H, (R x : H) - K ⟨R x, R_in_domain x⟩ = x
  R_sub_K_apply : ∀ (x : H) (hx : x ∈ D_K), R (x - K ⟨x, hx⟩) = x

instance : Inhabited (ResolventData H) where
  default := {
    D_K := ⊤
    K := 0
    R := ContinuousLinearMap.id ℝ H
    R_in_domain := fun _ => Submodule.mem_top
    sub_K_R_apply := by
      intro x
      simp
    R_sub_K_apply := by
      intro x _
      simp
  }

def PreservesDomain (S : H →L[ℝ] H) (D_K : Submodule ℝ H) : Prop :=
  ∀ ⦃x : H⦄, x ∈ D_K → S x ∈ D_K

theorem resolvent_commute_of_unbounded_commute
    (res : ResolventData H) (S : H →L[ℝ] H)
    (h_inv : PreservesDomain S res.D_K)
    (h_comm : ∀ x : res.D_K, S (res.K x) = res.K ⟨S x.1, h_inv x.2⟩) :
    S.comp res.R = res.R.comp S := by
  ext y
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  let x := res.R y
  have hx : x ∈ res.D_K := res.R_in_domain y
  have hsx : S x ∈ res.D_K := h_inv hx
  have h_left : (x : H) - res.K ⟨x, hx⟩ = y := res.sub_K_R_apply y
  have h1 : S y = S ((x : H) - res.K ⟨x, hx⟩) := by
    rw [h_left]
  rw [map_sub, h_comm ⟨x, hx⟩] at h1
  have h2 : res.R (S y) = res.R ((S x : H) - res.K ⟨S x, hsx⟩) := by
    rw [h1]
  rw [res.R_sub_K_apply (S x) hsx] at h2
  exact h2.symm

theorem unbounded_commute_of_resolvent_commute
    (res : ResolventData H) (S : H →L[ℝ] H)
    (hR : S.comp res.R = res.R.comp S) :
    PreservesDomain S res.D_K ∧
    ∀ (h_inv : PreservesDomain S res.D_K) (x : res.D_K),
      S (res.K x) = res.K ⟨S x.1, h_inv x.2⟩ := by
  have hR_apply : ∀ y : H, S (res.R y) = res.R (S y) := by
    intro y
    exact (ContinuousLinearMap.ext_iff.mp hR) y
  have h_inv : PreservesDomain S res.D_K := by
    intro x hx
    let y := (x : H) - res.K ⟨x, hx⟩
    have hy : res.R y = x := res.R_sub_K_apply x hx
    have hsx : S x = res.R (S y) := by
      rw [← hy, hR_apply]
    rw [hsx]
    exact res.R_in_domain (S y)
  refine ⟨h_inv, fun _ x => ?_⟩
  let y := (x.1 : H) - res.K x
  have hy : res.R y = x.1 := res.R_sub_K_apply x.1 x.2
  have hsx : res.R (S y) = S x.1 := by
    rw [← hR_apply, hy]
  have h_sub : (⟨res.R (S y), res.R_in_domain (S y)⟩ : res.D_K) = ⟨S x.1, h_inv x.2⟩ :=
    Subtype.ext hsx
  have hK_eq : res.K ⟨res.R (S y), res.R_in_domain (S y)⟩ = res.K ⟨S x.1, h_inv x.2⟩ :=
    congrArg res.K h_sub
  have h_left := res.sub_K_R_apply (S y)
  rw [hK_eq] at h_left
  have h_sy : S y = S x.1 - S (res.K x) := by
    change S ((x.1 : H) - res.K x) = S x.1 - S (res.K x)
    exact map_sub S x.1 (res.K x)
  rw [hsx, h_sy] at h_left
  have h_eq : res.K ⟨S x.1, h_inv x.2⟩ = S (res.K x) := by
    calc
      res.K ⟨S x.1, h_inv x.2⟩ = S x.1 - (S x.1 - res.K ⟨S x.1, h_inv x.2⟩) := by
        abel
      _ = S x.1 - (S x.1 - S (res.K x)) := by
        rw [h_left]
      _ = S (res.K x) := by
        abel
  exact h_eq.symm

/-- Under the displayed two-sided resolvent identities, domain intertwining
for `K` is equivalent to commutation with its bounded resolvent. -/
theorem unbounded_generator_commute_iff_resolvent_commute
    (res : ResolventData H) (S : H →L[ℝ] H) :
    (∃ (h_inv : PreservesDomain S res.D_K),
      ∀ x : res.D_K, S (res.K x) = res.K ⟨S x.1, h_inv x.2⟩) ↔
    S.comp res.R = res.R.comp S := by
  constructor
  · rintro ⟨h_inv, h_comm⟩
    exact resolvent_commute_of_unbounded_commute res S h_inv h_comm
  · intro hR
    obtain ⟨h_inv, h_comm⟩ := unbounded_commute_of_resolvent_commute res S hR
    exact ⟨h_inv, h_comm h_inv⟩

end KatoTrotter

/-! ### Section 3: Strong generator API

The unchanged `C0GroupGenerator` interface and domain-intertwining theorems
are imported from `InfoGeometry.OperatorAlgebra.C0GroupGenerator`.
The record stores group and generator-domain/derivative laws, with no separate
strong-continuity field. The concrete real ℓ² continuity theorem belongs to
`UnboundedHilbertStrongGenerator`.
-/

/-! ### Section 4: Coordinate Formulas for the Real ℓ² Block Model -/

section ConcreteWitness

abbrev H_lp := lp (fun _ : ℕ => ℝ) 2

/-- The submodule of finitely supported sequences in real ℓ². -/
def D_fin : Submodule ℝ H_lp where
  carrier := {x | ∃ N : ℕ, ∀ n ≥ N, x n = 0}
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  add_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨max Nx Ny, fun n hn => ?_⟩
    have hx_zero := hx n (le_of_max_le_left hn)
    have hy_zero := hy n (le_of_max_le_right hn)
    simp [hx_zero, hy_zero]
  smul_mem' := by
    rintro c x ⟨N, hx⟩
    refine ⟨N, fun n hn => ?_⟩
    simp [hx n hn]

/-- Pairwise constant tripotent scalar coefficient on block m. -/
def s_lp_coeff (m : ℕ) : ℝ :=
  if m % 3 = 0 then 1 else if m % 3 = 1 then -1 else 0

theorem s_lp_coeff_tripotent (m : ℕ) : (s_lp_coeff m)^3 = s_lp_coeff m := by
  dsimp [s_lp_coeff]
  split_ifs <;> ring

/-- Tripotent operator S_lp constant on (2m, 2m+1) coordinate pairs. -/
def S_lp_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  s_lp_coeff (n / 2) * x n

theorem S_lp_constant_on_pairs (m : ℕ) (x : ℕ → ℝ) :
    S_lp_fun x (2 * m) = s_lp_coeff m * x (2 * m) ∧
    S_lp_fun x (2 * m + 1) = s_lp_coeff m * x (2 * m + 1) := by
  constructor
  · dsimp [S_lp_fun]
    have h : (2 * m) / 2 = m := by omega
    rw [h]
  · dsimp [S_lp_fun]
    have h : (2 * m + 1) / 2 = m := by omega
    rw [h]

/-- Pointwise tripotence of S_lp on all sequences. -/
theorem S_lp_tripotent (x : ℕ → ℝ) (n : ℕ) :
    S_lp_fun (S_lp_fun (S_lp_fun x)) n = S_lp_fun x n := by
  dsimp [S_lp_fun]
  have h3 := s_lp_coeff_tripotent (n / 2)
  calc
    s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * (s_lp_coeff (n / 2) * x n)) =
      (s_lp_coeff (n / 2))^3 * x n := by
        ring
    _ = s_lp_coeff (n / 2) * x n := by
      rw [h3]

/-- Coordinate formula for the weighted skew-symmetric rotation blocks. -/
def K_unb_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n % 2 = 0 then
    -(((n / 2 : ℕ) + 1 : ℝ) * x (n + 1))
  else
    (((n / 2 : ℕ) + 1 : ℝ) * x (n - 1))

theorem K_unb_even (m : ℕ) (x : ℕ → ℝ) :
    K_unb_fun x (2 * m) = -((m + 1 : ℝ) * x (2 * m + 1)) := by
  dsimp [K_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
  · omega

theorem K_unb_odd (m : ℕ) (x : ℕ → ℝ) :
    K_unb_fun x (2 * m + 1) = (m + 1 : ℝ) * x (2 * m) := by
  dsimp [K_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]

theorem S_lp_K_unb_commute_on_pairs (m : ℕ) (x : ℕ → ℝ) :
    S_lp_fun (K_unb_fun x) (2 * m) = K_unb_fun (S_lp_fun x) (2 * m) ∧
    S_lp_fun (K_unb_fun x) (2 * m + 1) = K_unb_fun (S_lp_fun x) (2 * m + 1) := by
  obtain ⟨hS0, hS1⟩ := S_lp_constant_on_pairs m (K_unb_fun x)
  obtain ⟨hSx0, hSx1⟩ := S_lp_constant_on_pairs m x
  constructor
  · rw [hS0, K_unb_even, K_unb_even, hSx1]
    ring
  · rw [hS1, K_unb_odd, K_unb_odd, hSx0]
    ring

/-- Pairwise skew-symmetry identity, retaining its historical public name. -/
theorem K_unb_block_skew_adjoint (m : ℕ) (x y : ℕ → ℝ) :
    x (2 * m) * K_unb_fun y (2 * m) + x (2 * m + 1) * K_unb_fun y (2 * m + 1) +
    K_unb_fun x (2 * m) * y (2 * m) + K_unb_fun x (2 * m + 1) * y (2 * m + 1) = 0 := by
  rw [K_unb_even, K_unb_odd, K_unb_even, K_unb_odd]
  ring

/-- Coordinate resolvent formula; `R_unb_inverts_I_sub_K` proves its pairwise inverse identity. -/
noncomputable def R_unb_fun (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  let m := n / 2
  let d := 1 + (m + 1 : ℝ)^2
  if n % 2 = 0 then
    (x (2 * m) - (m + 1 : ℝ) * x (2 * m + 1)) / d
  else
    ((m + 1 : ℝ) * x (2 * m) + x (2 * m + 1)) / d

theorem R_unb_even (m : ℕ) (x : ℕ → ℝ) :
    R_unb_fun x (2 * m) = (x (2 * m) - (m + 1 : ℝ) * x (2 * m + 1)) / (1 + (m + 1 : ℝ)^2) := by
  dsimp [R_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
  · omega

theorem R_unb_odd (m : ℕ) (x : ℕ → ℝ) :
    R_unb_fun x (2 * m + 1) = ((m + 1 : ℝ) * x (2 * m) + x (2 * m + 1)) / (1 + (m + 1 : ℝ)^2) := by
  dsimp [R_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]

theorem R_unb_inverts_I_sub_K (m : ℕ) (x : ℕ → ℝ) :
    let y := R_unb_fun x
    y (2 * m) - K_unb_fun y (2 * m) = x (2 * m) ∧
    y (2 * m + 1) - K_unb_fun y (2 * m + 1) = x (2 * m + 1) := by
  intro y
  have hd : 1 + (m + 1 : ℝ)^2 ≠ 0 := by positivity
  constructor
  · dsimp only [y]
    rw [R_unb_even, K_unb_even, R_unb_odd]
    field_simp [hd]
    ring
  · dsimp only [y]
    rw [R_unb_odd, K_unb_odd, R_unb_even]
    field_simp [hd]
    ring

/-- Coordinate rotations, with pairwise Euclidean norm preservation proved below. -/
noncomputable def U_unb_fun (t : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  let m := n / 2
  let theta := (m + 1 : ℝ) * t
  if n % 2 = 0 then
    Real.cos theta * x (2 * m) - Real.sin theta * x (2 * m + 1)
  else
    Real.sin theta * x (2 * m) + Real.cos theta * x (2 * m + 1)

theorem U_unb_even (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    U_unb_fun t x (2 * m) =
    Real.cos ((m + 1 : ℝ) * t) * x (2 * m) - Real.sin ((m + 1 : ℝ) * t) * x (2 * m + 1) := by
  dsimp [U_unb_fun]
  split_ifs with h
  · have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
  · omega

theorem U_unb_odd (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    U_unb_fun t x (2 * m + 1) =
    Real.sin ((m + 1 : ℝ) * t) * x (2 * m) + Real.cos ((m + 1 : ℝ) * t) * x (2 * m + 1) := by
  dsimp [U_unb_fun]
  split_ifs with h
  · omega
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]

theorem U_unb_preserves_pair_norm_sq (m : ℕ) (t : ℝ) (x : ℕ → ℝ) :
    (U_unb_fun t x (2 * m))^2 + (U_unb_fun t x (2 * m + 1))^2 =
    (x (2 * m))^2 + (x (2 * m + 1))^2 := by
  rw [U_unb_even, U_unb_odd]
  set c := Real.cos ((m + 1 : ℝ) * t)
  set s := Real.sin ((m + 1 : ℝ) * t)
  set u := x (2 * m)
  set v := x (2 * m + 1)
  have hcs : c^2 + s^2 = 1 := Real.cos_sq_add_sin_sq ((m + 1 : ℝ) * t)
  calc (c * u - s * v)^2 + (s * u + c * v)^2
    _ = (c^2 + s^2) * (u^2 + v^2) := by
      ring
    _ = 1 * (u^2 + v^2) := by
      rw [hcs]
    _ = u^2 + v^2 := by
      ring

/-- Standard coordinate test vectors `e_{2m}` in the real ℓ² carrier. -/
def basisTestVec (m : ℕ) : H_lp :=
  lp.single 2 (2 * m) 1

theorem basisTestVec_mem_D_fin (m : ℕ) : basisTestVec m ∈ D_fin := by
  refine ⟨2 * m + 1, fun n hn => ?_⟩
  unfold basisTestVec
  rw [lp.single_apply_ne]
  omega

/-- Arithmetic unboundedness of the natural frequencies, retaining the
historical theorem name. The actual Hilbert norm-unboundedness statement is
`UnboundedHilbertResolventAndC0GroupWitness.K_max_is_unbounded`. -/
theorem K_unb_is_unbounded :
    ¬ ∃ C : ℝ, ∀ m : ℕ, (m : ℝ) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨m, hm⟩ := exists_nat_gt C
  exact not_lt_of_ge (hC m) hm

end ConcreteWitness

/-! ### Section 5: OpenGauss T16 Non-Commutativity Witness -/

section OpenGaussT16

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- OpenGauss Trap 16 Non-commutativity witness: any nonzero grade-1 element fails to commute with S. -/
theorem tripotent_adGrade_one_noncommuting {S X : A}
    (hX : X ∈ adGrade S 1) (hne : X ≠ 0) :
    S * X ≠ X * S := by
  intro h_comm
  have h_sub : S * X - X * S = 0 := sub_eq_zero.mpr h_comm
  have h_eigen := mem_adGrade_iff.mp hX
  dsimp [adOp] at h_eigen
  push_cast at h_eigen
  rw [one_smul] at h_eigen
  rw [h_sub] at h_eigen
  exact hne h_eigen.symm

abbrev RealMatrix := Matrix (Fin 2) (Fin 2) ℝ
def matJ : RealMatrix := !![0, -1; 1, 0]
def matSigma : RealMatrix := !![1, 0; 0, -1]

/-- Explicit matrix non-commutativity witness on Fin 2 certifying OpenGauss Trap 16. -/
theorem mat2_skew_symm_noncommuting :
    matJ * matSigma ≠ matSigma * matJ := by
  intro h
  have hh := congrArg (fun a : RealMatrix => a 0 1) h
  norm_num [matJ, matSigma, Matrix.mul_apply, Fin.sum_univ_two] at hh

end OpenGaussT16

end InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow
