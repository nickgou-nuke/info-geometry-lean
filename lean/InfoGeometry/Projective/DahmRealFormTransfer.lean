/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.DahmKleinLieIsomorphism

/-!
# Real forms of `sl₄(ℂ) ≅ so₆(ℂ)`: generic transfer theorem

Let `g ⊂ sl₄(ℂ)` be a real Lie subalgebra, `E ∈ GL₆(ℂ)` (with explicit inverse
`E'`), and `Q` a real symmetric matrix with `Eᵀ G E = Q` (`G = kleinGram`).
Assume

* (**realness**) for `X ∈ g`, every entry of `E' (Λ²X) E` is real, and
* (**surjectivity datum**) for every real `N` with `Nᵀ Q = Q (-N)`,
  `psi (E N E') ∈ g`.

Then `X ↦ Re (E' (Λ²X) E)` is an isomorphism of real Lie algebras
`g ≃ₗ⁅ℝ⁆ so(Q)` (`realFormEquiv`).  The individual real forms
(`su(4) ≅ so(6)`, `su(2,2) ≅ so(4,2)`, `su*(4) ≅ so(5,1)`) supply `E`, `Q` and the
two hypotheses from CAS-generated certificates in a separate module.
-/

namespace InfoGeometry.Projective.DahmRealFormTransfer

open Matrix LieAlgebra
open InfoGeometry.Projective.DahmKleinLieIsomorphism

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The spin-half commutator law forces an explicit noncommuting pair.  The
nonzero diagonal entry of `2 J₀` rules out commuting raising and lowering
matrices. -/
theorem dahmRealForm_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a := by
  refine ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
    _root_.InfoGeometry.Algebra.FiniteSpin.J_minus, ?_⟩
  intro h
  have hcomm : _root_.InfoGeometry.Algebra.FiniteSpin.comm
      _root_.InfoGeometry.Algebra.FiniteSpin.J_plus
      _root_.InfoGeometry.Algebra.FiniteSpin.J_minus = 0 := by
    unfold _root_.InfoGeometry.Algebra.FiniteSpin.comm
    rw [h]
    simp
  rw [_root_.InfoGeometry.Algebra.FiniteSpin.comm_J_plus_J_minus] at hcomm
  have h00 := congrFun (congrFun hcomm 0) 0
  norm_num [_root_.InfoGeometry.Algebra.FiniteSpin.J_zero] at h00

/-- Entrywise real part. -/
def reM {n : Type*} (A : Matrix n n ℂ) : Matrix n n ℝ := A.map Complex.re

/-- Entrywise inclusion `ℝ → ℂ`. -/
def ofRealM {n : Type*} (A : Matrix n n ℝ) : Matrix n n ℂ := A.map (fun r : ℝ => (r : ℂ))

/-- All entries are real. -/
def IsRealM {n : Type*} (A : Matrix n n ℂ) : Prop := ∀ a b, (A a b).im = 0

theorem ofRealM_reM {n : Type*} {A : Matrix n n ℂ} (h : IsRealM A) : ofRealM (reM A) = A := by
  ext a b; apply Complex.ext <;> simp [ofRealM, reM, h a b]

theorem reM_ofRealM {n : Type*} (A : Matrix n n ℝ) : reM (ofRealM A) = A := by
  ext a b; simp [ofRealM, reM]

theorem reM_mul_of_real {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hA : IsRealM A)
    (hB : IsRealM B) : reM (A * B) = reM A * reM B := by
  ext a b
  simp only [reM, Matrix.map_apply, Matrix.mul_apply, Complex.re_sum, Complex.mul_re]
  have hAi : ∀ i, (A a i).im = 0 := fun i => hA a i
  have hBi : ∀ i, (B i b).im = 0 := fun i => hB i b
  simp_rw [hAi, hBi]
  simp

theorem isRealM_mul {n : Type*} [Fintype n] {A B : Matrix n n ℂ} (hA : IsRealM A)
    (hB : IsRealM B) : IsRealM (A * B) := by
  intro a b
  simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im]
  have hAi : ∀ i, (A a i).im = 0 := fun i => hA a i
  have hBi : ∀ i, (B i b).im = 0 := fun i => hB i b
  simp_rw [hAi, hBi]
  simp

theorem isRealM_sub {n : Type*} {A B : Matrix n n ℂ} (hA : IsRealM A) (hB : IsRealM B) :
    IsRealM (A - B) := fun a b => by simp [hA a b, hB a b]

theorem reM_sub {n : Type*} (A B : Matrix n n ℂ) : reM (A - B) = reM A - reM B := by
  ext a b; simp [reM]

theorem reM_add {n : Type*} (A B : Matrix n n ℂ) : reM (A + B) = reM A + reM B := by
  ext a b; simp [reM]

theorem reM_real_smul {n : Type*} (r : ℝ) (A : Matrix n n ℂ) : reM (r • A) = r • reM A := by
  ext a b; simp [reM, Complex.smul_re]

section Transfer

variable {g : LieSubalgebra ℝ (Matrix (Fin 4) (Fin 4) ℂ)}
  {E E' : Matrix (Fin 6) (Fin 6) ℂ} {Q : Matrix (Fin 6) (Fin 6) ℝ}


/-- The transfer map `X ↦ Re (E' Λ²X E)`. -/
def phi (E E' : Matrix (Fin 6) (Fin 6) ℂ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 6) (Fin 6) ℝ := reM (E' * lam2 X * E)

theorem conj_lie (E_mul : E * E' = 1) (X Y : Matrix (Fin 4) (Fin 4) ℂ) :
    E' * lam2 (X * Y - Y * X) * E =
      (E' * lam2 X * E) * (E' * lam2 Y * E) -
        (E' * lam2 Y * E) * (E' * lam2 X * E) := by
  rw [lam2_lie]
  have h : ∀ A B : Matrix (Fin 6) (Fin 6) ℂ,
      (E' * A * E) * (E' * B * E) = E' * (A * B) * E := by
    intro A B
    calc (E' * A * E) * (E' * B * E) = E' * A * (E * E') * B * E := by
          simp only [Matrix.mul_assoc]
      _ = E' * (A * B) * E := by rw [E_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [h, h, Matrix.mul_sub, Matrix.sub_mul]

theorem phi_lie (E_mul : E * E' = 1) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E))
    {X Y : Matrix (Fin 4) (Fin 4) ℂ} (hX : X ∈ g) (hY : Y ∈ g) :
    phi E E' (X * Y - Y * X) = phi E E' X * phi E E' Y - phi E E' Y * phi E E' X := by
  unfold phi
  rw [conj_lie E_mul, reM_sub, reM_mul_of_real (real X hX) (real Y hY),
    reM_mul_of_real (real Y hY) (real X hX)]

theorem phi_mem (E_mul : E * E' = 1) (congr : Eᵀ * kleinGram * E = ofRealM Q)
    (trace_free : ∀ X ∈ g, X.trace = 0) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E))
    {X : Matrix (Fin 4) (Fin 4) ℂ} (hX : X ∈ g) :
    (phi E E' X)ᵀ * Q = Q * (-phi E E' X) := by
  have hskew := lam2_isSkewAdjoint (trace_free X hX)
  unfold Matrix.IsSkewAdjoint Matrix.IsAdjointPair at hskew
  -- complex identity: (E' L E)ᵀ (Eᵀ G E) = (Eᵀ G E) (-(E' L E))
  have hEt : E'ᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, E_mul, Matrix.transpose_one]
  have hc : (E' * lam2 X * E)ᵀ * (Eᵀ * kleinGram * E) =
      (Eᵀ * kleinGram * E) * (-(E' * lam2 X * E)) := by
    calc (E' * lam2 X * E)ᵀ * (Eᵀ * kleinGram * E)
        = Eᵀ * (lam2 X)ᵀ * (E'ᵀ * Eᵀ) * kleinGram * E := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Eᵀ * ((lam2 X)ᵀ * kleinGram) * E := by
          rw [hEt, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Eᵀ * (kleinGram * -(lam2 X)) * E := by rw [hskew]
      _ = (Eᵀ * kleinGram * E) * (-(E' * lam2 X * E)) := by
          rw [show Eᵀ * kleinGram * E * -(E' * lam2 X * E) =
              Eᵀ * kleinGram * (E * E') * -(lam2 X) * E by
                simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]]
          rw [E_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [congr] at hc
  have hr := real X hX
  have hT : IsRealM (E' * lam2 X * E)ᵀ := fun a b => hr b a
  have hQ : IsRealM (ofRealM Q) := fun a b => by simp [ofRealM]
  have hN : IsRealM (-(E' * lam2 X * E)) := fun a b => by simp [hr a b]
  have := congrArg reM hc
  rw [reM_mul_of_real hT hQ, reM_mul_of_real hQ hN, reM_ofRealM] at this
  have htranspose : reM (E' * lam2 X * E)ᵀ = (reM (E' * lam2 X * E))ᵀ := by
    ext a b
    rfl
  rw [htranspose] at this
  have hneg : reM (-(E' * lam2 X * E)) = -(reM (E' * lam2 X * E)) := by
    ext a b
    simp [reM]
  rw [hneg, Matrix.mul_neg] at this
  simpa [phi] using this

/-- The transfer as a Lie algebra homomorphism `g → so(Q)`. -/
def phiHom (E_mul : E * E' = 1) (congr : Eᵀ * kleinGram * E = ofRealM Q)
    (trace_free : ∀ X ∈ g, X.trace = 0) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E)) :
    g →ₗ⁅ℝ⁆ skewAdjointMatricesLieSubalgebra Q where
  toFun X := ⟨phi E E' X, by
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    exact phi_mem E_mul congr trace_free real X.2⟩
  map_add' X Y := Subtype.ext (by
    show reM (E' * lam2 (X.val + Y.val) * E) = reM (E' * lam2 X.val * E) +
      reM (E' * lam2 Y.val * E)
    rw [lam2_add, Matrix.mul_add, Matrix.add_mul, reM_add])
  map_smul' r X := Subtype.ext (by
    show reM (E' * lam2 (r • X.val) * E) = r • reM (E' * lam2 X.val * E)
    have : lam2 (r • X.val) = r • lam2 X.val := by
      rw [show (r • X.val) = ((r : ℂ) • X.val) by ext a b; simp [Complex.real_smul]]
      rw [lam2_smul]; ext a b; simp [Complex.real_smul]
    rw [this, Matrix.mul_smul, Matrix.smul_mul, reM_real_smul])
  map_lie' {X Y} := Subtype.ext (by
    show phi E E' (X.val * Y.val - Y.val * X.val) = phi E E' X.val * phi E E' Y.val - phi E E' Y.val * phi E E' X.val
    exact phi_lie E_mul real X.2 Y.2)

theorem phiHom_injective (E_mul : E * E' = 1) (congr : Eᵀ * kleinGram * E = ofRealM Q)
    (trace_free : ∀ X ∈ g, X.trace = 0) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E)) :
    Function.Injective (phiHom E_mul congr trace_free real) := by
  intro X Y h
  have h' : phi E E' X.val = phi E E' Y.val := congrArg Subtype.val h
  have hX := ofRealM_reM (real X.val X.2)
  have hY := ofRealM_reM (real Y.val Y.2)
  have hc : E' * lam2 X.val * E = E' * lam2 Y.val * E := by
    rw [← hX, ← hY]; exact congrArg ofRealM h'
  have hl : lam2 X.val = lam2 Y.val := by
    have := congrArg (fun A => E * A * E') hc
    simp only [← Matrix.mul_assoc, E_mul, Matrix.one_mul] at this
    simpa [Matrix.mul_assoc, E_mul] using this
  exact Subtype.ext (by rw [← psi_lam2 X.val, ← psi_lam2 Y.val, hl])

theorem phiHom_surjective (E_mul : E * E' = 1) (E'_mul : E' * E = 1)
    (congr : Eᵀ * kleinGram * E = ofRealM Q)
    (trace_free : ∀ X ∈ g, X.trace = 0) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E))
    (surj : ∀ N : Matrix (Fin 6) (Fin 6) ℝ, Nᵀ * Q = Q * (-N) → psi (E * ofRealM N * E') ∈ g) :
    Function.Surjective (phiHom E_mul congr trace_free real) := by
  rintro ⟨N, hN⟩
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at hN
  have hmem := surj N hN
  refine ⟨⟨psi (E * ofRealM N * E'), hmem⟩, Subtype.ext ?_⟩
  show reM (E' * lam2 (psi (E * ofRealM N * E')) * E) = N
  -- `E N E'` is Klein-skew, so `lam2 (psi _) = E N E'`
  have hskew : (E * ofRealM N * E')ᵀ * kleinGram = kleinGram * (-(E * ofRealM N * E')) := by
    have hNc : (ofRealM N)ᵀ * ofRealM Q = ofRealM Q * (-(ofRealM N)) := by
      have := congrArg ofRealM hN
      convert this using 1 <;> ext a b <;>
        simp [ofRealM, Matrix.mul_apply, Matrix.transpose_apply, Complex.ofReal_sum]
    have hG : kleinGram = E'ᵀ * ofRealM Q * E' := by
      rw [← congr]
      have hEt : E'ᵀ * Eᵀ = 1 := by rw [← Matrix.transpose_mul, E_mul, Matrix.transpose_one]
      simp only [← Matrix.mul_assoc, hEt, Matrix.one_mul]
      rw [Matrix.mul_assoc, E_mul, Matrix.mul_one]
    rw [hG]
    calc (E * ofRealM N * E')ᵀ * (E'ᵀ * ofRealM Q * E')
        = E'ᵀ * ((ofRealM N)ᵀ * (Eᵀ * E'ᵀ) * ofRealM Q) * E' := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = E'ᵀ * ((ofRealM N)ᵀ * ofRealM Q) * E' := by
          rw [show Eᵀ * E'ᵀ = 1 by rw [← Matrix.transpose_mul, E'_mul, Matrix.transpose_one],
            Matrix.mul_one]
      _ = E'ᵀ * (ofRealM Q * (-(ofRealM N))) * E' := by rw [hNc]
      _ = E'ᵀ * ofRealM Q * E' * (-(E * ofRealM N * E')) := by
          rw [show E'ᵀ * ofRealM Q * E' * -(E * ofRealM N * E') =
              E'ᵀ * ofRealM Q * (E' * E) * -(ofRealM N) * E' by
                simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]]
          rw [E'_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [(lam2_psi_of_skewAdjoint hskew).1]
  simp only [← Matrix.mul_assoc, E'_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, E'_mul, Matrix.mul_one, reM_ofRealM]

/-- **The real form `g` is isomorphic to `so(Q)`.** -/
noncomputable def realFormEquiv (E_mul : E * E' = 1) (E'_mul : E' * E = 1)
    (congr : Eᵀ * kleinGram * E = ofRealM Q)
    (trace_free : ∀ X ∈ g, X.trace = 0) (real : ∀ X ∈ g, IsRealM (E' * lam2 X * E))
    (surj : ∀ N : Matrix (Fin 6) (Fin 6) ℝ, Nᵀ * Q = Q * (-N) → psi (E * ofRealM N * E') ∈ g) :
    g ≃ₗ⁅ℝ⁆ skewAdjointMatricesLieSubalgebra Q :=
  LieEquiv.ofBijective (phiHom E_mul congr trace_free real)
    ⟨phiHom_injective E_mul congr trace_free real,
     phiHom_surjective E_mul E'_mul congr trace_free real surj⟩

end Transfer

end InfoGeometry.Projective.DahmRealFormTransfer
