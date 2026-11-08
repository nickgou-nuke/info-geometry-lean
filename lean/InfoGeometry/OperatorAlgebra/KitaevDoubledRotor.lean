/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.AnticommutingBalance

/-!
# Finite doubled real matrix rotors

The anti-commuting block matrices are actual `Matrix` values. Their square identity
holds for every real matrix. The continuous cancellation paths require, explicitly,
that the input is skew and has square `-1`. No infinite stabilization or topological
classification is inferred from these finite constructions.
-/

namespace InfoGeometry.OperatorAlgebra.KitaevDoubledRotor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The off-diagonal doubling of a real matrix. -/
def offDiagonal (A : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks 0 A A 0

omit [Fintype ι] [DecidableEq ι] in
theorem offDiagonal_smul (c : ℝ) (A : Matrix ι ι ℝ) :
    offDiagonal (c • A) = c • offDiagonal A := by
  simp only [offDiagonal, fromBlocks_smul, smul_zero]

/-- A matrix and its negative on the two diagonal blocks. -/
def oppositeDouble (A : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks A 0 0 (-A)

/-- The standard skew complex structure on the doubled real coordinate space. -/
def skewSwap (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks 0 1 (-1) 0

theorem offDiagonal_anticommutes (A : Matrix ι ι ℝ) :
    offDiagonal A * skewSwap ι + skewSwap ι * offDiagonal A = 0 := by
  simp [offDiagonal, skewSwap, fromBlocks_multiply, fromBlocks_add]

theorem oppositeDouble_anticommutes (A : Matrix ι ι ℝ) :
    oppositeDouble A * skewSwap ι + skewSwap ι * oppositeDouble A = 0 := by
  simp [oppositeDouble, skewSwap, fromBlocks_multiply, fromBlocks_add]

theorem offDiagonal_square (A : Matrix ι ι ℝ) :
    offDiagonal A * offDiagonal A = fromBlocks (A * A) 0 0 (A * A) := by
  simp [offDiagonal, fromBlocks_multiply]

theorem oppositeDouble_square (A : Matrix ι ι ℝ) :
    oppositeDouble A * oppositeDouble A = fromBlocks (A * A) 0 0 (A * A) := by
  simp [oppositeDouble, fromBlocks_multiply]

@[simp] theorem skewSwap_square :
    skewSwap ι * skewSwap ι = -(1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  have h := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => -M)
    (fromBlocks_one (α := ℝ) (l := ι) (m := ι))
  simp only [skewSwap, fromBlocks_multiply, mul_neg, neg_mul, one_mul,
    zero_mul, mul_zero, add_zero, zero_add]
  simpa only [fromBlocks_neg, neg_zero] using h

omit [Fintype ι] [DecidableEq ι] in
theorem offDiagonal_transpose (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    (offDiagonal A)ᵀ = -offDiagonal A := by
  simp [offDiagonal, fromBlocks_transpose, hA, fromBlocks_neg]

omit [Fintype ι] [DecidableEq ι] in
theorem oppositeDouble_transpose (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    (oppositeDouble A)ᵀ = -oppositeDouble A := by
  simp [oppositeDouble, fromBlocks_transpose, hA, fromBlocks_neg]

@[simp] theorem skewSwap_transpose : (skewSwap ι)ᵀ = -skewSwap ι := by
  simp [skewSwap, fromBlocks_transpose, fromBlocks_neg]

/-- The exact unnormalized square: its second term moves the negative square toward `1`. -/
theorem offDiagonal_weighted_square (A : Matrix ι ι ℝ) (c s : ℝ) :
    (c • offDiagonal A + s • skewSwap ι) ^ 2 =
      c ^ 2 • fromBlocks (A * A) 0 0 (A * A) -
        s ^ 2 • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [InfoGeometry.Algebra.AnticommutingBalance.weighted_square
    (offDiagonal A) (skewSwap ι) c s (offDiagonal_anticommutes A)]
  simp [offDiagonal_square, sub_eq_add_neg]

theorem oppositeDouble_weighted_square (A : Matrix ι ι ℝ) (c s : ℝ) :
    (c • oppositeDouble A + s • skewSwap ι) ^ 2 =
      c ^ 2 • fromBlocks (A * A) 0 0 (A * A) -
        s ^ 2 • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [InfoGeometry.Algebra.AnticommutingBalance.weighted_square
    (oppositeDouble A) (skewSwap ι) c s (oppositeDouble_anticommutes A)]
  simp [oppositeDouble_square, sub_eq_add_neg]

theorem offDiagonal_square_of_normalized (A : Matrix ι ι ℝ) (hA : A * A = -1) :
    offDiagonal A * offDiagonal A = -1 := by
  rw [offDiagonal_square, hA]
  have h := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => -M)
    (fromBlocks_one (α := ℝ) (l := ι) (m := ι))
  simpa only [fromBlocks_neg, neg_zero] using h

theorem oppositeDouble_square_of_normalized (A : Matrix ι ι ℝ) (hA : A * A = -1) :
    oppositeDouble A * oppositeDouble A = -1 := by
  rw [oppositeDouble_square, hA]
  have h := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => -M)
    (fromBlocks_one (α := ℝ) (l := ι) (m := ι))
  simpa only [fromBlocks_neg, neg_zero] using h

/-- The native subtype of normalized skew real matrices, with its induced topology. -/
abbrev NormalizedSkew (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {A : Matrix ι ι ℝ // Aᵀ = -A ∧ A * A = -1}

/-- Cosine-sine interpolation between two fixed matrices. -/
noncomputable def interpolate (A B : Matrix ι ι ℝ) (θ : ℝ) : Matrix ι ι ℝ :=
  Real.cos θ • A + Real.sin θ • B

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem interpolate_zero (A B : Matrix ι ι ℝ) : interpolate A B 0 = A := by
  simp [interpolate]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem interpolate_half_pi (A B : Matrix ι ι ℝ) :
    interpolate A B (Real.pi / 2) = B := by
  simp [interpolate]

omit [Fintype ι] [DecidableEq ι] in
theorem interpolate_transpose (A B : Matrix ι ι ℝ)
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) (θ : ℝ) :
    (interpolate A B θ)ᵀ = -interpolate A B θ := by
  simp [interpolate, hA, hB, add_comm]

theorem interpolate_square (A B : Matrix ι ι ℝ)
    (hAB : A * B + B * A = 0) (hA : A * A = -1) (hB : B * B = -1) (θ : ℝ) :
    interpolate A B θ * interpolate A B θ = -1 := by
  have h := InfoGeometry.Algebra.AnticommutingBalance.weighted_square
    A B (Real.cos θ) (Real.sin θ) hAB
  rw [hA, hB, ← add_smul, Real.cos_sq_add_sin_sq, one_smul] at h
  simpa only [interpolate, pow_two] using h

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_interpolate (A B : Matrix ι ι ℝ) :
    Continuous (interpolate A B) := by
  exact (Real.continuous_cos.smul continuous_const).add
    (Real.continuous_sin.smul continuous_const)

/-- A genuine path of normalized skew matrices between anti-commuting endpoints. -/
noncomputable def normalizedPath (A B : NormalizedSkew ι)
    (hAB : A.val * B.val + B.val * A.val = 0) : Path A B where
  toFun t := ⟨interpolate A.val B.val (Real.pi / 2 * (t : ℝ)),
    interpolate_transpose A.val B.val A.property.1 B.property.1 _,
    interpolate_square A.val B.val hAB A.property.2 B.property.2 _⟩
  continuous_toFun :=
    ((continuous_interpolate A.val B.val).comp
      (continuous_const.mul continuous_subtype_val)).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [interpolate]
  target' := by
    apply Subtype.ext
    simp [interpolate]

/-- The standard endpoint belongs to the normalized skew space. -/
def normalizedSwap (ι : Type*) [Fintype ι] [DecidableEq ι] :
    NormalizedSkew (ι ⊕ ι) :=
  ⟨skewSwap ι, skewSwap_transpose, skewSwap_square⟩

/-- Off-diagonal doubling preserves the normalized skew conditions. -/
def normalizedOffDiagonal (A : NormalizedSkew ι) : NormalizedSkew (ι ⊕ ι) :=
  ⟨offDiagonal A.val, offDiagonal_transpose A.val A.property.1,
    offDiagonal_square_of_normalized A.val A.property.2⟩

/-- Opposite diagonal doubling preserves the normalized skew conditions. -/
def normalizedOppositeDouble (A : NormalizedSkew ι) : NormalizedSkew (ι ⊕ ι) :=
  ⟨oppositeDouble A.val, oppositeDouble_transpose A.val A.property.1,
    oppositeDouble_square_of_normalized A.val A.property.2⟩

/-- Continuous normalized cancellation from the actual off-diagonal double to the standard one. -/
noncomputable def offDiagonalPath (A : NormalizedSkew ι) :
    Path (normalizedOffDiagonal A) (normalizedSwap ι) :=
  normalizedPath (normalizedOffDiagonal A) (normalizedSwap ι)
    (offDiagonal_anticommutes A.val)

/-- Continuous normalized cancellation of `diag(A,-A)` to the standard complex structure. -/
noncomputable def cancellationPath (A : NormalizedSkew ι) :
    Path (normalizedOppositeDouble A) (normalizedSwap ι) :=
  normalizedPath (normalizedOppositeDouble A) (normalizedSwap ι)
    (oppositeDouble_anticommutes A.val)

/-- The unnormalized block Hadamard matrix. -/
def hadamardBlocks (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks 1 1 1 (-1)

/-- The orthogonal, normalized real Hadamard matrix. -/
noncomputable def hadamard (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  (1 / Real.sqrt 2) • hadamardBlocks ι

theorem hadamardBlocks_square :
    hadamardBlocks ι * hadamardBlocks ι =
      (2 : ℝ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  simp only [hadamardBlocks, fromBlocks_multiply, mul_neg, neg_mul, neg_neg,
    one_mul, add_neg_cancel]
  have h := congrArg (fun M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ => (2 : ℝ) • M)
    (fromBlocks_one (α := ℝ) (l := ι) (m := ι))
  simpa only [two_smul, fromBlocks_add, add_zero] using h

theorem hadamardBlocks_conjugation (A : Matrix ι ι ℝ) :
    hadamardBlocks ι * oppositeDouble A * hadamardBlocks ι =
      (2 : ℝ) • offDiagonal A := by
  simp [hadamardBlocks, oppositeDouble, offDiagonal, fromBlocks_multiply,
    two_smul, fromBlocks_add]

private theorem hadamard_scale :
    (1 / Real.sqrt 2) * (1 / Real.sqrt 2) * 2 = (1 : ℝ) := by
  rw [div_mul_div_comm]
  norm_num [← pow_two, Real.sq_sqrt]

@[simp] theorem hadamard_transpose : (hadamard ι)ᵀ = hadamard ι := by
  simp [hadamard, hadamardBlocks, fromBlocks_transpose]

theorem hadamard_square :
    hadamard ι * hadamard ι = (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  simp only [hadamard, smul_mul_smul, hadamardBlocks_square, smul_smul,
    hadamard_scale, one_smul]

theorem hadamard_orthogonal :
    (hadamard ι)ᵀ * hadamard ι = 1 ∧ hadamard ι * (hadamard ι)ᵀ = 1 := by
  simp only [hadamard_transpose, hadamard_square, and_self]

/-- The actual orthogonal change of basis sends `diag(A,-A)` to the off-diagonal double. -/
theorem hadamard_conjugation (A : Matrix ι ι ℝ) :
    hadamard ι * oppositeDouble A * hadamard ι = offDiagonal A := by
  simp only [hadamard]
  rw [smul_mul_assoc, smul_mul_smul, hadamardBlocks_conjugation,
    smul_smul, hadamard_scale, one_smul]

/-- These full doubled matrices really fail to commute whenever a coordinate exists. -/
theorem offDiagonal_one_skewSwap_noncommute (i : ι) :
    offDiagonal (1 : Matrix ι ι ℝ) * skewSwap ι ≠
      skewSwap ι * offDiagonal (1 : Matrix ι ι ℝ) := by
  intro h
  have hi := congrArg (fun M => M (Sum.inl i) (Sum.inl i)) h
  norm_num [offDiagonal, skewSwap, fromBlocks_multiply] at hi

theorem twiceSwap_negative_square :
    -(((2 : ℝ) • skewSwap ι) * ((2 : ℝ) • skewSwap ι)) =
      (4 : ℝ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [smul_mul_smul, skewSwap_square]
  norm_num

theorem offDiagonal_twiceSwap_negative_square :
    -(offDiagonal ((2 : ℝ) • skewSwap ι) * offDiagonal ((2 : ℝ) • skewSwap ι)) =
      (4 : ℝ) • (1 : Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ℝ) := by
  rw [offDiagonal_smul, smul_mul_smul,
    offDiagonal_square_of_normalized (skewSwap ι) skewSwap_square]
  norm_num

/-- A concrete skew input has negative square `4I`, while its rotor ends at negative
square `I`. Thus an arbitrary original spectral interval cannot be retained verbatim. -/
theorem unnormalized_endpoint_counterexample :
    let A := (2 : ℝ) • skewSwap (Fin 1)
    let first := offDiagonal A
    let second := skewSwap (Fin 1 ⊕ Fin 1)
    Aᵀ = -A ∧
      -(interpolate first second 0 * interpolate first second 0) = (4 : ℝ) • 1 ∧
      -(interpolate first second (Real.pi / 2) *
        interpolate first second (Real.pi / 2)) = 1 ∧
      (4 : ℝ) • (1 : Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1))
        ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ℝ) ≠ 1 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simpa using (offDiagonal_twiceSwap_negative_square (ι := Fin 1))
  · simp
  · intro h
    have hi := congrArg
      (fun M => M (Sum.inl (Sum.inl (0 : Fin 1))) (Sum.inl (Sum.inl (0 : Fin 1)))) h
    norm_num at hi

end InfoGeometry.OperatorAlgebra.KitaevDoubledRotor
