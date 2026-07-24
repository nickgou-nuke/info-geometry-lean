import Mathlib

/-!
# Finite tensor determinant stabilization

This file records the finite algebra behind the determinant part of the
Cantor/Clifford tensor corridor.

The ordinary determinant is multiplicative but not stable under the doubling
embedding `A ↦ A ⊗ I₂`: the determinant squares.  The normalized logarithmic
readout

`logDet(A) / 2^n`

is stable when the next-stage log determinant doubles.  This is the finite
algebraic shadow of the Markov-trace/Fuglede-Kadison determinant lane, without
claiming an analytic completion or a von Neumann algebra theorem.

It also records the elementary multiplicative flux recurrence

`(1 + Y) * (1 + Z) = 1 + (Y + Z + Y * Z)`.

No infinite matrix.
No Type II/III existence claim.
No Fuglede-Kadison determinant theorem.
No Virasoro exponentiation claim.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteTensorDeterminantStabilization

/-! ## Normalized log-determinant stabilization -/

/-- Normalized logarithmic determinant readout at a binary tensor depth. -/
def normalizedLogDet
    (n : ℕ)
    (logDet : ℝ) : ℝ :=
  logDet / (2 : ℝ) ^ n

/--
If the unnormalized log-determinant doubles under `A ↦ A ⊗ I₂`, then the
binary-volume normalized log-determinant is unchanged.
-/
theorem normalizedLogDet_succ_of_double
    (n : ℕ)
    (x : ℝ) :
    normalizedLogDet (n + 1) (2 * x) = normalizedLogDet n x := by
  unfold normalizedLogDet
  rw [pow_succ]
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]

/--
The tensor determinant law specializes to determinant squaring for the
doubling embedding `A ↦ A ⊗ I₂`, once the identity block has determinant `1`.

This is the finite reason the ordinary determinant is not itself stable under
the binary tensor tower.
-/
theorem determinant_tensor_embedding_square
    {detA detI detTensor : ℝ}
    (hTensor : detTensor = detA ^ (2 : ℕ) * detI)
    (hI : detI = 1) :
    detTensor = detA ^ (2 : ℕ) := by
  rw [hTensor, hI]
  ring

/--
The ordinary determinant readout is fixed by the binary tensor-doubling rule
`det ↦ det²` only at the algebraic fixed points `0` and `1`.

This is the finite obstruction behind using a normalized logarithmic readout
instead of the raw determinant in a doubling tower.
-/
theorem determinant_square_fixed_iff_zero_or_one
    (detA : ℝ) :
    detA ^ (2 : ℕ) = detA ↔ detA = 0 ∨ detA = 1 := by
  constructor
  · intro h
    have hmul : detA * (detA - 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hmul with hzero | hone
    · exact Or.inl hzero
    · right
      nlinarith
  · intro h
    rcases h with hzero | hone
    · rw [hzero]
      norm_num
    · rw [hone]
      norm_num

/--
If the binary tensor embedding squares the determinant, then raw determinant
stability occurs only at determinant `0` or determinant `1`.
-/
theorem determinant_tensor_embedding_stable_iff_zero_or_one
    {detA detTensor : ℝ}
    (hTensor : detTensor = detA ^ (2 : ℕ)) :
    detTensor = detA ↔ detA = 0 ∨ detA = 1 := by
  rw [hTensor]
  exact determinant_square_fixed_iff_zero_or_one detA

/--
Logarithmic tensor determinant law for the binary embedding.

If `logDet(A ⊗ I₂) = 2 * logDet(A) + dim(A) * logDet(I₂)` and
`logDet(I₂)=0`, then `logDet(A ⊗ I₂) = 2 * logDet(A)`.
-/
theorem logDet_tensor_embedding_double
    (dimA : ℝ)
    {logDetA logDetI logDetTensor : ℝ}
    (hTensor : logDetTensor = 2 * logDetA + dimA * logDetI)
    (hI : logDetI = 0) :
    logDetTensor = 2 * logDetA := by
  rw [hTensor, hI]
  ring

/--
Finite binary tensor stabilization of the normalized log determinant.

This is the direct finite-stage theorem:

`logDet(A ⊗ I₂) = 2 logDet(A)` implies
`logDet(A ⊗ I₂) / 2^(n+1) = logDet(A) / 2^n`.
-/
theorem normalizedLogDet_tensor_embedding_stable
    (n : ℕ)
    {logDetA logDetTensor : ℝ}
    (hTensor : logDetTensor = 2 * logDetA) :
    normalizedLogDet (n + 1) logDetTensor =
      normalizedLogDet n logDetA := by
  rw [hTensor]
  exact normalizedLogDet_succ_of_double n logDetA

/--
The full binary embedding law with the identity block included.
-/
theorem normalizedLogDet_tensor_embedding_stable_of_identity
    (n : ℕ)
    (dimA : ℝ)
    {logDetA logDetI logDetTensor : ℝ}
    (hTensor : logDetTensor = 2 * logDetA + dimA * logDetI)
    (hI : logDetI = 0) :
    normalizedLogDet (n + 1) logDetTensor =
      normalizedLogDet n logDetA := by
  exact normalizedLogDet_tensor_embedding_stable n
    (logDet_tensor_embedding_double dimA hTensor hI)

/--
Finite-chain stabilization of normalized log determinant along a binary
doubling tower.

If each transition doubles the unnormalized log determinant,
`x (n+1) = 2 * x n`, then the binary-volume normalized readout is constant at
every finite stage.
-/
theorem normalizedLogDet_stable_along_doubling_chain
    (x : ℕ → ℝ)
    (hstep : ∀ n : ℕ, x (n + 1) = 2 * x n) :
    ∀ n : ℕ, normalizedLogDet n (x n) = normalizedLogDet 0 (x 0) := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [hstep n]
      rw [normalizedLogDet_succ_of_double]
      exact ih

/--
Two finite stages in a binary doubling tower have the same normalized
log-determinant.
-/
theorem normalizedLogDet_eq_of_doubling_chain
    (x : ℕ → ℝ)
    (hstep : ∀ n : ℕ, x (n + 1) = 2 * x n)
    (m n : ℕ) :
    normalizedLogDet m (x m) = normalizedLogDet n (x n) := by
  rw [normalizedLogDet_stable_along_doubling_chain x hstep m]
  rw [normalizedLogDet_stable_along_doubling_chain x hstep n]

/-! ## Temperley-Lieb/Jones finite algebra consequences -/

/--
A Temperley-Lieb/Jones adjacent triple relation is stable under right
multiplication by the idempotent endpoint.
-/
theorem jones_triple_right_idempotent
    {A : Type*} [Semiring A]
    {e f : A}
    {τ : A}
    (he : e * e = e)
    (hTL : (e * f) * e = τ * e) :
  ((e * f) * e) * e = τ * e := by
  rw [hTL]
  rw [mul_assoc, he]

/--
A Temperley-Lieb/Jones adjacent triple relation is stable under left
multiplication by the idempotent endpoint.
-/
theorem jones_triple_left_idempotent
    {A : Type*} [Semiring A]
    {e f : A}
    {τ : A}
    (he : e * e = e)
    (hTL : e * (f * e) = τ * e) :
    e * (e * (f * e)) = τ * e := by
  rw [← mul_assoc, he]
  exact hTL

/-! ## Multiplicative flux recurrence -/

/-- Multiplicative flux cross term for `(1 + Y) * (1 + Z)`. -/
def multiplicativeFlux
    {A : Type*} [Mul A] [Add A]
    (Y Z : A) : A :=
  Y + Z + Y * Z

/--
The finite multiplicative recurrence behind
`Δ_{N+1} = Δ_N ⊗ Δ_1` after writing `Δ = 1 + Y`.
-/
theorem one_add_mul_one_add_eq_one_add_flux
    {A : Type*} [Ring A]
    (Y Z : A) :
    (1 + Y) * (1 + Z) = 1 + multiplicativeFlux Y Z := by
  unfold multiplicativeFlux
  noncomm_ring

/--
Equivalently, the centered flux of the product is
`Y + Z + YZ`.
-/
theorem product_centered_flux_eq
    {A : Type*} [Ring A]
    (Y Z : A) :
    (1 + Y) * (1 + Z) - 1 = multiplicativeFlux Y Z := by
  rw [one_add_mul_one_add_eq_one_add_flux]
  simp

end InfoGeometry.Algebra.FiniteTensorDeterminantStabilization
