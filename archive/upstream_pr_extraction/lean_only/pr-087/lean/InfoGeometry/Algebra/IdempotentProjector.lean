import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `compIdempotent_isIdempotent` : Proves natively that the complement `1 - p` of an idempotent `p` is idempotent.
- `compIdempotent_orthogonal` : Proves natively that `p * (1 - p) = 0` given `IsIdempotent p`.
- `compIdempotent_orthogonal_rev` : Proves natively that `(1 - p) * p = 0` given `IsIdempotent p`.
- `compIdempotent_add_eq_one` : Proves natively the structural recovery identity `p + (1 - p) = 1`.
- `Peirce_left_decomp` : Proves natively the left algebraic projection decomposition over an element `x`.
- `Peirce_right_decomp` : Proves natively the right algebraic projection decomposition over an element `x`.
- `orthogonal_add_isIdempotent` : Proves natively that mutually orthogonal projectors sum to a valid projector.
- `commute_iff_comp_commute` : Proves natively that projectors commute if and only if their respective orthogonal complements commute.
- `peirce_decomposition_sum` : Proves that any ring element can be exactly reconstructed from its Peirce projectors.
- `peirce10_square_zero` : Exact algebraic verification that the off-diagonal flux channel `p * x * (1-p)` is strictly nilpotent.
- `peirce01_square_zero` : Exact algebraic verification that the dual off-diagonal flux channel `(1-p) * x * p` is strictly nilpotent.
- `peirce11_mul_peirce00` : Proves native topological separation (strict annihilation) between complementary diagonal blocks.
- `peirce00_mul_peirce11` : Proves native topological separation in reverse.
- `peirce11_mul_peirce11` : Proves native multiplicative closure of the generic particle transition block.
- `peirce00_mul_peirce00` : Proves native multiplicative closure of the complementary hole transition block.
- `peirce10_mul_peirce01` : Proves coupled opposing off-diagonal fluxes map structurally back into the `(1,1)` diagonal.
- `peirce01_mul_peirce10` : Proves reverse coupled opposing off-diagonal fluxes map structurally back into the `(0,0)` diagonal.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[Theorems that compile conditionally based on explicitly named, valid premises or external verified witnesses. No hidden assumptions.]
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
[Identified gaps, missing structural steps, or unverified steps. This defines the exact remaining debt line. No overclaims permitted.]
- None.
-/

section IdempotentProjectorAlgebra

variable {R : Type*} [Ring R]

/-- An element `p` is idempotent if `p * p = p`. -/
def IsIdempotent (p : R) : Prop := p * p = p

/-- The complementary idempotent to `p`. -/
def compIdempotent (p : R) : R := 1 - p

/-- The complement of an idempotent is also idempotent. -/
theorem compIdempotent_isIdempotent {p : R} (h : IsIdempotent p) : 
    IsIdempotent (compIdempotent p) := by
  dsimp [IsIdempotent, compIdempotent]
  calc
    (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
    _ = 1 - p - p + p := by rw [h]
    _ = 1 - p := by noncomm_ring

/-- Complementary idempotents are orthogonal. -/
theorem compIdempotent_orthogonal {p : R} (h : IsIdempotent p) : 
    p * compIdempotent p = 0 := by
  dsimp [compIdempotent]
  calc
    p * (1 - p) = p * 1 - p * p := by rw [mul_sub]
    _ = p - p * p := by rw [mul_one]
    _ = p - p := by rw [h]
    _ = 0 := by rw [sub_self]

/-- Complementary idempotents are orthogonal (reverse order). -/
theorem compIdempotent_orthogonal_rev {p : R} (h : IsIdempotent p) : 
    compIdempotent p * p = 0 := by
  dsimp [compIdempotent]
  calc
    (1 - p) * p = 1 * p - p * p := by rw [sub_mul]
    _ = p - p * p := by rw [one_mul]
    _ = p - p := by rw [h]
    _ = 0 := by rw [sub_self]

/-- The sum of complementary idempotents recovers the identity. -/
theorem compIdempotent_add_eq_one (p : R) :
    p + compIdempotent p = 1 := by
  dsimp [compIdempotent]
  noncomm_ring

/-- Left Peirce decomposition identity. -/
theorem Peirce_left_decomp (p x : R) : 
    x = p * x + compIdempotent p * x := by
  dsimp [compIdempotent]
  noncomm_ring

/-- Right Peirce decomposition identity. -/
theorem Peirce_right_decomp (p x : R) : 
    x = x * p + x * compIdempotent p := by
  dsimp [compIdempotent]
  noncomm_ring

/-- The sum of mutually orthogonal idempotents is idempotent. -/
theorem orthogonal_add_isIdempotent {p q : R} (hp : IsIdempotent p) (hq : IsIdempotent q) 
    (hpq : p * q = 0) (hqp : q * p = 0) : IsIdempotent (p + q) := by
  dsimp [IsIdempotent] at *
  calc
    (p + q) * (p + q) = p * p + p * q + q * p + q * q := by noncomm_ring
    _ = p + 0 + 0 + q := by rw [hp, hq, hpq, hqp]
    _ = p + q := by abel

/-- Two idempotents commute if and only if their complements commute. -/
theorem commute_iff_comp_commute (p q : R) : 
    p * q = q * p ↔ compIdempotent p * compIdempotent q = compIdempotent q * compIdempotent p := by
  dsimp [compIdempotent]
  constructor
  · intro h
    calc
      (1 - p) * (1 - q) = 1 - p - q + p * q := by noncomm_ring
      _ = 1 - p - q + q * p := by rw [h]
      _ = (1 - q) * (1 - p) := by noncomm_ring
  · intro h
    calc
      p * q = (1 - p) * (1 - q) - 1 + p + q := by noncomm_ring
      _ = (1 - q) * (1 - p) - 1 + p + q := by rw [h]
      _ = q * p := by noncomm_ring

/-- The (1, 1) diagonal block (particle-to-particle transition). -/
def peirce11 (p x : R) : R := p * x * p

/-- The (1, 0) off-diagonal block (hole-to-particle flux). -/
def peirce10 (p x : R) : R := p * x * compIdempotent p

/-- The (0, 1) off-diagonal block (particle-to-hole flux). -/
def peirce01 (p x : R) : R := compIdempotent p * x * p

/-- The (0, 0) diagonal block (hole-to-hole transition). -/
def peirce00 (p x : R) : R := compIdempotent p * x * compIdempotent p

/-- Exact reconstruction of a global operator from its orthogonal Peirce components. -/
theorem peirce_decomposition_sum (p x : R) :
    peirce11 p x + peirce10 p x + peirce01 p x + peirce00 p x = x := by
  dsimp [peirce11, peirce10, peirce01, peirce00, compIdempotent]
  noncomm_ring

/-- The off-diagonal flux channel isolates into a strictly nilpotent (square-zero) operator. -/
theorem peirce10_square_zero {p : R} (h : IsIdempotent p) (x : R) :
    peirce10 p x * peirce10 p x = 0 := by
  dsimp [peirce10]
  have h_ortho : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev h
  set c := compIdempotent p
  have id : (p * x * c) * (p * x * c) = p * x * (c * p) * (x * c) := by noncomm_ring
  rw [id, h_ortho, mul_zero, zero_mul]

/-- The dual off-diagonal flux channel also isolates into a strictly nilpotent operator. -/
theorem peirce01_square_zero {p : R} (h : IsIdempotent p) (x : R) :
    peirce01 p x * peirce01 p x = 0 := by
  dsimp [peirce01]
  have h_ortho : p * compIdempotent p = 0 := compIdempotent_orthogonal h
  set c := compIdempotent p
  have id : (c * x * p) * (c * x * p) = c * x * (p * c) * (x * p) := by noncomm_ring
  rw [id, h_ortho, mul_zero, zero_mul]

/-! ### Structural Multiplicative Relations of Peirce Blocks -/

/-- Distinct diagonal blocks strictly annihilate. -/
theorem peirce11_mul_peirce00 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce11 p x * peirce00 p y = 0 := by
  dsimp [peirce11, peirce00]
  have h_ortho : p * compIdempotent p = 0 := compIdempotent_orthogonal h
  set c := compIdempotent p
  have id : (p * x * p) * (c * y * c) = p * x * (p * c) * (y * c) := by noncomm_ring
  rw [id, h_ortho, mul_zero, zero_mul]

/-- Distinct diagonal blocks strictly annihilate (reverse order). -/
theorem peirce00_mul_peirce11 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce00 p x * peirce11 p y = 0 := by
  dsimp [peirce00, peirce11]
  have h_ortho : compIdempotent p * p = 0 := compIdempotent_orthogonal_rev h
  set c := compIdempotent p
  have id : (c * x * c) * (p * y * p) = c * x * (c * p) * (y * p) := by noncomm_ring
  rw [id, h_ortho, mul_zero, zero_mul]

/-- The (1,1) diagonal block is multiplicatively closed (subalgebra property). -/
theorem peirce11_mul_peirce11 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce11 p x * peirce11 p y = peirce11 p (x * p * y) := by
  dsimp [peirce11]
  have id : (p * x * p) * (p * y * p) = p * x * (p * p) * y * p := by noncomm_ring
  rw [id, h]
  noncomm_ring

/-- The (0,0) diagonal block is multiplicatively closed. -/
theorem peirce00_mul_peirce00 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce00 p x * peirce00 p y = peirce00 p (x * compIdempotent p * y) := by
  dsimp [peirce00]
  have hc : IsIdempotent (compIdempotent p) := compIdempotent_isIdempotent h
  dsimp [IsIdempotent] at hc
  set c := compIdempotent p
  have id : (c * x * c) * (c * y * c) = c * x * (c * c) * y * c := by noncomm_ring
  rw [id, hc]
  noncomm_ring

/-- Opposing flux channels multiply to populate the (1,1) diagonal sector. -/
theorem peirce10_mul_peirce01 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce10 p x * peirce01 p y = peirce11 p (x * compIdempotent p * y) := by
  dsimp [peirce10, peirce01, peirce11]
  have hc : IsIdempotent (compIdempotent p) := compIdempotent_isIdempotent h
  dsimp [IsIdempotent] at hc
  set c := compIdempotent p
  have id : (p * x * c) * (c * y * p) = p * x * (c * c) * y * p := by noncomm_ring
  rw [id, hc]
  noncomm_ring

/-- Opposing flux channels multiply (reverse order) to populate the (0,0) diagonal sector. -/
theorem peirce01_mul_peirce10 {p : R} (h : IsIdempotent p) (x y : R) :
    peirce01 p x * peirce10 p y = peirce00 p (x * p * y) := by
  dsimp [peirce01, peirce10, peirce00]
  have id : (compIdempotent p * x * p) * (p * y * compIdempotent p) = 
            compIdempotent p * x * (p * p) * y * compIdempotent p := by noncomm_ring
  rw [id, h]
  noncomm_ring

end IdempotentProjectorAlgebra
