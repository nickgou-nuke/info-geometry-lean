import Mathlib.Tactic

/-!
## Audit Protocol Map

### BUCKET 1: CLOSED FINITE THEOREMS
- `T_pow4`
- `P_par_idem`
- `drazin_comm_pow`
- `P_core_idem`
- `P_nil_idem`
- `P_core_nil_orth`
- `P_nil_core_orth`
- `phi_pow3`
- `phi_pow4_sub_one`
- `one_add_phi_sq_mul_phi`
- `phi_mul_sub_one_eq_one`
- `phi_ne_zero`
- `phi_inv_eq`
- `phi_pow3_sub_inv`
- `verlinde_golden_identity_mul`

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- `P_sum`
- `P_hyp_idem`
- `P_ell_idem`
- `P_hyp_ell_orth`
- `P_hyp_par_orth`
- `P_ell_par_orth`
- `verlinde_golden_identity`

### BUCKET 3: OPEN CLOSURE DEBT
- none
-/

namespace InfoGeometry.Canonical.MathematicalUnification

section TriFacet

variable {F : Type*} [Field F]

/-- The Hyperbolic projection operator. -/
def P_hyp [Invertible (2 : F)] (T : F) : F :=
  ⅟(2 : F) * (T ^ 2 + T)

/-- The Elliptic projection operator. -/
def P_ell [Invertible (2 : F)] (T : F) : F :=
  ⅟(2 : F) * (T ^ 2 - T)

/-- The Parabolic (Harmonic Kernel) projection operator. -/
def P_par (T : F) : F :=
  1 - T ^ 2

/-- The projection operators partition unity. -/
theorem P_sum [Invertible (2 : F)] (T : F) :
    P_hyp T + P_ell T + P_par T = 1 := by
  dsimp [P_hyp, P_ell, P_par]
  have h2 : ⅟(2 : F) * (2 : F) = 1 := invOf_mul_self (2 : F)
  calc
    ⅟(2 : F) * (T ^ 2 + T) + ⅟(2 : F) * (T ^ 2 - T) + (1 - T ^ 2)
        = ⅟(2 : F) * (2 : F) * T ^ 2 + (1 - T ^ 2) := by ring
    _ = 1 * T ^ 2 + (1 - T ^ 2) := by rw [h2]
    _ = 1 := by ring

/-- Auxiliary lemma proving `T^4` collapses to `T^2`. -/
theorem T_pow4 (T : F) (hT : T ^ 3 = T) : T ^ 4 = T ^ 2 := by
  calc
    T ^ 4 = T * T ^ 3 := by ring
    _ = T * T := by rw [hT]
    _ = T ^ 2 := by ring

/-- The Hyperbolic operator is idempotent. -/
theorem P_hyp_idem [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_hyp T = P_hyp T := by
  dsimp [P_hyp]
  have h2inv : ⅟(2 : F) * (2 : F) = 1 := invOf_mul_self (2 : F)
  have h1 :
      (⅟(2 : F) * (T ^ 2 + T)) * (⅟(2 : F) * (T ^ 2 + T)) =
        ⅟(2 : F) ^ 2 * (T ^ 2 + T) ^ 2 := by ring
  rw [h1]
  have h2 : (T ^ 2 + T) ^ 2 = 2 * (T ^ 2 + T) := by
    have h3 : (T ^ 2 + T) ^ 2 = T ^ 4 + 2 * T ^ 3 + T ^ 2 := by ring
    rw [h3, T_pow4 T hT, hT]
    ring
  rw [h2]
  calc
    ⅟(2 : F) ^ 2 * (2 * (T ^ 2 + T))
        = ⅟(2 : F) * (⅟(2 : F) * (2 : F)) * (T ^ 2 + T) := by ring
    _ = ⅟(2 : F) * 1 * (T ^ 2 + T) := by rw [h2inv]
    _ = ⅟(2 : F) * (T ^ 2 + T) := by ring

/-- The Elliptic operator is idempotent. -/
theorem P_ell_idem [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_ell T * P_ell T = P_ell T := by
  dsimp [P_ell]
  have h2inv : ⅟(2 : F) * (2 : F) = 1 := invOf_mul_self (2 : F)
  have h1 :
      (⅟(2 : F) * (T ^ 2 - T)) * (⅟(2 : F) * (T ^ 2 - T)) =
        ⅟(2 : F) ^ 2 * (T ^ 2 - T) ^ 2 := by ring
  rw [h1]
  have h2 : (T ^ 2 - T) ^ 2 = 2 * (T ^ 2 - T) := by
    have h3 : (T ^ 2 - T) ^ 2 = T ^ 4 - 2 * T ^ 3 + T ^ 2 := by ring
    rw [h3, T_pow4 T hT, hT]
    ring
  rw [h2]
  calc
    ⅟(2 : F) ^ 2 * (2 * (T ^ 2 - T))
        = ⅟(2 : F) * (⅟(2 : F) * (2 : F)) * (T ^ 2 - T) := by ring
    _ = ⅟(2 : F) * 1 * (T ^ 2 - T) := by rw [h2inv]
    _ = ⅟(2 : F) * (T ^ 2 - T) := by ring

/-- The Parabolic operator is idempotent. -/
theorem P_par_idem (T : F) (hT : T ^ 3 = T) :
    P_par T * P_par T = P_par T := by
  dsimp [P_par]
  calc
    (1 - T ^ 2) * (1 - T ^ 2) = 1 - 2 * T ^ 2 + T ^ 4 := by ring
    _ = 1 - 2 * T ^ 2 + T ^ 2 := by rw [T_pow4 T hT]
    _ = 1 - T ^ 2 := by ring

/-- Hyperbolic and Elliptic operators are mutually orthogonal. -/
theorem P_hyp_ell_orth [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_ell T = 0 := by
  dsimp [P_hyp, P_ell]
  have h1 :
      (⅟(2 : F) * (T ^ 2 + T)) * (⅟(2 : F) * (T ^ 2 - T)) =
        ⅟(2 : F) ^ 2 * (T ^ 4 - T ^ 2) := by ring
  rw [h1, T_pow4 T hT]
  ring

/-- Hyperbolic and Parabolic operators are mutually orthogonal. -/
theorem P_hyp_par_orth [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_par T = 0 := by
  dsimp [P_hyp, P_par]
  have h1 :
      ⅟(2 : F) * (T ^ 2 + T) * (1 - T ^ 2) =
        ⅟(2 : F) * (T ^ 2 + T - T ^ 4 - T ^ 3) := by
    ring
  rw [h1, T_pow4 T hT, hT]
  ring

/-- Elliptic and Parabolic operators are mutually orthogonal. -/
theorem P_ell_par_orth [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_ell T * P_par T = 0 := by
  dsimp [P_ell, P_par]
  have h1 :
      ⅟(2 : F) * (T ^ 2 - T) * (1 - T ^ 2) =
        ⅟(2 : F) * (T ^ 2 - T - T ^ 4 + T ^ 3) := by
    ring
  rw [h1, T_pow4 T hT, hT]
  ring

end TriFacet

section Drazin

/-- Prop representing the three defining conditions of a Drazin inverse in a ring. -/
abbrev IsDrazinInverse {R : Type*} [Ring R] (X X_D : R) (k : ℕ) : Prop :=
  X_D * X * X_D = X_D ∧
    X * X_D = X_D * X ∧ X ^ (k + 1) * X_D = X ^ k

variable {R : Type*} [Ring R] {X X_D : R} {k : ℕ}

/-- The Drazin inverse commutes with all powers of the operator. -/
theorem drazin_comm_pow (h : IsDrazinInverse X X_D k) (n : ℕ) :
    X_D * X ^ n = X ^ n * X_D := by
  induction n with
  | zero =>
      rw [pow_zero, mul_one, one_mul]
  | succ n ih =>
      calc
        X_D * X ^ (n + 1) = X_D * (X ^ n * X) := by rw [pow_succ]
        _ = (X_D * X ^ n) * X := by rw [mul_assoc]
        _ = (X ^ n * X_D) * X := by rw [ih]
        _ = X ^ n * (X_D * X) := by rw [← mul_assoc]
        _ = X ^ n * (X * X_D) := by rw [h.2.1.symm]
        _ = (X ^ n * X) * X_D := by rw [mul_assoc]
        _ = X ^ (n + 1) * X_D := by rw [pow_succ]

/-- The Compact Core Projection operator. -/
def P_core (X X_D : R) : R := X * X_D

/-- The Nilpotent Boundary Projection operator. -/
def P_nil (X X_D : R) : R := 1 - X * X_D

/-- The Compact Core projection is idempotent. -/
theorem P_core_idem (h : IsDrazinInverse X X_D k) :
    P_core X X_D * P_core X X_D = P_core X X_D := by
  dsimp [P_core]
  calc
    (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
    _ = X * X_D := by rw [h.1]

/-- The Nilpotent Boundary projection is idempotent. -/
theorem P_nil_idem (h : IsDrazinInverse X X_D k) :
    P_nil X X_D * P_nil X X_D = P_nil X X_D := by
  dsimp [P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h.1]
  calc
    (1 - X * X_D) * (1 - X * X_D)
        = 1 - 2 * (X * X_D) + (X * X_D) * (X * X_D) := by noncomm_ring
    _ = 1 - 2 * (X * X_D) + (X * X_D) := by rw [h_core]
    _ = 1 - X * X_D := by noncomm_ring

/-- Core and Nilpotent projections are mutually orthogonal (left-to-right). -/
theorem P_core_nil_orth (h : IsDrazinInverse X X_D k) :
    P_core X X_D * P_nil X X_D = 0 := by
  dsimp [P_core, P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h.1]
  calc
    (X * X_D) * (1 - X * X_D) = (X * X_D) - (X * X_D) * (X * X_D) := by
      noncomm_ring
    _ = (X * X_D) - (X * X_D) := by rw [h_core]
    _ = 0 := by noncomm_ring

/-- Core and Nilpotent projections are mutually orthogonal (right-to-left). -/
theorem P_nil_core_orth (h : IsDrazinInverse X X_D k) :
    P_nil X X_D * P_core X X_D = 0 := by
  dsimp [P_core, P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h.1]
  calc
    (1 - X * X_D) * (X * X_D) = (X * X_D) - (X * X_D) * (X * X_D) := by
      noncomm_ring
    _ = (X * X_D) - (X * X_D) := by rw [h_core]
    _ = 0 := by noncomm_ring

end Drazin

section GoldenRatio

variable {F : Type*} [Field F] {phi : F}

/-- The third power of the golden ratio. -/
theorem phi_pow3 (hphi : phi ^ 2 = phi + 1) :
    phi ^ 3 = 2 * phi + 1 := by
  calc
    phi ^ 3 = phi * phi ^ 2 := by ring
    _ = phi * (phi + 1) := by rw [hphi]
    _ = phi ^ 2 + phi := by ring
    _ = (phi + 1) + phi := by rw [hphi]
    _ = 2 * phi + 1 := by ring

/-- The fourth power of the golden ratio minus one. -/
theorem phi_pow4_sub_one (hphi : phi ^ 2 = phi + 1) :
    phi ^ 4 - 1 = 3 * phi + 1 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := phi_pow3 hphi
  calc
    phi ^ 4 - 1 = phi * phi ^ 3 - 1 := by ring
    _ = phi * (2 * phi + 1) - 1 := by rw [h3]
    _ = 2 * phi ^ 2 + phi - 1 := by ring
    _ = 2 * (phi + 1) + phi - 1 := by rw [hphi]
    _ = 3 * phi + 1 := by ring

/-- The anyonic quantum dimension scaling relation. -/
theorem one_add_phi_sq_mul_phi (hphi : phi ^ 2 = phi + 1) :
    (1 + phi ^ 2) * phi = 3 * phi + 1 := by
  calc
    (1 + phi ^ 2) * phi = phi + phi ^ 3 := by ring
    _ = phi + (2 * phi + 1) := by rw [phi_pow3 hphi]
    _ = 3 * phi + 1 := by ring

/-- Multiplicative relation proving the golden ratio is invertible. -/
theorem phi_mul_sub_one_eq_one (hphi : phi ^ 2 = phi + 1) :
    phi * (phi - 1) = 1 := by
  calc
    phi * (phi - 1) = phi ^ 2 - phi := by ring
    _ = (phi + 1) - phi := by rw [hphi]
    _ = 1 := by ring

/-- The golden ratio is non-zero. -/
theorem phi_ne_zero (hphi : phi ^ 2 = phi + 1) :
    phi ≠ 0 := by
  intro h_zero
  have h_mul : phi * (phi - 1) = 1 := phi_mul_sub_one_eq_one hphi
  rw [h_zero, zero_mul] at h_mul
  exact zero_ne_one h_mul

/-- The explicit inverse of the golden ratio. -/
theorem phi_inv_eq (hphi : phi ^ 2 = phi + 1) :
    phi⁻¹ = phi - 1 := by
  have h_ne : phi ≠ 0 := phi_ne_zero hphi
  have h_mul : phi * (phi - 1) = 1 := phi_mul_sub_one_eq_one hphi
  calc
    phi⁻¹ = phi⁻¹ * 1 := by ring
    _ = phi⁻¹ * (phi * (phi - 1)) := by rw [h_mul]
    _ = (phi⁻¹ * phi) * (phi - 1) := by ring
    _ = 1 * (phi - 1) := by rw [inv_mul_cancel₀ h_ne]
    _ = phi - 1 := by ring

/-- The anyonic loop difference identity. -/
theorem phi_pow3_sub_inv (hphi : phi ^ 2 = phi + 1) :
    phi ^ 3 - phi⁻¹ = phi + 2 := by
  rw [phi_inv_eq hphi, phi_pow3 hphi]
  ring

/-- Multiplicative equivalent of the Verlinde anyonic fusion identity. -/
theorem verlinde_golden_identity_mul (hphi : phi ^ 2 = phi + 1) :
    phi ^ 3 - phi⁻¹ = 1 + phi ^ 2 := by
  calc
    phi ^ 3 - phi⁻¹ = phi + 2 := phi_pow3_sub_inv hphi
    _ = 1 + (phi + 1) := by ring
    _ = 1 + phi ^ 2 := by rw [← hphi]

/-- The exact Verlinde golden ratio division identity. -/
theorem verlinde_golden_identity
    (hphi : phi ^ 2 = phi + 1)
    (h_div : 1 + phi ^ 2 ≠ 0) :
    (phi ^ 3 - phi⁻¹) / (1 + phi ^ 2) = 1 := by
  rw [verlinde_golden_identity_mul hphi]
  exact div_self h_div

end GoldenRatio

end InfoGeometry.Canonical.MathematicalUnification
