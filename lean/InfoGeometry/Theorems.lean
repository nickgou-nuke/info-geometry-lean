import Mathlib.Tactic

/-!
# Mathematical Unification of Tri-Facet Geometry, Drazin Inverses, and Golden Ratio Invariants

This file formalizes algebraic components extracted from the structural chain
connecting finite projector decompositions, Drazin core/nilpotent splits, and
topological Fibonacci/Verlinde golden-ratio identities.

1. **Tri-Facet Geometry (`T^3 = T`)**: projective scalar identities splitting a
   carrier into elliptic, hyperbolic, and parabolic sectors. The half-projectors
   explicitly require `Invertible (2 : F)`.
2. **Drazin Core/Nilpotent Decomposition**: finite noncommutative ring identities
   for the core projection `X * X_D` and the complement `1 - X * X_D`. The Drazin
   laws are explicit theorem hypotheses, not fields of a proof-carrying structure.
3. **Golden Ratio Invariants**: pure algebraic proofs of golden-ratio identities
   underpinning the Verlinde fusion algebra of Fibonacci anyons.

#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `krein_plus_idem`: verifies idempotent positive sector projector in a scalar Krein split.
- `krein_minus_idem`: verifies idempotent negative sector projector in a scalar Krein split.
- `krein_ortho`: proves exact orthogonality between the scalar positive/negative projectors.
- `idempotent_trace_variance`: proves the centered second-moment identity for an idempotent.
- `tri_facet_trace_fluctuation`: proves the centered cubic identity for an `O^3 = O` element.
- `verlinde_fibonacci_fusion_algebraic`: proves the Fibonacci fusion numerator identity.
- `P_sum`: proves the tri-facet scalar projectors partition unity.
- `T_pow4`: proves the fourth-power collapse from `T^3 = T`.
- `P_hyp_idem`, `P_ell_idem`, `P_par_idem`: prove tri-facet projector idempotency.
- `P_hyp_ell_orth`, `P_hyp_par_orth`, `P_ell_par_orth`: prove tri-facet orthogonality.
- `drazin_comm_pow`: proves Drazin commutation propagates to powers.
- `P_core_idem`, `P_nil_idem`: prove core/nilpotent Drazin projector idempotency.
- `P_core_nil_orth`, `P_nil_core_orth`: prove core/nilpotent Drazin projector orthogonality.
- `phi_pow3`, `phi_pow4_sub_one`, `one_add_phi_sq_mul_phi`, `phi_mul_sub_one_eq_one`,
  `phi_ne_zero`, `phi_inv_eq`, `phi_pow3_sub_inv`, `verlinde_golden_identity_mul`,
  `verlinde_golden_identity`: prove golden-ratio and Verlinde identities.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
[Theorems that compile based on explicitly named theorem parameters or imported verified premises.]
- The projector lemmas are conditional on `J^2 = 1` and invertibility of `2`.
- The trace fluctuation lemmas are conditional on explicit linear trace-normalization,
  centering, decomposition, and idempotent/tri-facet hypotheses.
- The Verlinde algebraic identity is conditional on the explicit golden-ratio and
  normalization equations.
- The tri-facet lemmas are conditional on `T^3 = T`.
- The Drazin lemmas are conditional on explicit commutation/reflexive Drazin equations.
- The golden-ratio lemmas are conditional on `phi^2 = phi + 1`.

#### BUCKET 3: OPEN CLOSURE DEBT
[Exact theorem statements that remain unproved. No wrappers, sockets, fields, witnesses,
certificates, or renamed placeholders.]
- None in this file.
-/

namespace InfoGeometry.Theorems

section KreinSpaceProjectors

variable {A : Type*} [CommRing A] [Invertible (2 : A)]

/-- The positive-norm exact-forms projector defined by a scalar fundamental symmetry. -/
def krein_plus (J : A) : A := ⅟(2 : A) * (1 + J)

/-- The negative-norm coexact-forms projector defined by a scalar fundamental symmetry. -/
def krein_minus (J : A) : A := ⅟(2 : A) * (1 - J)

/-- The scalar positive-sector projector is idempotent. -/
theorem krein_plus_idem (J : A) (hJ : J ^ 2 = 1) :
    (krein_plus J) ^ 2 = krein_plus J := by
  unfold krein_plus
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self (2 : A)
  calc
    (⅟(2 : A) * (1 + J)) ^ 2
        = ⅟(2 : A) ^ 2 * (1 + 2 * J + J ^ 2) := by ring
    _ = ⅟(2 : A) ^ 2 * (1 + 2 * J + 1) := by rw [hJ]
    _ = ⅟(2 : A) ^ 2 * (2 + 2 * J) := by ring
    _ = ⅟(2 : A) * (⅟(2 : A) * 2) * (1 + J) := by ring
    _ = ⅟(2 : A) * 1 * (1 + J) := by rw [h2]
    _ = ⅟(2 : A) * (1 + J) := by ring

/-- The scalar negative-sector projector is idempotent. -/
theorem krein_minus_idem (J : A) (hJ : J ^ 2 = 1) :
    (krein_minus J) ^ 2 = krein_minus J := by
  unfold krein_minus
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self (2 : A)
  calc
    (⅟(2 : A) * (1 - J)) ^ 2
        = ⅟(2 : A) ^ 2 * (1 - 2 * J + J ^ 2) := by ring
    _ = ⅟(2 : A) ^ 2 * (1 - 2 * J + 1) := by rw [hJ]
    _ = ⅟(2 : A) ^ 2 * (2 - 2 * J) := by ring
    _ = ⅟(2 : A) * (⅟(2 : A) * 2) * (1 - J) := by ring
    _ = ⅟(2 : A) * 1 * (1 - J) := by rw [h2]
    _ = ⅟(2 : A) * (1 - J) := by ring

/-- The scalar positive and negative projectors are orthogonal. -/
theorem krein_ortho (J : A) (hJ : J ^ 2 = 1) :
    krein_plus J * krein_minus J = 0 := by
  unfold krein_plus krein_minus
  calc
    (⅟(2 : A) * (1 + J)) * (⅟(2 : A) * (1 - J))
        = ⅟(2 : A) ^ 2 * (1 - J ^ 2) := by ring
    _ = ⅟(2 : A) ^ 2 * (1 - 1) := by rw [hJ]
    _ = 0 := by ring

end KreinSpaceProjectors

section ThermodynamicFluctuations

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/--
The centered second moment of an idempotent is `c - c^2` under a normalized
linear trace functional and a centered decomposition `P = c + X`.
-/
theorem idempotent_trace_variance
    (tau : A →ₗ[K] K) (htau_one : tau 1 = 1)
    (P X : A) (c : K)
    (hP_eq : P = algebraMap K A c + X)
    (h_tau_X : tau X = 0)
    (h_idem : P ^ 2 = P) :
    tau (X ^ 2) = c - c ^ 2 := by
  have h_map (k : K) : tau (algebraMap K A k) = k := by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, htau_one, smul_eq_mul, mul_one]
  have hP : tau P = c := by
    rw [hP_eq, map_add, h_map, h_tau_X, add_zero]
  have hP2 : P ^ 2 = algebraMap K A (c ^ 2) + algebraMap K A (2 * c) * X + X ^ 2 := by
    rw [hP_eq]
    calc
      (algebraMap K A c + X) ^ 2
          = (algebraMap K A c) ^ 2 + 2 * (algebraMap K A c) * X + X ^ 2 := by ring
      _ = algebraMap K A (c ^ 2) + algebraMap K A (2 * c) * X + X ^ 2 := by
        simp only [map_pow, map_mul, map_ofNat]
  have h_tau_P2 : tau (P ^ 2) = c ^ 2 + tau (X ^ 2) := by
    rw [hP2, map_add, map_add, h_map]
    have h_cross : tau (algebraMap K A (2 * c) * X) = 0 := by
      calc
        tau (algebraMap K A (2 * c) * X)
            = tau ((2 * c) • X) := by rw [← Algebra.smul_def]
        _ = (2 * c) • tau X := by rw [LinearMap.map_smul]
        _ = (2 * c) • (0 : K) := by rw [h_tau_X]
        _ = 0 := smul_zero _
    rw [h_cross, add_zero]
  rw [h_idem] at h_tau_P2
  rw [hP] at h_tau_P2
  calc
    tau (X ^ 2) = (c ^ 2 + tau (X ^ 2)) - c ^ 2 := by abel
    _ = c - c ^ 2 := by rw [h_tau_P2.symm]

/--
The centered cubic trace decomposition for an element satisfying `O^3 = O`.
-/
theorem tri_facet_trace_fluctuation
    (tau : A →ₗ[K] K) (htau_one : tau 1 = 1)
    (O X : A) (c : K)
    (hO_eq : O = algebraMap K A c + X)
    (h_tau_X : tau X = 0)
    (h_tri : O ^ 3 = O) :
    3 * c * tau (X ^ 2) + tau (X ^ 3) = c - c ^ 3 := by
  have h_map (k : K) : tau (algebraMap K A k) = k := by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, htau_one, smul_eq_mul, mul_one]
  have hO : tau O = c := by
    rw [hO_eq, map_add, h_map, h_tau_X, add_zero]
  have hO3 :
      O ^ 3 =
        algebraMap K A (c ^ 3) +
          algebraMap K A (3 * c ^ 2) * X +
            algebraMap K A (3 * c) * X ^ 2 + X ^ 3 := by
    rw [hO_eq]
    calc
      (algebraMap K A c + X) ^ 3 =
          (algebraMap K A c) ^ 3 +
            3 * (algebraMap K A c) ^ 2 * X +
              3 * (algebraMap K A c) * X ^ 2 + X ^ 3 := by ring
      _ = algebraMap K A (c ^ 3) +
            algebraMap K A (3 * c ^ 2) * X +
              algebraMap K A (3 * c) * X ^ 2 + X ^ 3 := by
        simp only [map_pow, map_mul, map_ofNat]
  have h_tau_O3 : tau (O ^ 3) = c ^ 3 + (3 * c) * tau (X ^ 2) + tau (X ^ 3) := by
    rw [hO3]
    simp only [map_add]
    rw [h_map]
    have h_cross1 : tau (algebraMap K A (3 * c ^ 2) * X) = 0 := by
      calc
        tau (algebraMap K A (3 * c ^ 2) * X)
            = tau ((3 * c ^ 2) • X) := by rw [← Algebra.smul_def]
        _ = (3 * c ^ 2) • tau X := by rw [LinearMap.map_smul]
        _ = (3 * c ^ 2) • (0 : K) := by rw [h_tau_X]
        _ = 0 := smul_zero _
    have h_cross2 : tau (algebraMap K A (3 * c) * X ^ 2) = (3 * c) * tau (X ^ 2) := by
      calc
        tau (algebraMap K A (3 * c) * X ^ 2)
            = tau ((3 * c) • X ^ 2) := by rw [← Algebra.smul_def]
        _ = (3 * c) • tau (X ^ 2) := by rw [LinearMap.map_smul]
        _ = (3 * c) * tau (X ^ 2) := rfl
    rw [h_cross1, h_cross2]
    ring
  rw [h_tri] at h_tau_O3
  rw [hO] at h_tau_O3
  calc
    3 * c * tau (X ^ 2) + tau (X ^ 3)
        = (c ^ 3 + (3 * c * tau (X ^ 2) + tau (X ^ 3))) - c ^ 3 := by abel
    _ = c - c ^ 3 := by
      rw [show c ^ 3 + (3 * c * tau (X ^ 2) + tau (X ^ 3)) = c by
        simpa [add_assoc] using h_tau_O3.symm]

end ThermodynamicFluctuations

section VerlindeFusionAlgebra

variable {K : Type*} [CommRing K]

/--
Exact algebraic numerator trace identity for the Fibonacci Verlinde fusion loop.
-/
theorem verlinde_fibonacci_fusion_algebraic
    (phi N : K)
    (h_phi : phi ^ 2 = phi + 1)
    (h_N : N ^ 2 * (1 + phi ^ 2) = 1) :
    (N * phi) ^ 3 * (N * phi) + (-N) ^ 3 * N = N ^ 2 * phi := by
  have h_phi3 : phi ^ 3 = 2 * phi + 1 := by
    calc
      phi ^ 3 = phi ^ 2 * phi := by ring
      _ = (phi + 1) * phi := by rw [h_phi]
      _ = phi ^ 2 + phi := by ring
      _ = (phi + 1) + phi := by rw [h_phi]
      _ = 2 * phi + 1 := by ring
  have h_phi4 : phi ^ 4 = 3 * phi + 2 := by
    calc
      phi ^ 4 = phi ^ 3 * phi := by ring
      _ = (2 * phi + 1) * phi := by rw [h_phi3]
      _ = 2 * phi ^ 2 + phi := by ring
      _ = 2 * (phi + 1) + phi := by rw [h_phi]
      _ = 3 * phi + 2 := by ring
  have h_N2_val : N ^ 2 * (phi + 2) = 1 := by
    calc
      N ^ 2 * (phi + 2) = N ^ 2 * (phi + 1 + 1) := by ring
      _ = N ^ 2 * (phi ^ 2 + 1) := by rw [h_phi]
      _ = N ^ 2 * (1 + phi ^ 2) := by ring
      _ = 1 := h_N
  calc
    (N * phi) ^ 3 * (N * phi) + (-N) ^ 3 * N
        = N ^ 4 * phi ^ 4 - N ^ 4 := by ring
    _ = N ^ 4 * (phi ^ 4 - 1) := by ring
    _ = N ^ 4 * (3 * phi + 2 - 1) := by rw [h_phi4]
    _ = N ^ 4 * (3 * phi + 1) := by ring
    _ = N ^ 2 * (N ^ 2 * (3 * phi + 1)) := by ring
    _ = N ^ 2 * (N ^ 2 * (phi * (phi + 2))) := by
      have h_factor : 3 * phi + 1 = phi * (phi + 2) := by
        calc
          3 * phi + 1 = (phi + 1) + 2 * phi := by ring
          _ = phi ^ 2 + 2 * phi := by rw [← h_phi]
          _ = phi * (phi + 2) := by ring
      rw [h_factor]
    _ = N ^ 2 * phi * (N ^ 2 * (phi + 2)) := by ring
    _ = N ^ 2 * phi * 1 := by rw [h_N2_val]
    _ = N ^ 2 * phi := by ring

end VerlindeFusionAlgebra

section TriFacet

variable {F : Type*} [CommRing F]

/-- The hyperbolic projection scalar associated to a tri-facet element. -/
def P_hyp [Invertible (2 : F)] (T : F) : F := ⅟(2 : F) * (T ^ 2 + T)

/-- The elliptic projection scalar associated to a tri-facet element. -/
def P_ell [Invertible (2 : F)] (T : F) : F := ⅟(2 : F) * (T ^ 2 - T)

/-- The parabolic projection scalar associated to a tri-facet element. -/
def P_par (T : F) : F := 1 - T ^ 2

/-- The tri-facet scalar projectors partition unity. -/
theorem P_sum [Invertible (2 : F)] (T : F) : P_hyp T + P_ell T + P_par T = 1 := by
  dsimp [P_hyp, P_ell, P_par]
  have h2 : ⅟(2 : F) * 2 = 1 := invOf_mul_self (2 : F)
  calc
    ⅟(2 : F) * (T ^ 2 + T) + ⅟(2 : F) * (T ^ 2 - T) + (1 - T ^ 2)
        = ⅟(2 : F) * 2 * T ^ 2 + (1 - T ^ 2) := by ring
    _ = 1 * T ^ 2 + (1 - T ^ 2) := by rw [h2]
    _ = 1 := by ring

/-- A tri-facet element satisfying `T^3 = T` has `T^4 = T^2`. -/
theorem T_pow4 (T : F) (hT : T ^ 3 = T) : T ^ 4 = T ^ 2 := by
  calc
    T ^ 4 = T * T ^ 3 := by ring
    _ = T * T := by rw [hT]
    _ = T ^ 2 := by ring

/-- The hyperbolic tri-facet scalar projector is idempotent. -/
theorem P_hyp_idem [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_hyp T = P_hyp T := by
  dsimp [P_hyp]
  have h2inv : ⅟(2 : F) * 2 = 1 := invOf_mul_self (2 : F)
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
        = ⅟(2 : F) * (⅟(2 : F) * 2) * (T ^ 2 + T) := by ring
    _ = ⅟(2 : F) * 1 * (T ^ 2 + T) := by rw [h2inv]
    _ = ⅟(2 : F) * (T ^ 2 + T) := by ring

/-- The elliptic tri-facet scalar projector is idempotent. -/
theorem P_ell_idem [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_ell T * P_ell T = P_ell T := by
  dsimp [P_ell]
  have h2inv : ⅟(2 : F) * 2 = 1 := invOf_mul_self (2 : F)
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
        = ⅟(2 : F) * (⅟(2 : F) * 2) * (T ^ 2 - T) := by ring
    _ = ⅟(2 : F) * 1 * (T ^ 2 - T) := by rw [h2inv]
    _ = ⅟(2 : F) * (T ^ 2 - T) := by ring

/-- The parabolic tri-facet scalar projector is idempotent. -/
theorem P_par_idem (T : F) (hT : T ^ 3 = T) :
    P_par T * P_par T = P_par T := by
  dsimp [P_par]
  calc
    (1 - T ^ 2) * (1 - T ^ 2) = 1 - 2 * T ^ 2 + T ^ 4 := by ring
    _ = 1 - 2 * T ^ 2 + T ^ 2 := by rw [T_pow4 T hT]
    _ = 1 - T ^ 2 := by ring

/-- The hyperbolic and elliptic tri-facet projectors are orthogonal. -/
theorem P_hyp_ell_orth [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_ell T = 0 := by
  dsimp [P_hyp, P_ell]
  have h1 :
      (⅟(2 : F) * (T ^ 2 + T)) * (⅟(2 : F) * (T ^ 2 - T)) =
        ⅟(2 : F) ^ 2 * (T ^ 4 - T ^ 2) := by ring
  rw [h1, T_pow4 T hT]
  ring

/-- The hyperbolic and parabolic tri-facet projectors are orthogonal. -/
theorem P_hyp_par_orth [Invertible (2 : F)] (T : F) (hT : T ^ 3 = T) :
    P_hyp T * P_par T = 0 := by
  dsimp [P_hyp, P_par]
  have h1 :
      ⅟(2 : F) * (T ^ 2 + T) * (1 - T ^ 2) =
        ⅟(2 : F) * (T ^ 2 + T - T ^ 4 - T ^ 3) := by
    ring
  rw [h1, T_pow4 T hT, hT]
  ring

/-- The elliptic and parabolic tri-facet projectors are orthogonal. -/
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

variable {R : Type*} [Ring R] {X X_D : R}

/-- The compact core projection associated to an explicit Drazin pair. -/
def P_core (X X_D : R) : R := X * X_D

/-- The nilpotent boundary projection associated to an explicit Drazin pair. -/
def P_nil (X X_D : R) : R := 1 - X * X_D

/-- Drazin commutation propagates to every natural power. -/
theorem drazin_comm_pow
    (h_comm : X_D * X = X * X_D) (n : ℕ) :
    X_D * X ^ n = X ^ n * X_D := by
  induction n with
  | zero =>
      rw [pow_zero, mul_one, one_mul]
  | succ n ih =>
      calc
        X_D * X ^ (n + 1) = X_D * (X ^ n * X) := by rw [pow_succ]
        _ = (X_D * X ^ n) * X := by rw [mul_assoc]
        _ = (X ^ n * X_D) * X := by rw [ih]
        _ = X ^ n * (X_D * X) := by rw [mul_assoc]
        _ = X ^ n * (X * X_D) := by rw [h_comm]
        _ = (X ^ n * X) * X_D := by rw [mul_assoc]
        _ = X ^ (n + 1) * X_D := by rw [pow_succ]

/-- The compact Drazin core projection is idempotent under the reflexive Drazin law. -/
theorem P_core_idem
    (h_reflexive : X_D * X * X_D = X_D) :
    P_core X X_D * P_core X X_D = P_core X X_D := by
  dsimp [P_core]
  calc
    (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
    _ = X * X_D := by rw [h_reflexive]

/-- The nilpotent Drazin boundary projection is idempotent under the reflexive Drazin law. -/
theorem P_nil_idem
    (h_reflexive : X_D * X * X_D = X_D) :
    P_nil X X_D * P_nil X X_D = P_nil X X_D := by
  dsimp [P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h_reflexive]
  calc
    (1 - X * X_D) * (1 - X * X_D)
        = 1 - 2 * (X * X_D) + (X * X_D) * (X * X_D) := by noncomm_ring
    _ = 1 - 2 * (X * X_D) + (X * X_D) := by rw [h_core]
    _ = 1 - X * X_D := by noncomm_ring

/-- The Drazin core and nilpotent boundary projections are left-to-right orthogonal. -/
theorem P_core_nil_orth
    (h_reflexive : X_D * X * X_D = X_D) :
    P_core X X_D * P_nil X X_D = 0 := by
  dsimp [P_core, P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h_reflexive]
  calc
    (X * X_D) * (1 - X * X_D) = (X * X_D) - (X * X_D) * (X * X_D) := by
      noncomm_ring
    _ = (X * X_D) - (X * X_D) := by rw [h_core]
    _ = 0 := by noncomm_ring

/-- The Drazin nilpotent boundary and core projections are right-to-left orthogonal. -/
theorem P_nil_core_orth
    (h_reflexive : X_D * X * X_D = X_D) :
    P_nil X X_D * P_core X X_D = 0 := by
  dsimp [P_core, P_nil]
  have h_core : (X * X_D) * (X * X_D) = X * X_D := by
    calc
      (X * X_D) * (X * X_D) = X * (X_D * X * X_D) := by noncomm_ring
      _ = X * X_D := by rw [h_reflexive]
  calc
    (1 - X * X_D) * (X * X_D) = (X * X_D) - (X * X_D) * (X * X_D) := by
      noncomm_ring
    _ = (X * X_D) - (X * X_D) := by rw [h_core]
    _ = 0 := by noncomm_ring

end Drazin

section GoldenRatio

variable {F : Type*} [Field F] {phi : F}

/-- The third power of a golden-ratio element. -/
theorem phi_pow3 (hphi : phi ^ 2 = phi + 1) :
    phi ^ 3 = 2 * phi + 1 := by
  calc
    phi ^ 3 = phi * phi ^ 2 := by ring
    _ = phi * (phi + 1) := by rw [hphi]
    _ = phi ^ 2 + phi := by ring
    _ = (phi + 1) + phi := by rw [hphi]
    _ = 2 * phi + 1 := by ring

/-- The fourth power minus one of a golden-ratio element. -/
theorem phi_pow4_sub_one (hphi : phi ^ 2 = phi + 1) :
    phi ^ 4 - 1 = 3 * phi + 1 := by
  have h3 : phi ^ 3 = 2 * phi + 1 := phi_pow3 hphi
  calc
    phi ^ 4 - 1 = phi * phi ^ 3 - 1 := by ring
    _ = phi * (2 * phi + 1) - 1 := by rw [h3]
    _ = 2 * phi ^ 2 + phi - 1 := by ring
    _ = 2 * (phi + 1) + phi - 1 := by rw [hphi]
    _ = 3 * phi + 1 := by ring

/-- The anyonic quantum-dimension scaling relation. -/
theorem one_add_phi_sq_mul_phi (hphi : phi ^ 2 = phi + 1) :
    (1 + phi ^ 2) * phi = 3 * phi + 1 := by
  calc
    (1 + phi ^ 2) * phi = phi + phi ^ 3 := by ring
    _ = phi + (2 * phi + 1) := by rw [phi_pow3 hphi]
    _ = 3 * phi + 1 := by ring

/-- A golden-ratio element has explicit right inverse `phi - 1`. -/
theorem phi_mul_sub_one_eq_one (hphi : phi ^ 2 = phi + 1) :
    phi * (phi - 1) = 1 := by
  calc
    phi * (phi - 1) = phi ^ 2 - phi := by ring
    _ = (phi + 1) - phi := by rw [hphi]
    _ = 1 := by ring

/-- A golden-ratio element is nonzero. -/
theorem phi_ne_zero (hphi : phi ^ 2 = phi + 1) :
    phi ≠ 0 := by
  intro h_zero
  have h_mul : phi * (phi - 1) = 1 := phi_mul_sub_one_eq_one hphi
  rw [h_zero, zero_mul] at h_mul
  exact zero_ne_one h_mul

/-- The explicit inverse of a golden-ratio element. -/
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

/-- Multiplicative equivalent of the Verlinde golden-ratio identity. -/
theorem verlinde_golden_identity_mul (hphi : phi ^ 2 = phi + 1) :
    phi ^ 3 - phi⁻¹ = 1 + phi ^ 2 := by
  calc
    phi ^ 3 - phi⁻¹ = phi + 2 := phi_pow3_sub_inv hphi
    _ = 1 + (phi + 1) := by ring
    _ = 1 + phi ^ 2 := by rw [← hphi]

/-- The exact Verlinde golden-ratio division identity. -/
theorem verlinde_golden_identity
    (hphi : phi ^ 2 = phi + 1)
    (h_div : 1 + phi ^ 2 ≠ 0) :
    (phi ^ 3 - phi⁻¹) / (1 + phi ^ 2) = 1 := by
  rw [verlinde_golden_identity_mul hphi]
  exact div_self h_div

end GoldenRatio

end InfoGeometry.Theorems
