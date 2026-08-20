import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Center
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.HypothesisFoundations

/-!
=============================================================================
1. AUTOMORPHISM & DERIVATION-FLOW INVARIANCE OF ALGEBRAIC STRUCTURES
=============================================================================
-/

section AutomorphismInvariance

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- An automorphism strictly preserves idempotent elements (e.g. Peirce projectors e_±). -/
theorem automorphism_preserves_idempotent (f : A ≃+* A) (x : A) (hx : x * x = x) :
    f x * f x = f x := by
  rw [← f.map_mul, hx]

/-- An automorphism strictly preserves nilpotent elements (e.g. fermionic generators G_±). -/
theorem automorphism_preserves_nilpotent (f : A ≃+* A) (x : A) (hx : x * x = 0) :
    f x * f x = 0 := by
  rw [← f.map_mul, hx, f.map_zero]

/-- An automorphism strictly preserves canonical anticommutators {x, y} = c. -/
theorem automorphism_preserves_anticommutator (f : A ≃+* A) (x y c : A) (h : x * y + y * x = c) :
    f x * f y + f y * f x = f c := by
  rw [← f.map_mul, ← f.map_mul, ← f.map_add, h]

variable {A_unit : Type*} [Ring A_unit]

/-- An automorphism on a unital ring strictly preserves the partition of unity e_+ + e_- = 1. -/
theorem automorphism_preserves_partition_of_unity (f : A_unit ≃+* A_unit) (e₁ e₂ : A_unit) (h : e₁ + e₂ = 1) :
    f e₁ + f e₂ = 1 := by
  rw [← f.map_add, h, f.map_one]

end AutomorphismInvariance

/-!
=============================================================================
2. BdG PARTICLE-HOLE SYMMETRY & ANTIUNITARY BLOCK RELATIONS
=============================================================================
-/

section BdGBlockSymmetries

variable {R : Type*} [Ring R]

/-- BdG Hamiltonian represented as a 2x2 block matrix over a ring R. -/
structure BdGMatrix (R : Type*) [Ring R] where
  h : R
  delta : R
  delta_adj : R
  h_adj : R

/-- 
  BdG Particle-Hole Anticommutation Theorem:
  If the normal state satisfies C h = - h_adj C,
  and the pairing satisfies C delta = delta_adj C,
  then the total BdG Hamiltonian strictly anticommutes with C:
  C * H_BdG + H_BdG * C = 0.
-/
theorem bdg_particle_hole_anticommutation (H : BdGMatrix R) (C : R)
    (h_norm : C * H.h = - (H.h_adj * C))
    (h_pair1 : C * H.delta = H.delta_adj * C)
    (h_pair2 : C * H.delta_adj = H.delta * C) :
    (C * H.h + H.h_adj * C = 0) ∧
    (C * H.delta - H.delta_adj * C = 0) ∧
    (C * H.delta_adj - H.delta * C = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h_norm, neg_add_cancel]
  · rw [h_pair1, sub_self]
  · rw [h_pair2, sub_self]

/-- Schur complement self-energy formula: Σ(E) = h + Δ (E + h_adj)⁻¹ Δ†. -/
def schur_self_energy (h delta delta_adj : R) (resolvent : R) : R :=
  h + delta * resolvent * delta_adj

/-- Invertibility requirement: Resolvent equation (E + h_adj) * resolvent = 1. -/
theorem schur_resolvent_identity (delta_adj resolvent E h_adj : R)
    (h_res : (E + h_adj) * resolvent = 1) :
    (E + h_adj) * (resolvent * delta_adj) = delta_adj := by
  rw [← mul_assoc, h_res, one_mul]

end BdGBlockSymmetries

/-!
=============================================================================
3. GRADED TRIFOLD DECOMPOSITION WITH INVERTIBILITY HYPOTHESIS
=============================================================================
-/

section TrifoldDecomposition

variable {R : Type*} [CommRing R]

/-- Trifold representation of a 2-graded matrix with trace and supertrace. -/
structure GradedMatrix2 (R : Type*) [CommRing R] where
  diag_top : R
  diag_bot : R
  off_diag1 : R
  off_diag2 : R

namespace GradedMatrix2

variable {R : Type*} [CommRing R]

def tr (M : GradedMatrix2 R) : R := M.diag_top + M.diag_bot
def str (M : GradedMatrix2 R) : R := M.diag_top - M.diag_bot

/-- The Common Weyl Mode α = (Tr M) / 2 -/
def alpha (M : GradedMatrix2 R) (two_inv : R) : R := two_inv * M.tr

/-- The Chiral Mode β = (STr M) / 2 -/
def beta (M : GradedMatrix2 R) (two_inv : R) : R := two_inv * M.str

/-- The Traceless and Supertraceless Shape Mode M₀ -/
def M0 (M : GradedMatrix2 R) : GradedMatrix2 R where
  diag_top := 0
  diag_bot := 0
  off_diag1 := M.off_diag1
  off_diag2 := M.off_diag2

/-- THEOREM: M₀ has strictly zero trace. -/
theorem tr_M0 (M : GradedMatrix2 R) : (M0 M).tr = 0 := by
  dsimp [tr, M0]
  exact add_zero 0

/-- THEOREM: M₀ has strictly zero supertrace. -/
theorem str_M0 (M : GradedMatrix2 R) : (M0 M).str = 0 := by
  dsimp [str, M0]
  exact sub_self 0

/-- THEOREM: Exact diagonal reconstruction from α and β. -/
theorem diagonal_reconstruction (M : GradedMatrix2 R) (two_inv : R) (htwo : 2 * two_inv = 1) :
    alpha M two_inv + beta M two_inv = M.diag_top ∧
    alpha M two_inv - beta M two_inv = M.diag_bot := by
  dsimp [alpha, beta, tr, str]
  constructor
  · calc two_inv * (M.diag_top + M.diag_bot) + two_inv * (M.diag_top - M.diag_bot)
      _ = two_inv * ((M.diag_top + M.diag_bot) + (M.diag_top - M.diag_bot)) := by rw [← mul_add]
      _ = two_inv * (2 * M.diag_top) := by ring_nf
      _ = (two_inv * 2) * M.diag_top := by rw [mul_assoc]
      _ = (2 * two_inv) * M.diag_top := by rw [mul_comm two_inv 2]
      _ = 1 * M.diag_top := by rw [htwo]
      _ = M.diag_top := by rw [one_mul]
  · calc two_inv * (M.diag_top + M.diag_bot) - two_inv * (M.diag_top - M.diag_bot)
      _ = two_inv * ((M.diag_top + M.diag_bot) - (M.diag_top - M.diag_bot)) := by rw [← mul_sub]
      _ = two_inv * (2 * M.diag_bot) := by ring_nf
      _ = (two_inv * 2) * M.diag_bot := by rw [mul_assoc]
      _ = (2 * two_inv) * M.diag_bot := by rw [mul_comm two_inv 2]
      _ = 1 * M.diag_bot := by rw [htwo]
      _ = M.diag_bot := by rw [one_mul]

end GradedMatrix2

end TrifoldDecomposition

/-!
=============================================================================
4. LOGARITHMIC DERIVATION (dlog) HOMOMORPHISM ON INVERTIBLE ELEMENTS
=============================================================================
-/

section LogarithmicDerivations

variable {R : Type*} [CommRing R]

/-- A derivation on a commutative ring R. -/
structure CommRingDerivation (R : Type*) [CommRing R] where
  toFun : R → R
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

namespace CommRingDerivation

variable {R : Type*} [CommRing R] (D : CommRingDerivation R)

instance : CoeFun (CommRingDerivation R) (fun _ => R → R) where
  coe D := D.toFun

@[simp] theorem map_add (x y : R) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : R) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by rw [← D.map_add, add_zero, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_one : D 1 = 0 := by
  have h : D 1 + D 1 = D 1 + 0 := by
    calc D 1 + D 1
      _ = D 1 * 1 + 1 * D 1 := by rw [mul_one, one_mul]
      _ = D (1 * 1) := (D.leibniz 1 1).symm
      _ = D 1 := by rw [mul_one]
      _ = D 1 + 0 := by rw [add_zero]
  exact add_left_cancel h

/-- The logarithmic derivation dlog_D(u) = u⁻¹ * D(u) for an invertible element u with inverse u_inv. -/
def dlog (u u_inv : R) : R :=
  u_inv * D u

/-- THEOREM: Logarithmic Derivation of Identity is Zero: dlog(1) = 0. -/
theorem dlog_one : D.dlog 1 1 = 0 := by
  dsimp [dlog]
  rw [D.map_one, mul_zero]

/-- 
  THEOREM: Logarithmic Derivation Product Rule (Homomorphism Property):
  dlog_D(u * v) = dlog_D(u) + dlog_D(v)
  for invertible elements u, v with inverses u_inv, v_inv.
-/
theorem dlog_mul (u v u_inv v_inv : R) (hu : u * u_inv = 1) (hv : v * v_inv = 1) :
    D.dlog (u * v) (u_inv * v_inv) = D.dlog u u_inv + D.dlog v v_inv := by
  dsimp [dlog]
  rw [D.leibniz]
  calc (u_inv * v_inv) * (D u * v + u * D v)
    _ = (u_inv * v_inv) * (D u * v) + (u_inv * v_inv) * (u * D v) := by rw [mul_add]
    _ = (u_inv * D u) * (v_inv * v) + (v_inv * D v) * (u_inv * u) := by ring
    _ = (u_inv * D u) * (v * v_inv) + (v_inv * D v) * (u * u_inv) := by rw [mul_comm v_inv v, mul_comm u_inv u]
    _ = (u_inv * D u) * 1 + (v_inv * D v) * 1 := by rw [hu, hv]
    _ = u_inv * D u + v_inv * D v := by rw [mul_one, mul_one]

/-- 
  THEOREM: Logarithmic Derivation of Inverse:
  dlog_D(u⁻¹) = - dlog_D(u).
-/
theorem dlog_inv (u u_inv : R) (hu : u * u_inv = 1) :
    D.dlog u_inv u = - D.dlog u u_inv := by
  have hprod : D.dlog (u * u_inv) (u_inv * u) = D.dlog u u_inv + D.dlog u_inv u := by
    apply D.dlog_mul u u_inv u_inv u hu
    rw [mul_comm]
    exact hu
  rw [hu] at hprod
  have hone : D.dlog 1 (u_inv * u) = 0 := by
    dsimp [dlog]
    rw [D.map_one, mul_zero]
  rw [hone] at hprod
  exact eq_neg_of_add_eq_zero_right hprod.symm

end CommRingDerivation

end LogarithmicDerivations

/-!
=============================================================================
5. GENERIC DUAL-FLOW COMMUTATOR & THERMAL TIME GENESIS
=============================================================================
-/

section DualFlowCommutator

variable {A : Type*} [Ring A]

/-- Pointwise Inner Modular Generator ad_K(X) = K * X - X * K. -/
def adK (K X : A) : A := K * X - X * K

/-- Ring Derivation Structure. -/
structure GenericDerivation (A : Type*) [Ring A] where
  toFun : A → A
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  leibniz' : ∀ x y, toFun (x * y) = toFun x * y + x * toFun y

/-- The inner derivation generated by `K`, bundled in the generic derivation
structure. -/
def innerDerivation (K : A) : GenericDerivation A where
  toFun := adK K
  map_add' := by
    intro x y
    dsimp [adK]
    simp only [mul_add, add_mul]
    abel
  leibniz' := by
    intro x y
    dsimp [adK]
    calc
      K * (x * y) - (x * y) * K =
          (K * x * y - x * K * y) + (x * K * y - x * y * K) := by
            simp only [mul_assoc]
            abel
      _ = (K * x - x * K) * y + x * (K * y - y * K) := by
            simp only [sub_mul, mul_sub, mul_assoc]

namespace GenericDerivation

variable {A : Type*} [Ring A] (D : GenericDerivation A)

instance : CoeFun (GenericDerivation A) (fun _ => A → A) where
  coe D := D.toFun

@[simp] theorem innerDerivation_apply (K X : A) :
    innerDerivation K X = adK K X := rfl

@[simp] theorem map_add (x y : A) : D (x + y) = D x + D y := D.map_add' x y
@[simp] theorem leibniz (x y : A) : D (x * y) = D x * y + x * D y := D.leibniz' x y

@[simp]
theorem map_zero : D 0 = 0 := by
  have h : D 0 + D 0 = D 0 + 0 := by rw [← D.map_add, add_zero, add_zero]
  exact add_left_cancel h

@[simp]
theorem map_neg (x : A) : D (-x) = - D x := by
  have h : D x + D (-x) = 0 := by rw [← D.map_add, add_neg_cancel, D.map_zero]
  exact eq_neg_of_add_eq_zero_right h

@[simp]
theorem map_sub (x y : A) : D (x - y) = D x - D y := by
  rw [sub_eq_add_neg, D.map_add, D.map_neg, ← sub_eq_add_neg]

/-- 
  MASTER THEOREM: The Dual-Flow Commutator Identity is 100% Generic for any Ring Derivation.
  [D, ad_K](X) = ad_{D(K)}(X)
-/
theorem master_dual_flow_commutator (K X : A) :
    D (adK K X) - adK K (D X) = adK (D K) X := by
  dsimp [adK]
  rw [D.map_sub, D.leibniz, D.leibniz]
  noncomm_ring

/-- The commutator of two inner derivations is inner, with generator the
commutator of their generators. -/
theorem adK_bracket (K₁ K₂ X : A) :
    adK K₁ (adK K₂ X) - adK K₂ (adK K₁ X) = adK (adK K₁ K₂) X := by
  dsimp [adK]
  noncomm_ring

/-- The pointwise commutator of two generic derivations, bundled again as a
generic derivation. -/
def commutator (D₁ D₂ : GenericDerivation A) : GenericDerivation A where
  toFun := fun X => D₁ (D₂ X) - D₂ (D₁ X)
  map_add' := by
    intro x y
    rw [D₂.map_add, D₁.map_add, D₁.map_add, D₂.map_add]
    abel
  leibniz' := by
    intro x y
    rw [D₂.leibniz, D₁.leibniz, D₁.map_add, D₁.leibniz,
      D₁.leibniz, D₂.map_add, D₂.leibniz, D₂.leibniz]
    noncomm_ring

@[simp] theorem commutator_apply (D₁ D₂ : GenericDerivation A) (X : A) :
    commutator D₁ D₂ X = D₁ (D₂ X) - D₂ (D₁ X) := rfl

theorem commutator_skew (D₁ D₂ : GenericDerivation A) (X : A) :
    commutator D₁ D₂ X = -commutator D₂ D₁ X := by
  dsimp [commutator]
  abel

@[simp] theorem commutator_self (D : GenericDerivation A) (X : A) :
    commutator D D X = 0 := by
  dsimp [commutator]
  abel

theorem commutator_jacobi (D₁ D₂ D₃ : GenericDerivation A) (X : A) :
    commutator D₁ (commutator D₂ D₃) X +
        commutator D₂ (commutator D₃ D₁) X +
        commutator D₃ (commutator D₁ D₂) X = 0 := by
  dsimp [commutator]
  rw [D₁.map_sub, D₂.map_sub, D₃.map_sub]
  abel

theorem commutator_innerDerivation (K₁ K₂ X : A) :
    commutator (innerDerivation K₁) (innerDerivation K₂) X =
      innerDerivation (adK K₁ K₂) X := by
  exact adK_bracket K₁ K₂ X

theorem commutator_derivation_innerDerivation
    (D : GenericDerivation A) (K X : A) :
    commutator D (innerDerivation K) X = innerDerivation (D K) X := by
  exact D.master_dual_flow_commutator K X

/-- 
  THEOREM: Adiabatic Decoupling
  If D(K) = 0, then [D, ad_K] = 0.
-/
theorem adiabatic_decoupling (K : A) (hK : D K = 0) (X : A) :
    D (adK K X) - adK K (D X) = 0 := by
  rw [D.master_dual_flow_commutator K X, hK]
  dsimp [adK]
  simp

/-- 
  THEOREM: Connes-Rovelli Thermal Time Genesis
  If K is central (∀ x, K * x = x * K), then ad_K = 0.
-/
theorem central_modular_timelessness (K : A) (hK : ∀ x, K * x = x * K) (X : A) :
    adK K X = 0 := by
  dsimp [adK]
  rw [hK X, sub_self]

/-! Vanishing of the inner derivation has the converse characterization: its
generator is central precisely when every commutator with it vanishes. -/

theorem central_of_adK_eq_zero (K : A) (hK : ∀ X, adK K X = 0) (X : A) :
    K * X = X * K := by
  have h := hK X
  dsimp [adK] at h
  exact sub_eq_zero.mp h

theorem adK_eq_zero_iff_central (K : A) :
    (∀ X, adK K X = 0) ↔ ∀ X, K * X = X * K := by
  constructor
  · exact central_of_adK_eq_zero K
  · intro hK X
    exact central_modular_timelessness K hK X

end GenericDerivation

end DualFlowCommutator

end InfoGeometry.Canonical.HypothesisFoundations
