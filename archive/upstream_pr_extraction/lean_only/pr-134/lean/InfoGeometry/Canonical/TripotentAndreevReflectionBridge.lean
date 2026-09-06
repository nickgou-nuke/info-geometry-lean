import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-!
# Tripotent Andreev Reflection Bridge

This owner module formalizes the exact operator algebra of Andreev reflection on
a tripotent carrier space $(V, A)$ with $A^3 = A$:

1. **Andreev Reflection Operator $\mathcal{A}$:**
   Involutive reflection $\mathcal{A}^2 = I$ that anticommutes with the Peirce defect:
   $$\{\mathcal{A}, A\} = \mathcal{A} A + A \mathcal{A} = 0$$

2. **Horizon Projection and Partition of Unity:**
   $$P_0 = I - A^2, \quad P_+ = \frac{1}{2}(A^2 + A), \quad P_- = \frac{1}{2}(A^2 - A), \qquad P_0 + P_+ + P_- = I$$
   with mutually orthogonal chiral sectors: $P_+ P_- = 0, P_- P_+ = 0, P_0 P_+ = 0, P_0 P_- = 0$.

3. **Zero-Mode Horizon Stability:**
   $$[\mathcal{A}, A^2] = 0 \implies \boxed{[\mathcal{A}, P_0] = 0}$$
   preserving the zero-mode carrier subspace $\mathcal{H}_0 = \ker A = \operatorname{im} P_0$.

4. **Particle-Hole Chiral Exchange:**
   $$\boxed{\mathcal{A} P_+ = P_- \mathcal{A}, \qquad \mathcal{A} P_- = P_+ \mathcal{A}}$$
   swapping the positive and negative eigenvalue sectors: $\mathcal{A}(V_+) = V_-$.

5. **Peirce Parity Commutation:**
   $$[\mathcal{A}, M] = 0 \qquad \text{where } M = I - 2A^2 = 2P_0 - I.$$
-/

noncomputable section

namespace InfoGeometry.Canonical.TripotentAndreevReflectionBridge

structure TripotentAndreevDatum (V : Type*) [AddCommGroup V] [Module ℝ V] where
  A : Module.End ℝ V
  R : Module.End ℝ V
  A_tripotent : A * A * A = A
  R_involutive : R * R = 1
  R_anticommute_A : R * A = - A * R

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The zero-mode horizon projector: $P_0 = I - A^2$. -/
def zeroModeProjector (d : TripotentAndreevDatum V) : Module.End ℝ V :=
  1 - d.A * d.A

/-- The positive chiral sector projector: $P_+ = \frac{1}{2}(A^2 + A)$. -/
def plusProjector (d : TripotentAndreevDatum V) : Module.End ℝ V :=
  (1 / 2 : ℝ) • (d.A * d.A + d.A)

/-- The negative chiral sector projector: $P_- = \frac{1}{2}(A^2 - A)$. -/
def minusProjector (d : TripotentAndreevDatum V) : Module.End ℝ V :=
  (1 / 2 : ℝ) • (d.A * d.A - d.A)

/-- The Peirce fermion parity operator: $M = I - 2A^2 = 2P_0 - I$. -/
def peirceParity (d : TripotentAndreevDatum V) : Module.End ℝ V :=
  1 - (2 : ℝ) • (d.A * d.A)

theorem tripotent_sq_idempotent (d : TripotentAndreevDatum V) :
    (d.A * d.A) * (d.A * d.A) = d.A * d.A := by
  calc
    (d.A * d.A) * (d.A * d.A) = (d.A * d.A * d.A) * d.A := by
      simp [mul_assoc]
    _ = d.A * d.A := by rw [d.A_tripotent]

/-- 🏆 THEOREM 1: The tripotent zero-mode projector is genuinely idempotent: $P_0^2 = P_0$. -/
theorem zeroModeProjector_idempotent (d : TripotentAndreevDatum V) :
    zeroModeProjector d * zeroModeProjector d = zeroModeProjector d := by
  dsimp [zeroModeProjector]
  rw [sub_mul, mul_sub, mul_one, one_mul, mul_sub, mul_one,
    tripotent_sq_idempotent d]
  abel

/-- 🏆 THEOREM 2: Partition of unity: $P_0 + P_+ + P_- = I$. -/
theorem projector_sum_eq_one (d : TripotentAndreevDatum V) :
    zeroModeProjector d + plusProjector d + minusProjector d = 1 := by
  ext x
  simp only [zeroModeProjector, plusProjector, minusProjector,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  module

theorem projectors_sum_to_id (d : TripotentAndreevDatum V) :
    zeroModeProjector d + plusProjector d + minusProjector d = 1 :=
  projector_sum_eq_one d

/-- 🏆 THEOREM 3: Orthogonality of chiral sectors: $P_+ P_- = 0$ and $P_- P_+ = 0$. -/
theorem plus_mul_minus_eq_zero (d : TripotentAndreevDatum V) :
    plusProjector d * minusProjector d = 0 := by
  dsimp [plusProjector, minusProjector]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_prod : (d.A * d.A + d.A) * (d.A * d.A - d.A) = 0 := by
    rw [add_mul, mul_sub, mul_sub]
    rw [tripotent_sq_idempotent d]
    have h1 : (d.A * d.A) * d.A = d.A := d.A_tripotent
    have h2 : d.A * (d.A * d.A) = d.A := by
      rw [← mul_assoc, d.A_tripotent]
    rw [h1, h2]
    ext x
    simp only [one_mul, mul_one, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply]
    abel
  rw [h_prod, smul_zero]

theorem minus_mul_plus_eq_zero (d : TripotentAndreevDatum V) :
    minusProjector d * plusProjector d = 0 := by
  dsimp [plusProjector, minusProjector]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_prod : (d.A * d.A - d.A) * (d.A * d.A + d.A) = 0 := by
    rw [sub_mul, mul_add, mul_add]
    rw [tripotent_sq_idempotent d]
    have h1 : (d.A * d.A) * d.A = d.A := d.A_tripotent
    have h2 : d.A * (d.A * d.A) = d.A := by
      rw [← mul_assoc, d.A_tripotent]
    rw [h1, h2]
    ext x
    simp only [one_mul, mul_one, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply]
    abel
  rw [h_prod, smul_zero]

theorem plusProjector_mul_minusProjector (d : TripotentAndreevDatum V) :
    plusProjector d * minusProjector d = 0 :=
  plus_mul_minus_eq_zero d

theorem plusProjector_sq (d : TripotentAndreevDatum V) :
    plusProjector d * plusProjector d = plusProjector d := by
  dsimp [plusProjector]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hleft : (d.A * d.A) * d.A = d.A := d.A_tripotent
  have hright : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  rw [add_mul, mul_add, mul_add, h4, hleft, hright]
  ext x
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  module

theorem minusProjector_sq (d : TripotentAndreevDatum V) :
    minusProjector d * minusProjector d = minusProjector d := by
  dsimp [minusProjector]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hleft : (d.A * d.A) * d.A = d.A := d.A_tripotent
  have hright : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  rw [sub_mul, mul_sub, mul_sub, h4, hleft, hright]
  ext x
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  module

theorem zeroMode_mul_plusProjector (d : TripotentAndreevDatum V) :
    zeroModeProjector d * plusProjector d = 0 := by
  dsimp [zeroModeProjector, plusProjector]
  rw [mul_smul_comm]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hleft : (d.A * d.A) * d.A = d.A := d.A_tripotent
  have hprod : (1 - d.A * d.A) * (d.A * d.A + d.A) = 0 := by
    rw [sub_mul, mul_add, mul_add, h4, hleft]
    simp only [one_mul, mul_one]
    ext x
    simp only [one_mul, mul_one, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply]
    abel
  rw [hprod, smul_zero]

theorem plusProjector_mul_zeroMode (d : TripotentAndreevDatum V) :
    plusProjector d * zeroModeProjector d = 0 := by
  dsimp [zeroModeProjector, plusProjector]
  rw [smul_mul_assoc]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hright : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  have hprod : (d.A * d.A + d.A) * (1 - d.A * d.A) = 0 := by
    rw [add_mul, mul_sub, mul_sub, h4, hright]
    simp only [one_mul, mul_one]
    ext x
    simp only [one_mul, mul_one, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.zero_apply]
    abel
  rw [hprod, smul_zero]

theorem zeroMode_mul_minusProjector (d : TripotentAndreevDatum V) :
    zeroModeProjector d * minusProjector d = 0 := by
  dsimp [zeroModeProjector, minusProjector]
  rw [mul_smul_comm]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hleft : (d.A * d.A) * d.A = d.A := d.A_tripotent
  have hprod : (1 - d.A * d.A) * (d.A * d.A - d.A) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, h4, hleft]
    simp only [one_mul, mul_one]
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    abel
  rw [hprod, smul_zero]

theorem minusProjector_mul_zeroMode (d : TripotentAndreevDatum V) :
    minusProjector d * zeroModeProjector d = 0 := by
  dsimp [zeroModeProjector, minusProjector]
  rw [smul_mul_assoc]
  have h4 : (d.A * d.A) * (d.A * d.A) = d.A * d.A :=
    tripotent_sq_idempotent d
  have hright : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  have hprod : (d.A * d.A - d.A) * (1 - d.A * d.A) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, h4, hright]
    simp only [one_mul, mul_one]
    ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    abel
  rw [hprod, smul_zero]

/-- 🏆 THEOREM 4: Horizon Annihilation: $A P_0 = 0$ and $P_0 A = 0$. -/
theorem tripotent_mul_zeroModeProjector (d : TripotentAndreevDatum V) :
    d.A * zeroModeProjector d = 0 := by
  dsimp [zeroModeProjector]
  rw [mul_sub, mul_one]
  rw [← mul_assoc, d.A_tripotent]
  exact sub_self _

theorem zeroModeProjector_mul_tripotent (d : TripotentAndreevDatum V) :
    zeroModeProjector d * d.A = 0 := by
  dsimp [zeroModeProjector]
  rw [sub_mul, one_mul]
  rw [d.A_tripotent]
  exact sub_self _

/-- The projector-defined zero-mode carrier is exactly the tripotent kernel. -/
theorem zeroMode_range_eq_ker_A (d : TripotentAndreevDatum V) :
    LinearMap.range (zeroModeProjector d) = LinearMap.ker d.A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    have h := congrArg (fun T : Module.End ℝ V => T y)
      (tripotent_mul_zeroModeProjector d)
    exact h
  · intro hx
    have hAx : d.A x = 0 := LinearMap.mem_ker.mp hx
    refine ⟨x, ?_⟩
    simp [zeroModeProjector, hAx]

theorem A_mul_zeroModeProjector (d : TripotentAndreevDatum V) :
    d.A * zeroModeProjector d = 0 :=
  tripotent_mul_zeroModeProjector d

theorem A_mul_plusProjector (d : TripotentAndreevDatum V) :
    d.A * plusProjector d = plusProjector d := by
  dsimp [plusProjector]
  rw [mul_smul_comm]
  congr 1
  rw [mul_add]
  have h1 : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  rw [h1, add_comm]

theorem A_mul_minusProjector (d : TripotentAndreevDatum V) :
    d.A * minusProjector d = - minusProjector d := by
  dsimp [minusProjector]
  rw [mul_smul_comm]
  have h1 : d.A * (d.A * d.A) = d.A := by
    rw [← mul_assoc, d.A_tripotent]
  have h_inner : d.A * (d.A * d.A - d.A) = - (d.A * d.A - d.A) := by
    rw [mul_sub, h1]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.neg_apply]
    abel
  rw [h_inner, smul_neg]

/-- 🏆 THEOREM 5: Andreev Reflection Involutivity and Anticommutation:
    $\mathcal{A}^2 = I, \qquad \{\mathcal{A}, A\} = \mathcal{A} A + A \mathcal{A} = 0$. -/
theorem andreev_involutive (d : TripotentAndreevDatum V) :
    d.R * d.R = 1 :=
  d.R_involutive

theorem andreev_anticommute (d : TripotentAndreevDatum V) :
    d.R * d.A + d.A * d.R = 0 := by
  rw [d.R_anticommute_A, neg_mul, neg_add_cancel]

/-- 🏆 THEOREM 6: Andreev reflection commutes with $A^2$: $[\mathcal{A}, A^2] = 0$. -/
theorem andreev_comm_A_sq (d : TripotentAndreevDatum V) :
    d.R * (d.A * d.A) = (d.A * d.A) * d.R := by
  have h : d.R * d.A = - (d.A * d.R) := by
    rw [d.R_anticommute_A, neg_mul]
  have h2 : d.R * (d.A * d.A) = (d.R * d.A) * d.A := (mul_assoc d.R d.A d.A).symm
  rw [h2, h, neg_mul, mul_assoc, d.R_anticommute_A, neg_mul, mul_neg, neg_neg, mul_assoc]

/-- 🏆 THEOREM 7: Andreev reflection commutes with the zero-mode projector: $[\mathcal{A}, P_0] = 0$. -/
theorem andreev_comm_zeroMode (d : TripotentAndreevDatum V) :
    d.R * (zeroModeProjector d) = (zeroModeProjector d) * d.R := by
  dsimp [zeroModeProjector]
  rw [mul_sub, sub_mul, mul_one, one_mul]
  rw [andreev_comm_A_sq d]

theorem andreev_comm_bracket_zeroMode (d : TripotentAndreevDatum V) :
    d.R * zeroModeProjector d - zeroModeProjector d * d.R = 0 := by
  rw [andreev_comm_zeroMode d, sub_self]

/-- 🏆 THEOREM 8: Particle-Hole Chiral Exchange:
    $$\mathcal{A} P_+ = P_- \mathcal{A}, \qquad \mathcal{A} P_- = P_+ \mathcal{A}.$$ -/
theorem andreev_mul_plus_eq_minus_mul (d : TripotentAndreevDatum V) :
    d.R * (plusProjector d) = (minusProjector d) * d.R := by
  dsimp [plusProjector, minusProjector]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_add, sub_mul]
  rw [andreev_comm_A_sq d, d.R_anticommute_A]
  rw [sub_eq_add_neg, neg_mul]

theorem andreev_mul_minus_eq_plus_mul (d : TripotentAndreevDatum V) :
    d.R * (minusProjector d) = (plusProjector d) * d.R := by
  dsimp [plusProjector, minusProjector]
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, add_mul]
  rw [andreev_comm_A_sq d, d.R_anticommute_A]
  rw [neg_mul, sub_neg_eq_add]

theorem andreev_mul_plus_eq_minus (d : TripotentAndreevDatum V) :
    d.R * (plusProjector d) = (minusProjector d) * d.R :=
  andreev_mul_plus_eq_minus_mul d

theorem andreev_mul_minus_eq_plus (d : TripotentAndreevDatum V) :
    d.R * (minusProjector d) = (plusProjector d) * d.R :=
  andreev_mul_minus_eq_plus_mul d

/-- 🏆 THEOREM 9: Andreev reflection commutes with the Peirce parity grading: $[\mathcal{A}, M] = 0$. -/
theorem andreev_comm_peirceParity (d : TripotentAndreevDatum V) :
    d.R * (peirceParity d) = (peirceParity d) * d.R := by
  dsimp [peirceParity]
  rw [mul_sub, sub_mul, mul_one, one_mul]
  rw [mul_smul_comm, smul_mul_assoc]
  rw [andreev_comm_A_sq d]

theorem andreev_comm_bracket_peirceParity (d : TripotentAndreevDatum V) :
    d.R * peirceParity d - peirceParity d * d.R = 0 := by
  rw [andreev_comm_peirceParity d, sub_self]

/-- 🏆 THEOREM 10: Horizon Invariance: $\mathcal{A}(\ker A) \subseteq \ker A$. -/
theorem andreev_preserves_ker_A (d : TripotentAndreevDatum V)
    (x : V) (hx : d.A x = 0) :
    d.A (d.R x) = 0 := by
  have h_anti : (d.A * d.R) x = - (d.R * d.A) x := by
    have h : d.A * d.R = - (d.R * d.A) := by
      rw [d.R_anticommute_A, neg_mul, neg_neg]
    rw [h, LinearMap.neg_apply]
  have h_zero : (d.R * d.A) x = 0 := by
    show d.R (d.A x) = 0
    rw [hx, map_zero]
  calc
    d.A (d.R x) = (d.A * d.R) x := rfl
    _ = - (d.R * d.A) x := h_anti
    _ = - (0 : V) := by rw [h_zero]
    _ = 0 := neg_zero

/-- Andreev reflection preserves the tripotent kernel in both directions. -/
theorem andreev_mem_ker_A_iff (d : TripotentAndreevDatum V) (x : V) :
    d.A x = 0 ↔ d.A (d.R x) = 0 := by
  constructor
  · exact andreev_preserves_ker_A d x
  · intro hx
    have h' := andreev_preserves_ker_A d (d.R x) hx
    have hR : d.R (d.R x) = x := by
      have hR' := congrArg (fun T : Module.End ℝ V => T x)
        (andreev_involutive d)
      simpa only [Module.End.mul_apply, Module.End.one_apply] using hR'
    calc
      d.A x = d.A (d.R (d.R x)) := by
        rw [hR]
      _ = 0 := h'

/-- The Andreev involution preserves the projector-defined zero-mode carrier. -/
theorem andreev_preserves_zeroMode_range (d : TripotentAndreevDatum V)
    (x : V) (hx : x ∈ LinearMap.range (zeroModeProjector d)) :
    d.R x ∈ LinearMap.range (zeroModeProjector d) := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨d.R y, ?_⟩
  have hcomm := andreev_comm_zeroMode d
  have happ := congrArg (fun F : Module.End ℝ V => F y) hcomm
  simpa only [Module.End.mul_apply] using happ.symm

/-- Andreev reflection preserves the projector-defined zero-mode range in both directions. -/
theorem andreev_mem_zeroMode_range_iff (d : TripotentAndreevDatum V) (x : V) :
    x ∈ LinearMap.range (zeroModeProjector d) ↔
      d.R x ∈ LinearMap.range (zeroModeProjector d) := by
  constructor
  · exact andreev_preserves_zeroMode_range d x
  · intro hx
    have h' := andreev_preserves_zeroMode_range d (d.R x) hx
    rcases h' with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hR : d.R (d.R x) = x := by
      have hR' := congrArg (fun T : Module.End ℝ V => T x)
        (andreev_involutive d)
      simpa only [Module.End.mul_apply, Module.End.one_apply] using hR'
    calc
      (zeroModeProjector d) y = d.R (d.R x) := hy
      _ = x := hR

/-- 🏆 THEOREM 11: Chiral Eigenspace Reflection:
    $A x = x \implies A(\mathcal{A} x) = -(\mathcal{A} x)$, and
    $A x = -x \implies A(\mathcal{A} x) = \mathcal{A} x$. -/
theorem andreev_swaps_plus_eigenspace (d : TripotentAndreevDatum V)
    (x : V) (hx : d.A x = x) :
    d.A (d.R x) = - (d.R x) := by
  have h_anti : (d.A * d.R) x = - (d.R * d.A) x := by
    have h : d.A * d.R = - (d.R * d.A) := by
      rw [d.R_anticommute_A, neg_mul, neg_neg]
    rw [h, LinearMap.neg_apply]
  calc
    d.A (d.R x) = (d.A * d.R) x := rfl
    _ = - (d.R * d.A) x := h_anti
    _ = - d.R (d.A x) := rfl
    _ = - d.R x := by rw [hx]

theorem andreev_swaps_minus_eigenspace (d : TripotentAndreevDatum V)
    (x : V) (hx : d.A x = - x) :
    d.A (d.R x) = d.R x := by
  have h_anti : (d.A * d.R) x = - (d.R * d.A) x := by
    have h : d.A * d.R = - (d.R * d.A) := by
      rw [d.R_anticommute_A, neg_mul, neg_neg]
    rw [h, LinearMap.neg_apply]
  calc
    d.A (d.R x) = (d.A * d.R) x := rfl
    _ = - (d.R * d.A) x := h_anti
    _ = - d.R (d.A x) := rfl
    _ = - d.R (- x) := by rw [hx]
    _ = - (- d.R x) := by rw [map_neg]
    _ = d.R x := neg_neg _

end InfoGeometry.Canonical.TripotentAndreevReflectionBridge
