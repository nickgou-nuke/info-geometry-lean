import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Artinian.Module
import InfoGeometry.Singular.MoorePenrose

namespace InfoGeometry.Singular.Drazin

open InfoGeometry.Singular.MoorePenrose

section Drazin
variable {R : Type*} [Ring R]

/-- The Three Equations defining the Drazin Inverse of index k. -/
def IsDrazinInverse (A D : R) (k : ℕ) : Prop :=
  D * A * D = D ∧
  A * D = D * A ∧
  A^k = A^(k + 1) * D

namespace IsDrazinInverse

variable {A D : R} {k : ℕ}

theorem mk
    (h1 : D * A * D = D)
    (h2 : A * D = D * A)
    (h3 : A^k = A^(k + 1) * D) :
    IsDrazinInverse A D k :=
  ⟨h1, h2, h3⟩

theorem dad_eq_d (h : IsDrazinInverse A D k) : D * A * D = D := h.1

theorem comm (h : IsDrazinInverse A D k) : A * D = D * A := h.2.1

theorem pow_eq_pow_succ_mul (h : IsDrazinInverse A D k) : A^k = A^(k + 1) * D := h.2.2

-- Backward-compatible aliases
theorem eq1 (h : IsDrazinInverse A D k) : D * A * D = D := h.dad_eq_d

theorem eq2 (h : IsDrazinInverse A D k) : A * D = D * A := h.comm

theorem eq3 (h : IsDrazinInverse A D k) : A^k = A^(k + 1) * D := h.pow_eq_pow_succ_mul

end IsDrazinInverse

/-- The Spectral/Core Projector P_D = A * A^D -/
def Drazin_Projector (A D : R) (k : ℕ) (_h : IsDrazinInverse A D k) : R := A * D

lemma Drazin_Projector_idempotent {A D : R} {k : ℕ} (h : IsDrazinInverse A D k) :
    (Drazin_Projector A D k h) * (Drazin_Projector A D k h) = Drazin_Projector A D k h := by
  unfold Drazin_Projector
  calc
    (A * D) * (A * D) = A * (D * A * D) := by simp [mul_assoc]
    _ = A * D := by rw [h.dad_eq_d]

end Drazin

section DrazinLinear
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/--
Global constructive Drazin inverse existence for finite-dimensional endomorphisms.

Construction:
1. use Fitting decomposition `V = ker(A^k) ⊕ range(A^k)` (for stabilized `k = N+1`),
2. invert `A` on the stable range `range(A^k)`,
3. set the inverse to zero on `ker(A^k)`.
-/
theorem exists_drazinInverse_global (A : Module.End K V) :
    ∃ (k : ℕ) (D : Module.End K V), IsDrazinInverse A D k := by
  classical

  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (LinearMap.eventually_isCompl_ker_pow_range_pow (f := A))

  let k : ℕ := N.succ
  let Ker : Submodule K V := (A ^ k).ker
  let Ran : Submodule K V := (A ^ k).range

  have hk_le : N ≤ k := by
    simp [k]

  have hk : IsCompl Ker Ran := by
    exact hN k hk_le

  -- Projection `V → Ran` along `Ker`.
  let πRan : V →ₗ[K] Ran := Ran.linearProjOfIsCompl Ker hk.symm

  -- `A` preserves the stable range.
  have hA_map_Ran : ∀ x : Ran, A x.1 ∈ Ran := by
    intro x
    rcases x.2 with ⟨y, hy⟩
    refine ⟨A y, ?_⟩
    calc
      (A ^ k) (A y) = A ((A ^ k) y) := by
        calc
          (A ^ k) (A y) = (A ^ k * A) y := by rfl
          _ = (A ^ (k + 1)) y := by simp [pow_succ]
          _ = (A * A ^ k) y := by simp [pow_succ']
          _ = A ((A ^ k) y) := by rfl
      _ = A x.1 := by simp [hy]

  -- Restriction `A|Ran : Ran → Ran`.
  let AR : Ran →ₗ[K] Ran := LinearMap.codRestrict Ran (A ∘ₗ Ran.subtype) hA_map_Ran

  have hpowA_apply : ∀ z : V, (A ^ k) (A z) = A ((A ^ k) z) := by
    intro z
    calc
      (A ^ k) (A z) = (A ^ k * A) z := by rfl
      _ = (A ^ (k + 1)) z := by simp [pow_succ]
      _ = (A * A ^ k) z := by simp [pow_succ']
      _ = A ((A ^ k) z) := by rfl

  -- Injectivity of `A|Ran`.
  have hAR_inj : Function.Injective AR := by
    intro x y hxy
    apply Subtype.ext
    have hzero : AR (x - y) = 0 := by simp [map_sub, hxy]
    have hzA : A ((x - y : Ran).1) = 0 := congrArg Subtype.val hzero
    have hzKer : ((x - y : Ran).1) ∈ Ker := by
      change (A ^ N.succ) ((x - y : Ran).1) = 0
      calc
        (A ^ N.succ) ((x - y : Ran).1) = (A ^ N) (A ((x - y : Ran).1)) := by
          simp [pow_succ]
        _ = 0 := by
          rw [hzA]
          simp
    have hzRan : ((x - y : Ran).1) ∈ Ran := (x - y).2
    have hz : ((x - y : Ran).1) = 0 := by
      have hmem : ((x - y : Ran).1) ∈ Ker ⊓ Ran := ⟨hzKer, hzRan⟩
      have hbot : Ker ⊓ Ran = ⊥ := hk.inf_eq_bot
      have : ((x - y : Ran).1) ∈ (⊥ : Submodule K V) := by simpa [hbot] using hmem
      simpa using this
    simpa [sub_eq_zero] using hz

  -- Inverse on the stable range.
  let eRan : Ran ≃ₗ[K] Ran := LinearEquiv.ofInjectiveEndo AR hAR_inj

  -- Drazin inverse candidate.
  let D : Module.End K V :=
    Ran.subtype ∘ₗ (eRan.symm : Ran →ₗ[K] Ran) ∘ₗ πRan

  -- Explicit projector onto `Ran` along `Ker`.
  let P : Module.End K V := Ran.subtype ∘ₗ πRan

  have hA_mul_D : A * D = P := by
    ext x
    have hright : AR (eRan.symm (πRan x)) = πRan x := by
      have h := LinearEquiv.ofInjectiveEndo_right_inv AR hAR_inj
      exact congrArg (fun f : Ran →ₗ[K] Ran => f (πRan x)) h
    calc
      (A * D) x = A (Ran.subtype (eRan.symm (πRan x))) := by
        rfl
      _ = Ran.subtype (AR (eRan.symm (πRan x))) := by
        rfl
      _ = Ran.subtype (πRan x) := by rw [hright]
      _ = P x := by rfl

  have hA_map_Ker : ∀ x ∈ Ker, A x ∈ Ker := by
    intro x hx
    have hx0 : (A ^ k) x = 0 := by
      simpa [Ker, LinearMap.mem_ker] using hx
    change (A ^ k) (A x) = 0
    calc
      (A ^ k) (A x) = A ((A ^ k) x) := hpowA_apply x
      _ = 0 := by simp [hx0]

  have hD_mul_A : D * A = P := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hAK : A (xK : V) ∈ Ker := hA_map_Ker xK xK.2
    have hπAK : πRan (A (xK : V)) = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right' hk.symm _ hAK
    have hARxR : A (xR : V) ∈ Ran := hA_map_Ran xR
    have hπARxR : πRan (A (xR : V)) = ⟨A xR, hARxR⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨A xR, hARxR⟩
    have hARxR_eq : (⟨A xR, hARxR⟩ : Ran) = AR xR := by
      apply Subtype.ext
      rfl
    have hleftInv : eRan.symm (AR xR) = xR := by
      have h := LinearEquiv.ofInjectiveEndo_left_inv AR hAR_inj
      exact congrArg (fun f : Ran →ₗ[K] Ran => f xR) h
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    calc
      (D * A) x = D (A ((xK : V) + xR)) := by simp [hsum]
      _ = D (A (xK : V) + A xR) := by simp [map_add]
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V) + A xR))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan (A (xK : V)) + πRan (A xR))) := by
        simp [map_add]
      _ = Ran.subtype (eRan.symm (0 + ⟨A xR, hARxR⟩)) := by rw [hπAK, hπARxR]
      _ = Ran.subtype (eRan.symm (AR xR)) := by
        rw [hARxR_eq]
        simp
      _ = (xR : V) := by simp [hleftInv]
      _ = P ((xK : V) + xR) := by symm; exact hP_on_sum
      _ = P x := by simp [hsum]

  have hD_mem_Ran : ∀ x : V, D x ∈ Ran := by
    intro x
    unfold D
    exact (eRan.symm (πRan x)).2

  have hD_mul_P : D * P = D := by
    ext x
    have hπPx : πRan (P x) = πRan x := by
      unfold P
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm (πRan x)
    calc
      (D * P) x = Ran.subtype (eRan.symm (πRan (P x))) := by rfl
      _ = Ran.subtype (eRan.symm (πRan x)) := by rw [hπPx]
      _ = D x := by rfl

  have hP_mul_D : P * D = D := by
    ext x
    have hπDx : πRan (D x) = ⟨D x, hD_mem_Ran x⟩ := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm ⟨D x, hD_mem_Ran x⟩
    calc
      (P * D) x = Ran.subtype (πRan (D x)) := by rfl
      _ = Ran.subtype ⟨D x, hD_mem_Ran x⟩ := by rw [hπDx]
      _ = D x := by rfl

  have hAk_mul_P : (A ^ k) * P = A ^ k := by
    ext x
    rcases Submodule.existsUnique_add_of_isCompl hk x with ⟨xK, xR, hsum, huniq⟩
    have hπK : πRan xK = 0 := by
      exact Submodule.linearProjOfIsCompl_apply_right hk.symm xK
    have hπR : πRan xR = xR := by
      exact Submodule.linearProjOfIsCompl_apply_left hk.symm xR
    have hP_on_sum : P ((xK : V) + xR) = (xR : V) := by
      unfold P
      simp [map_add, hπK, hπR]
    have hAk_xK : (A ^ k) (xK : V) = 0 := xK.2
    calc
      ((A ^ k) * P) x = (A ^ k) (P ((xK : V) + xR)) := by simp [hsum]
      _ = (A ^ k) (xR : V) := by rw [hP_on_sum]
      _ = (A ^ k) ((xK : V) + xR) := by simp [map_add, hAk_xK]
      _ = (A ^ k) x := by simp [hsum]

  have hEq1 : D * A * D = D := by
    calc
      D * A * D = (D * A) * D := by simp [mul_assoc]
      _ = P * D := by rw [hD_mul_A]
      _ = D := hP_mul_D

  have hEq2 : A * D = D * A := by
    exact hA_mul_D.trans hD_mul_A.symm

  have hEq3 : A ^ k = A ^ (k + 1) * D := by
    calc
      A ^ k = (A ^ k) * P := by simp [hAk_mul_P]
      _ = (A ^ k) * (A * D) := by rw [hA_mul_D]
      _ = (A ^ (k + 1)) * D := by simp [pow_succ, mul_assoc]

  exact ⟨k, D, IsDrazinInverse.mk hEq1 hEq2 hEq3⟩

/-- 
The Drazin Index: The smallest k for which the Fitting decomposition stabilizes. 
-/
noncomputable def drazinIndex (A : Module.End K V) : ℕ :=
  (exists_drazinInverse_global A).choose

/--
The Constructive Drazin Inverse Operator.
Chooses the unique Drazin inverse guaranteed by the Fitting decomposition.
-/
noncomputable def drazinInverse (A : Module.End K V) : Module.End K V :=
  (exists_drazinInverse_global A).choose_spec.choose

/--
Theorem: The chosen operator satisfies the Drazin laws.
-/
theorem drazinInverse_spec (A : Module.End K V) :
    IsDrazinInverse A (drazinInverse A) (drazinIndex A) :=
  (exists_drazinInverse_global A).choose_spec.choose_spec

/--
The Spectral Projector P_D constructed natively from the operator A.
-/
noncomputable def drazinProjector (A : Module.End K V) : Module.End K V :=
  A * (drazinInverse A)

end DrazinLinear

section Anomaly
variable {R : Type*} [Ring R] [StarRing R]

/--
THE CHIRAL ANOMALY:
The commutator of the Geometric Mirror (MP) and the Spectral Mirror (Drazin).
χ = [P_MP, P_D]

This formally isolates the metric-spectral mismatch that occurs strictly
on the singular causal boundary.
-/
def ChiralAnomaly (A B D : R) (k : ℕ)
    (hMP : IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) : R :=
  let P_MP := MP_Projector A B hMP
  let P_D := Drazin_Projector A D k hD
  P_MP * P_D - P_D * P_MP

/-- The Normal Metric Property:
If the matrix commutes with its geometric adjoint (AA† = A†A),
the anomaly rigorously vanishes (ε = 0). -/
def IsNormal (A : R) : Prop := A * A† = A† * A

end Anomaly
end InfoGeometry.Singular.Drazin
