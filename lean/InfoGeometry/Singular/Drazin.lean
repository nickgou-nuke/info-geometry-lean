import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Artinian.Module
import InfoGeometry.Singular.MoorePenrose

namespace InfoGeometry.Singular.Drazin

open MoorePenrose

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

namespace IsDrazinInverse

variable {A D : R} {k ℓ : ℕ}

/--
Lift a Drazin witness from index `k` to any larger index `ℓ`.
-/
theorem lift (h : IsDrazinInverse A D k) (hkℓ : k ≤ ℓ) :
    IsDrazinInverse A D ℓ := by
  rcases Nat.exists_eq_add_of_le hkℓ with ⟨t, rfl⟩
  have hcommDA : Commute D A := h.comm.symm
  refine IsDrazinInverse.mk h.dad_eq_d h.comm ?_
  calc
    A ^ (k + t) = A ^ k * A ^ t := by rw [pow_add]
    _ = (A ^ (k + 1) * D) * A ^ t := by rw [h.pow_eq_pow_succ_mul]
    _ = A ^ (k + 1) * (D * A ^ t) := by simp [mul_assoc]
    _ = A ^ (k + 1) * (A ^ t * D) := by rw [(hcommDA.pow_right t).eq]
    _ = (A ^ (k + 1) * A ^ t) * D := by simp [mul_assoc]
    _ = A ^ ((k + 1) + t) * D := by rw [← pow_add]
    _ = A ^ (k + t + 1) * D := by
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end IsDrazinInverse

namespace IsDrazinInverse

/-- An idempotent is its own Drazin inverse at index `1`. -/
theorem of_idempotent {P : R} (hP : P * P = P) :
    IsDrazinInverse P P 1 := by
  refine mk ?_ rfl ?_
  · simp [hP]
  · simp [pow_two, hP]

end IsDrazinInverse

section RootStar

variable [StarRing R]

namespace IsDrazinInverse

variable {A D : R} {k : ℕ}

/-- Taking adjoints transports a Drazin inverse of `A` to one of `A†`. -/
theorem star_isDrazinInverse (h : IsDrazinInverse A D k) :
    IsDrazinInverse A† D† k := by
  have hcommStar : D† * A† = A† * D† := by
    simpa using congrArg (fun x : R => x†) h.comm
  refine mk ?_ hcommStar.symm ?_
  · simpa [mul_assoc] using congrArg (fun x : R => x†) h.dad_eq_d
  · have hpowStar : A† ^ k = D† * A† ^ (k + 1) := by
      simpa using congrArg (fun x : R => x†) h.pow_eq_pow_succ_mul
    have hcomm : Commute A† D† := hcommStar.symm
    calc
      A† ^ k = D† * A† ^ (k + 1) := hpowStar
      _ = A† ^ (k + 1) * D† := by
        exact (hcomm.pow_left (k + 1)).eq.symm

end IsDrazinInverse

end RootStar

/-- A positive power of an idempotent is itself. -/
lemma pow_succ_eq_of_idempotent {R : Type*} [Monoid R] {P : R}
    (hP : P * P = P) :
    ∀ n : ℕ, P ^ (n + 1) = P := by
  intro n
  induction n with
  | zero =>
      simp [pow_succ]
  | succ n ih =>
      calc
        P ^ (n.succ + 1) = P ^ (n + 1) * P := by
          simp [pow_succ]
        _ = P * P := by rw [ih]
        _ = P := hP

/-- The Drazin projector attached to a Drazin witness is idempotent. -/
lemma drazin_projector_idempotent'
    {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k) :
    (A * D) * (A * D) = A * D := by
  calc
    (A * D) * (A * D) = A * (D * A * D) := by simp [mul_assoc]
    _ = A * D := by rw [h.dad_eq_d]

/--
For a positive-index Drazin witness, the mixed power collapses to the projector
`A * D`.
-/
lemma mul_pow_eq_drazinProjector_of_pos
    {A D : R} {n : ℕ}
    (h : IsDrazinInverse A D (n + 1)) :
    D ^ (n + 1) * A ^ (n + 1) = A * D := by
  have hcommAD : Commute A D := h.comm
  have hcommDA : Commute D A := hcommAD.symm
  have hIdem : (A * D) * (A * D) = A * D :=
    drazin_projector_idempotent' h
  calc
    D ^ (n + 1) * A ^ (n + 1) = (D * A) ^ (n + 1) := by
      simpa using (hcommDA.mul_pow (n + 1)).symm
    _ = (A * D) ^ (n + 1) := by
      rw [h.comm.symm]
    _ = A * D := pow_succ_eq_of_idempotent hIdem n

/--
Uniqueness of the Drazin inverse at a fixed index.

If `B` and `C` both satisfy the Drazin equations for `A` with the same
index `k`, then they are equal.
-/
theorem Drazin_unique {A B C : R} {k : ℕ}
    (hB : IsDrazinInverse A B k)
    (hC : IsDrazinInverse A C k) :
    B = C := by
  rcases k with _ | n
  · have hAB : A * B = 1 := by
      simpa using hB.pow_eq_pow_succ_mul.symm
    have hAC : A * C = 1 := by
      simpa using hC.pow_eq_pow_succ_mul.symm
    have hBA : B * A = 1 := by
      calc
        B * A = A * B := hB.comm.symm
        _ = 1 := hAB
    calc
      B = B * 1 := by simp
      _ = B * (A * C) := by rw [hAC]
      _ = (B * A) * C := by simp [mul_assoc]
      _ = 1 * C := by rw [hBA]
      _ = C := by simp
  ·
    let E : R := A * B
    let F : R := A * C

    have hEpow : B ^ (n + 1) * A ^ (n + 1) = E := by
      simpa [E] using mul_pow_eq_drazinProjector_of_pos (h := hB)

    have hFpow : C ^ (n + 1) * A ^ (n + 1) = F := by
      simpa [F] using mul_pow_eq_drazinProjector_of_pos (h := hC)

    have hcommAB : Commute A B := hB.comm
    have hcommAC : Commute A C := hC.comm

    have hE_mul_F : E = F * E := by
      have hABpow : A ^ (n + 1) * B ^ (n + 1) = B ^ (n + 1) * A ^ (n + 1) := by
        simpa using (hcommAB.pow_pow (n + 1) (n + 1)).eq
      have hA_pow_eq_F_mul : A ^ (n + 1) = F * A ^ (n + 1) := by
        calc
          A ^ (n + 1) = A ^ (n + 2) * C := hC.pow_eq_pow_succ_mul
          _ = C * A ^ (n + 2) := by
            simpa using (hcommAC.pow_left (n + 2)).eq
          _ = (A * C) * A ^ (n + 1) := by
            calc
              C * A ^ (n + 2) = C * (A * A ^ (n + 1)) := by
                simp [pow_succ']
              _ = (C * A) * A ^ (n + 1) := by
                simp [mul_assoc]
              _ = (A * C) * A ^ (n + 1) := by
                rw [hcommAC.eq]
          _ = F * A ^ (n + 1) := by rfl
      have hMulByBpow :
          A ^ (n + 1) * B ^ (n + 1) = (F * A ^ (n + 1)) * B ^ (n + 1) := by
        simpa [mul_assoc] using congrArg (fun t => t * B ^ (n + 1)) hA_pow_eq_F_mul
      calc
        E = B ^ (n + 1) * A ^ (n + 1) := hEpow.symm
        _ = A ^ (n + 1) * B ^ (n + 1) := by rw [← hABpow]
        _ = (F * A ^ (n + 1)) * B ^ (n + 1) := hMulByBpow
        _ = F * (A ^ (n + 1) * B ^ (n + 1)) := by simp [mul_assoc]
        _ = F * (B ^ (n + 1) * A ^ (n + 1)) := by rw [hABpow]
        _ = F * E := by rw [hEpow]

    have hF_mul_E : F = F * E := by
      calc
        F = C ^ (n + 1) * A ^ (n + 1) := hFpow.symm
        _ = C ^ (n + 1) * (A ^ (n + 2) * B) := by
          rw [hB.pow_eq_pow_succ_mul]
        _ = (C ^ (n + 1) * A ^ (n + 1)) * (A * B) := by
          simp [pow_succ, mul_assoc]
        _ = F * E := by simp [hFpow, E, F]

    have hEF : E = F := by
      exact hE_mul_F.trans hF_mul_E.symm

    have hAB : A * B = A * C := by
      simpa [E, F] using hEF

    have hBA : B * A = C * A := by
      calc
        B * A = A * B := hB.comm.symm
        _ = A * C := hAB
        _ = C * A := hC.comm

    calc
      B = B * A * B := hB.dad_eq_d.symm
      _ = (B * A) * B := by simp [mul_assoc]
      _ = (C * A) * B := by rw [hBA]
      _ = C * (A * B) := by simp [mul_assoc]
      _ = C * (A * C) := by rw [hAB]
      _ = C * A * C := by simp [mul_assoc]
      _ = C := hC.dad_eq_d

/--
Index-independent uniqueness of Drazin witnesses.

If two witnesses satisfy the Drazin laws for possibly different indices,
they still coincide.
-/
theorem Drazin_unique_of_indices {A B C : R} {k ℓ : ℕ}
    (hB : IsDrazinInverse A B k)
    (hC : IsDrazinInverse A C ℓ) :
    B = C := by
  let m := max k ℓ
  have hBm : IsDrazinInverse A B m :=
    IsDrazinInverse.lift hB (Nat.le_max_left _ _)
  have hCm : IsDrazinInverse A C m :=
    IsDrazinInverse.lift hC (Nat.le_max_right _ _)
  exact Drazin_unique hBm hCm

section StarSelf

variable [StarRing R]

/-- A Drazin inverse of a self-adjoint element is self-adjoint. -/
theorem Drazin_star_eq_self_of_selfAdjoint {A D : R} {k : ℕ}
    (h : IsDrazinInverse A D k)
    (hA : A† = A) :
    D† = D := by
  have hstar : IsDrazinInverse A D† k := by
    simpa [hA] using h.star_isDrazinInverse
  exact Drazin_unique hstar h

end StarSelf

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

/-- Any witness at the chosen Drazin index equals the chosen Drazin inverse. -/
theorem drazinInverse_eq_of_spec
    (A : Module.End K V) {D : Module.End K V}
    (hD : IsDrazinInverse A D (drazinIndex A)) :
    D = drazinInverse A := by
  exact Drazin_unique hD (drazinInverse_spec A)

/-- Any Drazin witness at any index coincides with the chosen inverse. -/
theorem drazinInverse_eq_of_spec_any_index
    (A : Module.End K V) {D : Module.End K V} {k : ℕ}
    (hD : IsDrazinInverse A D k) :
    D = drazinInverse A := by
  exact Drazin_unique_of_indices hD (drazinInverse_spec A)

/-- The chosen Drazin inverse is the unique witness at the chosen index. -/
theorem drazinInverse_unique
    (A : Module.End K V) {D : Module.End K V} :
    IsDrazinInverse A D (drazinIndex A) ↔ D = drazinInverse A := by
  constructor
  · intro hD
    exact drazinInverse_eq_of_spec A hD
  · intro hD
    rw [hD]
    exact drazinInverse_spec A

/-- Existence of any Drazin witness is equivalent to equality with the chosen inverse. -/
theorem drazinInverse_unique_any_index
    (A : Module.End K V) {D : Module.End K V} :
    (∃ k : ℕ, IsDrazinInverse A D k) ↔ D = drazinInverse A := by
  constructor
  · rintro ⟨k, hD⟩
    exact drazinInverse_eq_of_spec_any_index A hD
  · intro hD
    refine ⟨drazinIndex A, ?_⟩
    rw [hD]
    exact drazinInverse_spec A

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

