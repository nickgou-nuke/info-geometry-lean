import Mathlib

/-!
# N-Potent Zero-Mode Projector Bridge

Formalizes the canonical polynomial zero-mode projector for general $N$-potent operators:
$$T^N = T \quad (N \ge 2) \implies P_0^{(N)} := I - T^{N-1}$$

## Core Theorems:
1. `nPotentZeroProjector_mul_self`: Idempotence: $(I - T^{N-1})^2 = I - T^{N-1}$.
2. `mul_nPotentZeroProjector`: Annihilation: $T \cdot (I - T^{N-1}) = 0$.
3. `nPotentZeroProjector_mul`: Annihilation: $(I - T^{N-1}) \cdot T = 0$.
4. `range_nPotentZeroProjector_eq_ker`: Kernel Identification: $\operatorname{im}(I - T^{N-1}) = \ker T$.
5. `tripotent_zero_projector`: Specialization $N=3$: $P_0^{(3)} = I - T^2$, $\operatorname{im}(I - T^2) = \ker T$.
6. `fibonacci_sixPotent_zero_projector`: Specialization $N=6$: $P_0^{(6)} = I - T^5$, $\operatorname{im}(I - T^5) = \ker T$.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra.NPotentZeroModeProjectorBridge

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

/-- Canonical degree-(N-1) zero-mode projector: P₀^{(N)} = I - T^{N-1}. -/
def nPotentZeroProjector (N : ℕ) (T : Module.End R V) : Module.End R V :=
  1 - T ^ (N - 1)

/-- Complementary nonzero-mode projector `P₁⁽ᴺ⁾ = T^(N-1)`. -/
def nPotentNonzeroProjector (N : ℕ) (T : Module.End R V) : Module.End R V :=
  T ^ (N - 1)

/-- An endomorphism T is N-potent if T^N = T. -/
def IsNPotent (N : ℕ) (T : Module.End R V) : Prop :=
  T ^ N = T

/-- Power reduction identity for N-potent operators: T^{2N-2} = T^{N-1}. -/
theorem nPotent_pow_two_sub_two {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} (hT : IsNPotent N T) :
    T ^ (2 * N - 2) = T ^ (N - 1) := by
  have hN1 : N - 1 = (N - 2) + 1 := by omega
  have h2N2 : 2 * N - 2 = N + (N - 2) := by omega
  have h_split : T ^ (2 * N - 2) = T ^ N * T ^ (N - 2) := by
    rw [h2N2, pow_add]
  have hT_unfold : T ^ N = T := hT
  have h_comb : T * T ^ (N - 2) = T ^ (N - 1) := by
    rw [hN1, pow_succ']
  rw [h_split, hT_unfold, h_comb]

/-- 🏆 THEOREM: The degree-(N-1) zero-mode projector is idempotent: (I - T^{N-1})² = I - T^{N-1}. -/
theorem nPotentZeroProjector_mul_self {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentZeroProjector N T * nPotentZeroProjector N T =
      nPotentZeroProjector N T := by
  dsimp [nPotentZeroProjector]
  have h2 : T ^ (N - 1) * T ^ (N - 1) = T ^ (2 * N - 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc (1 - T ^ (N - 1)) * (1 - T ^ (N - 1))
    _ = 1 - 2 • T ^ (N - 1) + T ^ (N - 1) * T ^ (N - 1) := by noncomm_ring
    _ = 1 - 2 • T ^ (N - 1) + T ^ (2 * N - 2) := by rw [h2]
    _ = 1 - 2 • T ^ (N - 1) + T ^ (N - 1) := by rw [nPotent_pow_two_sub_two hN hT]
    _ = 1 - T ^ (N - 1) := by
      ext x
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
      module

/-! The complementary projector is algebraic: no spectral or topological
assumption is needed. -/

theorem nPotentNonzeroProjector_mul_self {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentNonzeroProjector N T * nPotentNonzeroProjector N T =
      nPotentNonzeroProjector N T := by
  dsimp [nPotentNonzeroProjector]
  calc
    T ^ (N - 1) * T ^ (N - 1) = T ^ ((N - 1) + (N - 1)) := by
      rw [pow_add]
    _ = T ^ (2 * N - 2) := by congr 1; omega
    _ = T ^ (N - 1) := nPotent_pow_two_sub_two hN hT

theorem nPotentZeroProjector_add_nonzeroProjector {N : ℕ}
    (T : Module.End R V) :
    nPotentZeroProjector N T + nPotentNonzeroProjector N T =
      (1 : Module.End R V) := by
  dsimp [nPotentZeroProjector, nPotentNonzeroProjector]
  module

/-- 🏆 THEOREM: Left multiplication by T annihilates the zero-mode projector: T · (I - T^{N-1}) = 0. -/
theorem mul_nPotentZeroProjector {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} (hT : IsNPotent N T) :
    T * nPotentZeroProjector N T = 0 := by
  dsimp [nPotentZeroProjector]
  have hN1 : (N - 1) + 1 = N := by omega
  calc T * (1 - T ^ (N - 1))
    _ = T - T * T ^ (N - 1) := by noncomm_ring
    _ = T - T ^ ((N - 1) + 1) := by rw [pow_succ']
    _ = T - T ^ N := by rw [hN1]
    _ = T - T := by rw [hT]
    _ = 0 := by rw [sub_self]

/-! The complementary range is the algebraic nonzero-mode carrier.  On this
carrier the degree-(N-1) power of `T` is already the identity.  This is the
operator-level statement behind the later cyclotomic root classification; it
does not assert a chosen eigenspace decomposition. -/

theorem nPotent_pow_sub_one_apply_of_mem_nonzero_range {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) {x : V}
    (hx : x ∈ LinearMap.range (nPotentNonzeroProjector N T)) :
    (T ^ (N - 1)) x = x := by
  rcases hx with ⟨y, rfl⟩
  have hproj := nPotentNonzeroProjector_mul_self hN hT
  have happ := congrArg (fun F : Module.End R V => F y) hproj
  simpa only [Module.End.mul_apply, nPotentNonzeroProjector] using happ

theorem mem_nonzero_range_iff_pow_sub_one_apply {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) {x : V} :
    x ∈ LinearMap.range (nPotentNonzeroProjector N T) ↔
      (T ^ (N - 1)) x = x := by
  constructor
  · exact nPotent_pow_sub_one_apply_of_mem_nonzero_range hN hT
  · intro hx
    refine ⟨x, ?_⟩
    simpa [nPotentNonzeroProjector] using hx

theorem nPotent_nonzero_range_disjoint_zero_range {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) :
    Disjoint (LinearMap.range (nPotentZeroProjector N T))
      (LinearMap.range (nPotentNonzeroProjector N T)) := by
  refine Submodule.disjoint_def.mpr ?_
  intro x hx0 hx1
  rcases hx0 with ⟨y, rfl⟩
  have hzero : T (nPotentZeroProjector N T y) = 0 := by
    rw [← Module.End.mul_apply, mul_nPotentZeroProjector hN hT]
    rfl
  have hnonzero := nPotent_pow_sub_one_apply_of_mem_nonzero_range hN hT hx1
  have hpow_zero : (T ^ (N - 1)) (nPotentZeroProjector N T y) = 0 := by
    have hN1 : N - 1 = (N - 2) + 1 := by omega
    rw [hN1, pow_succ, Module.End.mul_apply, hzero]
    simp
  rw [hpow_zero] at hnonzero
  exact hnonzero.symm

/-- The two complementary projector ranges span the whole carrier. -/
theorem sup_range_nPotentZeroProjector_nonzeroProjector_eq_top {N : ℕ}
    (T : Module.End R V) :
    LinearMap.range (nPotentZeroProjector N T) ⊔
        LinearMap.range (nPotentNonzeroProjector N T) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x hx
    have hdecomp :
        x = nPotentZeroProjector N T x + nPotentNonzeroProjector N T x := by
      have hsum := congrArg (fun F : Module.End R V => F x)
        (nPotentZeroProjector_add_nonzeroProjector (N := N) T)
      simpa using hsum.symm
    rw [hdecomp]
    exact Submodule.add_mem_sup
      ⟨x, rfl⟩
      ⟨x, rfl⟩

/-- 🏆 THEOREM: Right multiplication by T annihilates the zero-mode projector: (I - T^{N-1}) · T = 0. -/
theorem nPotentZeroProjector_mul {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentZeroProjector N T * T = 0 := by
  dsimp [nPotentZeroProjector]
  have hN1 : (N - 1) + 1 = N := by omega
  calc (1 - T ^ (N - 1)) * T
    _ = T - T ^ (N - 1) * T := by noncomm_ring
    _ = T - T ^ ((N - 1) + 1) := by rw [← pow_succ]
    _ = T - T ^ N := by rw [hN1]
    _ = T - T := by rw [hT]
    _ = 0 := by rw [sub_self]

/-! The two complementary projectors are mutually annihilating, so the
zero/nonzero split is an algebraic direct decomposition rather than merely a
range identity. -/

theorem nPotentZeroProjector_mul_nonzeroProjector {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentZeroProjector N T * nPotentNonzeroProjector N T = 0 := by
  dsimp [nPotentZeroProjector, nPotentNonzeroProjector]
  have hproj : T ^ (N - 1) * T ^ (N - 1) = T ^ (N - 1) := by
    calc
      T ^ (N - 1) * T ^ (N - 1) = T ^ (2 * N - 2) := by
        rw [← pow_add]
        congr 1
        omega
      _ = T ^ (N - 1) := nPotent_pow_two_sub_two hN hT
  calc
    (1 - T ^ (N - 1)) * T ^ (N - 1) =
        T ^ (N - 1) - T ^ (N - 1) * T ^ (N - 1) := by noncomm_ring
    _ = 0 := by rw [hproj, sub_self]

theorem nPotentNonzeroProjector_mul_zeroProjector {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentNonzeroProjector N T * nPotentZeroProjector N T = 0 := by
  dsimp [nPotentZeroProjector, nPotentNonzeroProjector]
  have hproj : T ^ (N - 1) * T ^ (N - 1) = T ^ (N - 1) := by
    calc
      T ^ (N - 1) * T ^ (N - 1) = T ^ (2 * N - 2) := by
        rw [← pow_add]
        congr 1
        omega
      _ = T ^ (N - 1) := nPotent_pow_two_sub_two hN hT
  calc
    T ^ (N - 1) * (1 - T ^ (N - 1)) =
        T ^ (N - 1) - T ^ (N - 1) * T ^ (N - 1) := by noncomm_ring
    _ = 0 := by rw [hproj, sub_self]

theorem nPotentZeroProjector_commutes {N : ℕ} (hN : 2 ≤ N)
    {T : Module.End R V} (hT : IsNPotent N T) :
    nPotentZeroProjector N T * T = T * nPotentZeroProjector N T := by
  rw [nPotentZeroProjector_mul hN hT, mul_nPotentZeroProjector hN hT]

/-- Elements in ker T are invariant under the zero-mode projector P₀^{(N)}. -/
theorem nPotentZeroProjector_apply_of_mem_ker {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} {x : V}
    (hx : x ∈ LinearMap.ker T) :
    nPotentZeroProjector N T x = x := by
  have hx_zero : T x = 0 := LinearMap.mem_ker.mp hx
  have h_pow_zero : (T ^ (N - 1)) x = 0 := by
    have hN1 : N - 1 = (N - 2) + 1 := by omega
    calc (T ^ (N - 1)) x
      _ = (T ^ (N - 2) * T) x := by rw [hN1, pow_succ]
      _ = (T ^ (N - 2)) (T x) := rfl
      _ = (T ^ (N - 2)) 0 := by rw [hx_zero]
      _ = 0 := LinearMap.map_zero _
  dsimp [nPotentZeroProjector]
  simp [h_pow_zero]

/-- 🏆 THEOREM: The image of the canonical zero-mode projector is exactly the kernel of T: im(I - T^{N-1}) = ker T. -/
theorem range_nPotentZeroProjector_eq_ker {N : ℕ} (hN : 2 ≤ N) {T : Module.End R V} (hT : IsNPotent N T) :
    LinearMap.range (nPotentZeroProjector N T) = LinearMap.ker T := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have h := mul_nPotentZeroProjector hN hT
    calc T (nPotentZeroProjector N T y)
      _ = (T * nPotentZeroProjector N T) y := rfl
      _ = (0 : Module.End R V) y := by rw [h]
      _ = 0 := rfl
  · intro hx
    refine ⟨x, ?_⟩
    exact nPotentZeroProjector_apply_of_mem_ker hN hx

/-! ### Commutant transport on the general `N`-potent zero-mode carrier -/

/-- A map commuting with `P₀⁽ᴺ⁾` preserves the `N`-potent zero-mode carrier. -/
theorem nPotent_endomorphism_preserves_zeroModeCarrier
    {N : ℕ} (hN : 2 ≤ N) (T A : Module.End R V) (hT : IsNPotent N T)
    (hA : A * nPotentZeroProjector N T = nPotentZeroProjector N T * A) :
    ∀ x, x ∈ LinearMap.ker T → A x ∈ LinearMap.ker T := by
  intro x hx
  have hxP : nPotentZeroProjector N T x = x :=
    nPotentZeroProjector_apply_of_mem_ker hN hx
  have hcomm : nPotentZeroProjector N T (A x) = A (nPotentZeroProjector N T x) := by
    have h := congrArg (fun F : Module.End R V => F x) hA
    simpa only [Module.End.mul_apply] using h.symm
  rw [LinearMap.mem_ker]
  have hzero : T * nPotentZeroProjector N T = 0 :=
    mul_nPotentZeroProjector hN hT
  calc
    T (A x) = T (nPotentZeroProjector N T (A x)) := by rw [hcomm, hxP]
    _ = (T * nPotentZeroProjector N T) (A x) := rfl
    _ = 0 := by rw [hzero]; simp

/-- Native restriction of a commuting endomorphism to the general `N`-potent carrier. -/
def nPotentZeroModeRestriction
    {N : ℕ} (hN : 2 ≤ N) (T A : Module.End R V) (hT : IsNPotent N T)
    (hA : A * nPotentZeroProjector N T = nPotentZeroProjector N T * A) :
    Module.End R (LinearMap.ker T) where
  toFun x :=
    ⟨A x.1, nPotent_endomorphism_preserves_zeroModeCarrier hN T A hT hA x.1 x.2⟩
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp

@[simp] theorem nPotentZeroModeRestriction_apply
    {N : ℕ} (hN : 2 ≤ N) (T A : Module.End R V) (hT : IsNPotent N T)
    (hA : A * nPotentZeroProjector N T = nPotentZeroProjector N T * A)
    (x : LinearMap.ker T) :
    (nPotentZeroModeRestriction hN T A hT hA x).1 = A x.1 := rfl

/-- Commutation with `P₀⁽ᴺ⁾` is closed under products. -/
theorem commute_nPotentZeroProjector_mul
    {N : ℕ} (T A B : Module.End R V)
    (hA : A * nPotentZeroProjector N T = nPotentZeroProjector N T * A)
    (hB : B * nPotentZeroProjector N T = nPotentZeroProjector N T * B) :
    (A * B) * nPotentZeroProjector N T =
      nPotentZeroProjector N T * (A * B) := by
  calc
    (A * B) * nPotentZeroProjector N T = A * (B * nPotentZeroProjector N T) := by
      simp [mul_assoc]
    _ = A * (nPotentZeroProjector N T * B) := by rw [hB]
    _ = (A * nPotentZeroProjector N T) * B := by simp [mul_assoc]
    _ = (nPotentZeroProjector N T * A) * B := by rw [hA]
    _ = nPotentZeroProjector N T * (A * B) := by simp [mul_assoc]

theorem nPotentZeroModeRestriction_mul
    {N : ℕ} (hN : 2 ≤ N) (T A B : Module.End R V) (hT : IsNPotent N T)
    (hA : A * nPotentZeroProjector N T = nPotentZeroProjector N T * A)
    (hB : B * nPotentZeroProjector N T = nPotentZeroProjector N T * B) :
    nPotentZeroModeRestriction hN T (A * B) hT
        (commute_nPotentZeroProjector_mul T A B hA hB) =
      nPotentZeroModeRestriction hN T A hT hA *
        nPotentZeroModeRestriction hN T B hT hB := by
  ext x
  rfl

section Specializations

variable {T : Module.End R V}

/-- 🏆 SPECIALIZATION N=3 (Tripotent): P₀^{(3)} = 1 - T² satisfies im(1 - T²) = ker T. -/
theorem tripotent_zero_projector (hT : IsNPotent 3 T) :
    LinearMap.range (1 - T ^ 2) = LinearMap.ker T := by
  have h := range_nPotentZeroProjector_eq_ker (N := 3) (by omega) hT
  have h_proj : nPotentZeroProjector 3 T = 1 - T ^ 2 := by
    dsimp [nPotentZeroProjector]
  rwa [h_proj] at h

/-- 🏆 SPECIALIZATION N=6 (Fibonacci 6-potent): P₀^{(6)} = 1 - T⁵ satisfies im(1 - T⁵) = ker T. -/
theorem fibonacci_sixPotent_zero_projector (hT : IsNPotent 6 T) :
    LinearMap.range (1 - T ^ 5) = LinearMap.ker T := by
  have h := range_nPotentZeroProjector_eq_ker (N := 6) (by omega) hT
  have h_proj : nPotentZeroProjector 6 T = 1 - T ^ 5 := by
    dsimp [nPotentZeroProjector]
  rwa [h_proj] at h

end Specializations

end InfoGeometry.Physics.Algebra.NPotentZeroModeProjectorBridge
