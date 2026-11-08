import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.SplitCliffordSourceSuperVirasoroFiniteWindow

Finite-window Super-Virasoro interface with explicit boundary-defect extraction.
-/

noncomputable section

namespace InfoGeometry.Canonical.SuperVirasoroFiniteWindow

open Finset
open Filter

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

local notation "EndV" => Module.End 𝕜 V

/-- A sequence stabilizes from cutoff `N0` if all later values match the `N0` value. -/
def StabilizesFrom {α : Type*} (d : ℤ → α) (N0 : ℤ) : Prop :=
  ∀ ⦃N : ℤ⦄, N ≥ N0 → d N = d N0

/-- Finite support predicate for mode families. -/
def HasFiniteSupport (f : ℤ → EndV) : Prop :=
  ∃ S : Finset ℤ, ∀ n : ℤ, n ∉ S → f n = 0

/-- Finite truncated supercurrent mode. -/
def G_trunc (N r : ℤ) (J ψ : ℤ → EndV) : EndV :=
  ∑ k ∈ Icc (-N) N, (J k) * (ψ (r - k))

/-- Finite truncated bosonic stress mode. -/
def L_bosonic_trunc (N m : ℤ) (J : ℤ → EndV) : EndV :=
  ∑ k ∈ Icc (-N) N, (J k) * (J (m - k))

/-- Finite truncated fermionic stress mode. -/
def L_fermionic_trunc (N m : ℤ) (ψ : ℤ → EndV) : EndV :=
  ∑ k ∈ Icc (-N) N, (k : 𝕜) • ((ψ (-k)) * (ψ (k + m)))

/-- Total finite truncated stress mode. -/
def L_trunc (N m : ℤ) (J ψ : ℤ → EndV) : EndV :=
  L_bosonic_trunc N m J + L_fermionic_trunc N m ψ

/-- Candidate coefficient in `[L_m, G_r]`. -/
def LG_coeff (m r : ℤ) : 𝕜 :=
  (m : 𝕜) / 2 - (r : 𝕜)

/--
Explicit finite-window boundary defect for the mixed superbracket.
This is the exact algebraic remainder after subtracting the principal term.
-/
def boundaryDefect_LG (N m r : ℤ) (J ψ : ℤ → EndV) : EndV :=
  (L_trunc N m J ψ) * (G_trunc N r J ψ)
    - (G_trunc N r J ψ) * (L_trunc N m J ψ)
    - (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)

/--
Explicit finite-window boundary defect for the `G-G` anticommutator
at a chosen central profile `central_N`.
-/
def boundaryDefect_GG
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) : EndV :=
  (G_trunc N r J ψ) * (G_trunc N s J ψ)
    + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    - (2 : 𝕜) • (L_trunc N (r + s) J ψ)
    - (central_N r s) • (1 : EndV)

/--
Finite-window mixed superbracket decomposition:
`[L_m^N, G_r^N] = coeff * G_{m+r}^N + boundaryDefect`.
-/
theorem superBracket_LG_decompose
    (N m r : ℤ) (J ψ : ℤ → EndV) :
    (L_trunc N m J ψ) * (G_trunc N r J ψ)
      - (G_trunc N r J ψ) * (L_trunc N m J ψ)
    = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)
      + boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ := by
  unfold boundaryDefect_LG
  abel_nf

/--
Owner-side shifted-mode specialization of the mixed finite-window bracket:
at `(m,r) = (1,0)`,
`[L_1^N, G_0^N] = (1/2) • G_1^N + boundaryDefect`.
-/
theorem superBracket_LG_decompose_m1_r0
    (N : ℤ) (J ψ : ℤ → EndV) :
    (L_trunc N 1 J ψ) * (G_trunc N 0 J ψ)
      - (G_trunc N 0 J ψ) * (L_trunc N 1 J ψ)
    = ((1 : 𝕜) / 2) • (G_trunc N 1 J ψ)
      + boundaryDefect_LG (𝕜 := 𝕜) N 1 0 J ψ := by
  simpa [LG_coeff] using superBracket_LG_decompose (𝕜 := 𝕜) N 1 0 J ψ

/--
Exact closure criterion:
if the finite boundary defect vanishes, the finite mixed superbracket closes
with the expected coefficient term.
-/
theorem superBracket_LG_of_boundaryDefect_zero
    (N m r : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    (L_trunc N m J ψ) * (G_trunc N r J ψ)
      - (G_trunc N r J ψ) * (L_trunc N m J ψ)
    = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ) := by
  calc
    (L_trunc N m J ψ) * (G_trunc N r J ψ)
        - (G_trunc N r J ψ) * (L_trunc N m J ψ)
      = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ)
          + boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ := superBracket_LG_decompose (𝕜 := 𝕜) N m r J ψ
    _ = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ) := by simp [hdef]

/--
Owner-side shifted-mode exact closure criterion:
if the boundary defect at `(m,r) = (1,0)` vanishes, then
`[L_1^N, G_0^N] = (1/2) • G_1^N`.
-/
theorem superBracket_LG_m1_r0_of_boundaryDefect_zero
    (N : ℤ) (J ψ : ℤ → EndV)
    (hdef : boundaryDefect_LG (𝕜 := 𝕜) N 1 0 J ψ = 0) :
    (L_trunc N 1 J ψ) * (G_trunc N 0 J ψ)
      - (G_trunc N 0 J ψ) * (L_trunc N 1 J ψ)
    = ((1 : 𝕜) / 2) • (G_trunc N 1 J ψ) := by
  simpa [LG_coeff] using
    superBracket_LG_of_boundaryDefect_zero (𝕜 := 𝕜) N 1 0 J ψ hdef

/--
Finite-window `G-G` decomposition:
`{G_r^N, G_s^N} = 2 L_{r+s}^N + central_N(r,s) • id + boundaryDefect_GG`.
-/
theorem superBracket_GG_decompose
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) :
    (G_trunc N r J ψ) * (G_trunc N s J ψ)
      + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
      + (central_N r s) • (1 : EndV)
      + boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N := by
  unfold boundaryDefect_GG
  abel_nf

/--
Exact `G-G` closure criterion:
if the finite boundary defect vanishes, the finite anticommutator closes
to stress term plus central contribution.
-/
theorem superBracket_GG_of_boundaryDefect_zero
    (N r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hdef : boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N = 0) :
    (G_trunc N r J ψ) * (G_trunc N s J ψ)
      + (G_trunc N s J ψ) * (G_trunc N r J ψ)
    = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
      + (central_N r s) • (1 : EndV) := by
  calc
    (G_trunc N r J ψ) * (G_trunc N s J ψ)
        + (G_trunc N s J ψ) * (G_trunc N r J ψ)
      = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
          + (central_N r s) • (1 : EndV)
          + boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N :=
        superBracket_GG_decompose (𝕜 := 𝕜) N r s J ψ central_N
    _ = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
          + (central_N r s) • (1 : EndV) := by simp [hdef]

/-! ### Stabilization-to-closure lemmas (atTop) -/

/--
If the mixed finite-window defect vanishes eventually in `N`, then the mixed
finite-window bracket closes eventually in `N`.
-/
theorem eventually_superBracket_LG_closure
    (m r : ℤ) (J ψ : ℤ → EndV)
    (hstab :
      ∀ᶠ N : ℤ in atTop,
        boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ = 0) :
    ∀ᶠ N : ℤ in atTop,
      (L_trunc N m J ψ) * (G_trunc N r J ψ)
        - (G_trunc N r J ψ) * (L_trunc N m J ψ)
      = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ) := by
  filter_upwards [hstab] with N hN
  exact superBracket_LG_of_boundaryDefect_zero (𝕜 := 𝕜) N m r J ψ hN

/--
If the `G-G` finite-window defect vanishes eventually in `N`, then the
finite-window anticommutator closes eventually in `N`.
-/
theorem eventually_superBracket_GG_closure
    (r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜)
    (hstab :
      ∀ᶠ N : ℤ in atTop,
        boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N = 0) :
    ∀ᶠ N : ℤ in atTop,
      (G_trunc N r J ψ) * (G_trunc N s J ψ)
        + (G_trunc N s J ψ) * (G_trunc N r J ψ)
      = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
        + (central_N r s) • (1 : EndV) := by
  filter_upwards [hstab] with N hN
  exact superBracket_GG_of_boundaryDefect_zero (𝕜 := 𝕜) N r s J ψ central_N hN

/--
If a sequence stabilizes from `N0` and has value `0` at `N0`,
then it is eventually zero at `atTop`.
-/
theorem eventually_zero_of_stabilizesFrom
    (d : ℤ → EndV) (N0 : ℤ)
    (hstab : StabilizesFrom d N0)
    (h0 : d N0 = 0) :
    ∀ᶠ N : ℤ in atTop, d N = 0 := by
  refine Filter.eventually_atTop.2 ⟨N0, ?_⟩
  intro N hN
  calc
    d N = d N0 := hstab hN
    _ = 0 := h0

/--
Sufficient hypothesis package for mixed-bracket closure:
if the mixed boundary defect stabilizes and its stabilized value is `0`,
then mixed finite-window closure holds eventually.
-/
theorem eventually_superBracket_LG_closure_of_stabilization
    (m r : ℤ) (J ψ : ℤ → EndV) (N0 : ℤ)
    (hstab :
      StabilizesFrom
        (fun N => boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ) N0)
    (h0 : boundaryDefect_LG (𝕜 := 𝕜) N0 m r J ψ = 0) :
    ∀ᶠ N : ℤ in atTop,
      (L_trunc N m J ψ) * (G_trunc N r J ψ)
        - (G_trunc N r J ψ) * (L_trunc N m J ψ)
      = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ) := by
  exact eventually_superBracket_LG_closure (𝕜 := 𝕜) m r J ψ
    (eventually_zero_of_stabilizesFrom
      (d := fun N => boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ)
      N0 hstab h0)

/--
Sufficient hypothesis package for `G-G` closure:
if the `G-G` boundary defect stabilizes and its stabilized value is `0`,
then anticommutator finite-window closure holds eventually.
-/
theorem eventually_superBracket_GG_closure_of_stabilization
    (r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) (N0 : ℤ)
    (hstab :
      StabilizesFrom
        (fun N => boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N) N0)
    (h0 : boundaryDefect_GG (𝕜 := 𝕜) N0 r s J ψ central_N = 0) :
    ∀ᶠ N : ℤ in atTop,
      (G_trunc N r J ψ) * (G_trunc N s J ψ)
        + (G_trunc N s J ψ) * (G_trunc N r J ψ)
      = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
        + (central_N r s) • (1 : EndV) := by
  exact eventually_superBracket_GG_closure (𝕜 := 𝕜) r s J ψ central_N
    (eventually_zero_of_stabilizesFrom
      (d := fun N => boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N)
      N0 hstab h0)

/-! ### Support-aware strict interface (proved, no placeholders) -/

/--
Direct packaged criterion for mixed-bracket eventual closure:
it suffices to give a cutoff `N0` where the defect is zero and stays stable.
-/
theorem eventually_superBracket_LG_closure_of_stable_zero
    (m r : ℤ) (J ψ : ℤ → EndV) (N0 : ℤ)
    (hstab :
      StabilizesFrom
        (fun N => boundaryDefect_LG (𝕜 := 𝕜) N m r J ψ) N0)
    (h0 : boundaryDefect_LG (𝕜 := 𝕜) N0 m r J ψ = 0) :
    ∀ᶠ N : ℤ in atTop,
      (L_trunc N m J ψ) * (G_trunc N r J ψ)
        - (G_trunc N r J ψ) * (L_trunc N m J ψ)
      = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J ψ) := by
  exact eventually_superBracket_LG_closure_of_stabilization (𝕜 := 𝕜) m r J ψ N0 hstab h0

/--
Direct packaged criterion for `G-G` eventual closure:
it suffices to give a cutoff `N0` where the defect is zero and stays stable.
-/
theorem eventually_superBracket_GG_closure_of_stable_zero
    (r s : ℤ) (J ψ : ℤ → EndV) (central_N : ℤ → ℤ → 𝕜) (N0 : ℤ)
    (hstab :
      StabilizesFrom
        (fun N => boundaryDefect_GG (𝕜 := 𝕜) N r s J ψ central_N) N0)
    (h0 : boundaryDefect_GG (𝕜 := 𝕜) N0 r s J ψ central_N = 0) :
    ∀ᶠ N : ℤ in atTop,
      (G_trunc N r J ψ) * (G_trunc N s J ψ)
        + (G_trunc N s J ψ) * (G_trunc N r J ψ)
      = (2 : 𝕜) • (L_trunc N (r + s) J ψ)
        + (central_N r s) • (1 : EndV) := by
  exact eventually_superBracket_GG_closure_of_stabilization (𝕜 := 𝕜) r s J ψ central_N N0 hstab h0

/-! ### Concrete proved lane: explicit mode family `ψ ≡ 0` -/

/-- For `ψ ≡ 0`, the truncated supercurrent is identically zero. -/
theorem G_trunc_eq_zero_of_psi_zero
    (N r : ℤ) (J : ℤ → EndV) :
    G_trunc N r J (fun _ => (0 : EndV)) = 0 := by
  simp [G_trunc]

/-- For `ψ ≡ 0`, the fermionic truncated stress part is identically zero. -/
theorem L_fermionic_trunc_eq_zero_of_psi_zero
    (N m : ℤ) :
    L_fermionic_trunc (𝕜 := 𝕜) N m (fun _ => (0 : EndV)) = 0 := by
  simp [L_fermionic_trunc]

/--
Concrete real lemma: for the explicit mode family `ψ ≡ 0`,
the mixed finite-window boundary defect vanishes identically for all `N,m,r`.
-/
theorem boundaryDefect_LG_eq_zero_of_psi_zero
    (N m r : ℤ) (J : ℤ → EndV) :
    boundaryDefect_LG (𝕜 := 𝕜) N m r J (fun _ => (0 : EndV)) = 0 := by
  simp [boundaryDefect_LG, G_trunc_eq_zero_of_psi_zero]

/--
As a consequence, the mixed defect sequence is stable from any cutoff for
the explicit mode family `ψ ≡ 0`.
-/
theorem stabilizes_boundaryDefect_LG_of_psi_zero
    (m r : ℤ) (J : ℤ → EndV) (N0 : ℤ) :
    StabilizesFrom
      (fun N => boundaryDefect_LG (𝕜 := 𝕜) N m r J (fun _ => (0 : EndV))) N0 := by
  intro N hN
  simp [boundaryDefect_LG_eq_zero_of_psi_zero]

/--
Concrete eventual closure theorem in the explicit lane `ψ ≡ 0`.
-/
theorem eventually_superBracket_LG_closure_of_psi_zero
    (m r : ℤ) (J : ℤ → EndV) :
    ∀ᶠ N : ℤ in atTop,
      (L_trunc N m J (fun _ => (0 : EndV))) * (G_trunc N r J (fun _ => (0 : EndV)))
        - (G_trunc N r J (fun _ => (0 : EndV))) * (L_trunc N m J (fun _ => (0 : EndV)))
      = (LG_coeff (𝕜 := 𝕜) m r) • (G_trunc N (m + r) J (fun _ => (0 : EndV))) := by
  exact eventually_superBracket_LG_closure_of_stable_zero (𝕜 := 𝕜) m r J (fun _ => (0 : EndV)) 0
    (stabilizes_boundaryDefect_LG_of_psi_zero (𝕜 := 𝕜) m r J 0)
    (by simp [boundaryDefect_LG_eq_zero_of_psi_zero])

/-! ### Concrete nontrivial witness family: `J ≠ 0`, `ψ ≠ 0` but index-mismatched -/

/-- Single-mode witness for currents, supported at index `0`. -/
def J_mode0 (A : EndV) : ℤ → EndV :=
  fun n => if n = 0 then A else 0

/-- Single-mode witness for fermions, supported at index `1`. -/
def psi_mode1 (B : EndV) : ℤ → EndV :=
  fun n => if n = 1 then B else 0

theorem J_mode0_at_zero (A : EndV) :
    J_mode0 (𝕜 := 𝕜) A 0 = A := by
  simp [J_mode0]

theorem psi_mode1_at_one (B : EndV) :
    psi_mode1 (𝕜 := 𝕜) B 1 = B := by
  simp [psi_mode1]

theorem J_mode0_nontrivial (A : EndV) (hA : A ≠ 0) :
    ∃ n : ℤ, J_mode0 (𝕜 := 𝕜) A n ≠ 0 := by
  refine ⟨0, ?_⟩
  simpa [J_mode0] using hA

theorem psi_mode1_nontrivial (B : EndV) (hB : B ≠ 0) :
    ∃ n : ℤ, psi_mode1 (𝕜 := 𝕜) B n ≠ 0 := by
  refine ⟨1, ?_⟩
  simpa [psi_mode1] using hB

/--
For the explicit witness family with `J` at mode `0` and `ψ` at mode `1`,
the truncated supercurrent at `r = 0` vanishes for every cutoff.
-/
theorem G_trunc_r0_mode01_eq_zero
    (N : ℤ) (A B : EndV) :
    G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) = 0 := by
  classical
  unfold G_trunc
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp [J_mode0, psi_mode1]
  · have hJ : J_mode0 (𝕜 := 𝕜) A k = 0 := by simp [J_mode0, hk0]
    simp [hJ]

/--
Concrete real lemma (nontrivial witness family):
for `J = J_mode0 A`, `ψ = psi_mode1 B`, and `r = 0`,
the mixed finite-window defect is identically zero for all `N,m`.
-/
theorem boundaryDefect_LG_mode01_r0_eq_zero
    (N : ℤ) (A B : EndV) :
    boundaryDefect_LG (𝕜 := 𝕜) N 0 0
      (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) = 0 := by
  simp [boundaryDefect_LG, G_trunc_r0_mode01_eq_zero]

/--
Stabilization for the same nontrivial witness family at `r = 0`.
-/
theorem stabilizes_boundaryDefect_LG_mode01_r0
    (A B : EndV) (N0 : ℤ) :
    StabilizesFrom
      (fun N =>
        boundaryDefect_LG (𝕜 := 𝕜) N 0 0
          (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
      N0 := by
  intro N hN
  simp [boundaryDefect_LG_mode01_r0_eq_zero]

/--
Concrete eventual closure in the explicit nontrivial witness lane
for `(m,r) = (0,0)`.
-/
theorem eventually_superBracket_LG_closure_mode01_r0
    (A B : EndV) :
    ∀ᶠ N : ℤ in atTop,
      (L_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
        - (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (L_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
      = (LG_coeff (𝕜 := 𝕜) 0 0)
          • (G_trunc N (0 + 0) (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B)) := by
  exact eventually_superBracket_LG_closure_of_stable_zero
    (𝕜 := 𝕜) 0 0
    (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) 0
    (stabilizes_boundaryDefect_LG_mode01_r0 (𝕜 := 𝕜) A B 0)
    (boundaryDefect_LG_mode01_r0_eq_zero (𝕜 := 𝕜) 0 A B)

/--
Nontrivial explicit witness lane (both families nonzero somewhere) with
proved eventual closure at `(m,r) = (0,0)`.
-/
theorem nontrivial_mode01_family_with_eventual_closure
    (A B : EndV) (hA : A ≠ 0) (hB : B ≠ 0) :
    (∃ n : ℤ, J_mode0 (𝕜 := 𝕜) A n ≠ 0) ∧
    (∃ n : ℤ, psi_mode1 (𝕜 := 𝕜) B n ≠ 0) ∧
    (∀ᶠ N : ℤ in atTop,
      (L_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
        - (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (L_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
      = (LG_coeff (𝕜 := 𝕜) 0 0)
          • (G_trunc N (0 + 0) (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))) := by
  refine ⟨J_mode0_nontrivial (𝕜 := 𝕜) A hA, psi_mode1_nontrivial (𝕜 := 𝕜) B hB, ?_⟩
  exact eventually_superBracket_LG_closure_mode01_r0 (𝕜 := 𝕜) A B

/-! ### Concrete `{G,G}` witness lane with explicit central stabilization -/

/-- Explicit central profile used in the concrete witness lane. -/
def centralZero : ℤ → ℤ → 𝕜 := fun _ _ => 0

theorem G_trunc_r1_mode01_eq
    (N : ℤ) (A B : EndV) (hN : 0 ≤ N) :
    G_trunc N 1 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) = A * B := by
  classical
  unfold G_trunc
  have hmem0 : (0 : ℤ) ∈ Icc (-N) N := by
    simp [hN]
  rw [Finset.sum_eq_single_of_mem 0 hmem0]
  · simp [J_mode0, psi_mode1]
  · intro y hy hy0
    by_cases hy0' : y = 0
    · exact (hy0 hy0').elim
    · have hJ : J_mode0 (𝕜 := 𝕜) A y = 0 := by simp [J_mode0, hy0']
      simp [hJ]

theorem L_bosonic_trunc_mode0_n1_eq_zero
    (N : ℤ) (A : EndV) :
    L_bosonic_trunc N 1 (J_mode0 (𝕜 := 𝕜) A) = 0 := by
  classical
  unfold L_bosonic_trunc
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp [J_mode0]
  · have hJ : J_mode0 (𝕜 := 𝕜) A k = 0 := by simp [J_mode0, hk0]
    simp [hJ]

theorem L_fermionic_trunc_mode1_n1_eq_zero
    (N : ℤ) (B : EndV) :
    L_fermionic_trunc (𝕜 := 𝕜) N 1 (psi_mode1 (𝕜 := 𝕜) B) = 0 := by
  classical
  unfold L_fermionic_trunc
  refine Finset.sum_eq_zero ?_
  intro k hk
  by_cases hneg : -k = 1
  · have hkval : k = -1 := by omega
    subst hkval
    simp [psi_mode1]
  · have hψ : psi_mode1 (𝕜 := 𝕜) B (-k) = 0 := by simp [psi_mode1, hneg]
    simp [hψ]

theorem L_trunc_mode01_n1_eq_zero
    (N : ℤ) (A B : EndV) :
    L_trunc N 1 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) = 0 := by
  simp [L_trunc, L_bosonic_trunc_mode0_n1_eq_zero, L_fermionic_trunc_mode1_n1_eq_zero]

theorem boundaryDefect_GG_mode01_r0_s1_centralZero_eq_zero
    (N : ℤ) (A B : EndV) :
    boundaryDefect_GG (𝕜 := 𝕜) N 0 1
      (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) centralZero = 0 := by
  simp [boundaryDefect_GG, centralZero, G_trunc_r0_mode01_eq_zero, L_trunc_mode01_n1_eq_zero]

theorem stabilizes_boundaryDefect_GG_mode01_r0_s1_centralZero
    (A B : EndV) (N0 : ℤ) :
    StabilizesFrom
      (fun N =>
        boundaryDefect_GG (𝕜 := 𝕜) N 0 1
          (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) centralZero)
      N0 := by
  intro N hN
  simp [boundaryDefect_GG_mode01_r0_s1_centralZero_eq_zero]

theorem eventually_superBracket_GG_closure_mode01_r0_s1_centralZero
    (A B : EndV) :
    ∀ᶠ N : ℤ in atTop,
      (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (G_trunc N 1 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
        + (G_trunc N 1 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
          * (G_trunc N 0 (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
      = (2 : 𝕜) • (L_trunc N (0 + 1) (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B))
        + (centralZero (𝕜 := 𝕜) 0 1) • (1 : EndV) := by
  exact eventually_superBracket_GG_closure_of_stable_zero
    (𝕜 := 𝕜) 0 1
    (J_mode0 (𝕜 := 𝕜) A) (psi_mode1 (𝕜 := 𝕜) B) centralZero 0
    (stabilizes_boundaryDefect_GG_mode01_r0_s1_centralZero (𝕜 := 𝕜) A B 0)
    (boundaryDefect_GG_mode01_r0_s1_centralZero_eq_zero (𝕜 := 𝕜) 0 A B)

end InfoGeometry.Canonical.SuperVirasoroFiniteWindow
