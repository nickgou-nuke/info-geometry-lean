/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum
import InfoGeometry.Physics.NuclearSymmetrySectors

/-!
# Nuclear Shell Model

This module formalizes the nuclear shell model:

1. **Shell orbitals**: Each orbital is labeled by `(n, l, j, m_j)` where:
   - `n` = principal quantum number
   - `l` = orbital angular momentum
   - `j = l ± 1/2` = total angular momentum
   - `m_j` = magnetic quantum number, `-j ≤ m_j ≤ j`

2. **Shell capacity**: A shell with angular momentum `j` can hold `2j + 1` nucleons.

3. **Seniority**: The number of unpaired nucleons in a shell. Pairing favors
   `seniority = 0` (all nucleons paired).

4. **Shell closures**: Magic numbers occur when shells are completely filled.

All statements are finite-dimensional and proven constructively in Lean 4 with
no `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearShellModel

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

-- -----------------------------------------------------------------------------
-- SECTION 1: Shell orbitals
-- -----------------------------------------------------------------------------

/-- A single-particle shell orbital labeled by `(n, l, j, m_j)`. -/
structure ShellOrbital where
  n : ℕ                      -- principal quantum number
  l : ℕ                      -- orbital angular momentum
  j : ℕ                      -- total angular momentum (2j stored as integer)
  m : ℤ                      -- magnetic quantum number (-j ≤ m ≤ j)

/-- Validity condition: `-j ≤ m ≤ j`. -/
def valid_orbital (o : ShellOrbital) : Prop :=
  (o.m : ℤ) ≥ -(o.j : ℤ) ∧ (o.m : ℤ) ≤ (o.j : ℤ)

/-- Shell capacity: a shell with angular momentum `j` can hold `2j + 1` nucleons. -/
def shell_capacity (j : ℕ) : ℕ := 2 * j + 1

/-- The degeneracy of shell `j` equals `2j + 1`. -/
theorem shell_capacity_pos (j : ℕ) : shell_capacity j > 0 := by
  exact Nat.zero_lt_succ (2 * j)

-- -----------------------------------------------------------------------------
-- SECTION 2: Seniority
-- -----------------------------------------------------------------------------

/-- Seniority `v` = number of unpaired nucleons in a shell. -/
def seniority (n_occ : ℕ) (cap : ℕ) : ℕ :=
  if n_occ ≤ cap / 2 then n_occ else cap - n_occ

/-- Seniority is bounded by the shell capacity. -/
theorem seniority_le_cap (n_occ : ℕ) (cap : ℕ) : seniority n_occ cap ≤ cap := by
  unfold seniority
  split_ifs with h
  · omega
  · exact Nat.sub_le cap n_occ

-- -----------------------------------------------------------------------------
-- SECTION 3: Shell closures (magic numbers)
-- -----------------------------------------------------------------------------

/-- A shell is closed (filled) when occupation equals capacity. -/
def is_closed (n_occ : ℕ) (cap : ℕ) : Prop :=
  n_occ = cap

/-- A fully occupied shell has zero seniority: all particles are paired. -/
theorem seniority_full_shell_zero (cap : ℕ) : seniority cap cap = 0 := by
  unfold seniority
  by_cases h : cap ≤ cap / 2
  · have hcap : cap = 0 := by omega
    simp [hcap]
  · simp [h]

/-- A closed shell, expressed through `is_closed`, has zero seniority. -/
theorem seniority_zero_of_closed (n_occ cap : ℕ) (h : is_closed n_occ cap) :
    seniority n_occ cap = 0 := by
  change n_occ = cap at h
  rw [h]
  exact seniority_full_shell_zero cap

-- -----------------------------------------------------------------------------
-- SECTION 4: Half-integer j-orbitals, parity, spin-orbit coupling, and magic numbers
-- -----------------------------------------------------------------------------

section HalfIntegerAndMagicNumbers

open InfoGeometry.Physics.NuclearSymmetrySectors

/-- Half-integer single-particle shell orbital labeled by `(n, l, 2j, 2m_j)`. -/
structure HalfIntegerOrbital where
  n : ℕ
  l : ℕ
  twoJ : ℕ
  twoM : ℤ
  deriving DecidableEq, Repr

/-- Exact validity predicate for a half-integer orbital:
`2j` is odd, `|2m| ≤ 2j`, and `2j - 2m` is even. -/
def HalfIntegerOrbital.IsValid (o : HalfIntegerOrbital) : Prop :=
  o.twoJ % 2 = 1 ∧ |o.twoM| ≤ (o.twoJ : ℤ) ∧ ((o.twoJ : ℤ) - o.twoM) % 2 = 0

/-- Orbital spatial parity `(-1)^l`. -/
def orbitalParity (l : ℕ) : ℝ := (-1 : ℝ) ^ l

/-- Exact bridge from `orbitalParity l` to `NuclearSymmetrySectors.orbitalSpatialParity l`. -/
theorem orbitalParity_eq_spatialParity_sign (l : ℕ) :
    orbitalParity l = (orbitalSpatialParity l).sign := by
  rw [orbitalParity, orbitalSpatialParity_sign]

/-- Map a half-integer orbital `(n, l, 2j, 2m)` to its `SpinParitySector`. -/
def HalfIntegerOrbital.toSpinParitySector (o : HalfIntegerOrbital) : SpinParitySector :=
  ⟨o.twoJ, orbitalSpatialParity o.l⟩

/-- Exact capacity `2j + 1 = twoJ + 1` of a `j`-subshell. -/
def halfIntegerCapacity (twoJ : ℕ) : ℕ := twoJ + 1

/-- Every half-integer orbital (`twoJ` odd) has strictly positive even capacity `2j + 1`. -/
theorem halfIntegerCapacity_even {twoJ : ℕ} (hodd : twoJ % 2 = 1) :
    Even (halfIntegerCapacity twoJ) := by
  unfold halfIntegerCapacity
  rcases Nat.odd_iff.mpr hodd with ⟨k, rfl⟩
  exact ⟨k + 1, by omega⟩

theorem halfIntegerCapacity_pos (twoJ : ℕ) : 0 < halfIntegerCapacity twoJ :=
  Nat.succ_pos twoJ

/-- The finite set of valid magnetic projections `twoM` for a given `twoJ`. -/
def validTwoMFinset (twoJ : ℕ) : Finset ℤ :=
  (Finset.Icc (-(twoJ : ℤ)) (twoJ : ℤ)).filter (fun m => ((twoJ : ℤ) - m) % 2 = 0)

theorem mem_validTwoMFinset_iff (twoJ : ℕ) (m : ℤ) :
    m ∈ validTwoMFinset twoJ ↔ |m| ≤ (twoJ : ℤ) ∧ ((twoJ : ℤ) - m) % 2 = 0 := by
  simp only [validTwoMFinset, Finset.mem_filter, Finset.mem_Icc, abs_le]

/-- Exact combinatorial proof that the number of valid `twoM` states in a `twoJ`-multiplet
is `twoJ + 1 = 2j + 1`. -/
theorem validTwoMFinset_card (twoJ : ℕ) :
    (validTwoMFinset twoJ).card = halfIntegerCapacity twoJ := by
  let f : Fin (twoJ + 1) → ℤ := fun k => (twoJ : ℤ) - 2 * (k.val : ℤ)
  have hf_inj : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    ext
    omega
  have him : Finset.univ.image f = validTwoMFinset twoJ := by
    ext m
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_validTwoMFinset_iff]
    constructor
    · rintro ⟨k, rfl⟩
      have hk : (k.val : ℤ) ≤ twoJ := by omega
      have hk0 : (0 : ℤ) ≤ k.val := Int.natCast_nonneg k.val
      dsimp [f]
      refine ⟨abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
      have hdiff : (twoJ : ℤ) - ((twoJ : ℤ) - 2 * (k.val : ℤ)) = 2 * (k.val : ℤ) := by ring
      rw [hdiff]
      omega
    · rintro ⟨habs, hmod⟩
      have hle := abs_le.mp habs
      have hd_nonneg : 0 ≤ (twoJ : ℤ) - m := by omega
      have hd_le : (twoJ : ℤ) - m ≤ 2 * (twoJ : ℤ) := by omega
      have hk_nat_lt : ((twoJ : ℤ) - m).toNat / 2 < twoJ + 1 := by omega
      refine ⟨⟨((twoJ : ℤ) - m).toNat / 2, hk_nat_lt⟩, ?_⟩
      dsimp [f]
      omega
  rw [← him, Finset.card_image_of_injective Finset.univ hf_inj, Finset.card_fin]
  rfl

/-- Spin-orbit coupling relation `j = l ± 1/2` (`twoJ = 2*l + 1` or `twoJ = 2*l - 1` for `l > 0`). -/
def spinOrbitCoupled (l twoJ : ℕ) : Prop :=
  twoJ = 2 * l + 1 ∨ (0 < l ∧ twoJ = 2 * l - 1)

theorem spinOrbitCoupled_odd {l twoJ : ℕ} (h : spinOrbitCoupled l twoJ) : twoJ % 2 = 1 := by
  rcases h with rfl | ⟨hl, rfl⟩ <;> omega

theorem spinOrbitCoupled_triangle {l twoJ : ℕ} (h : spinOrbitCoupled l twoJ) :
    2 * l ≤ twoJ + 1 ∧ twoJ ≤ 2 * l + 1 ∧ 1 ≤ 2 * l + twoJ := by
  rcases h with rfl | ⟨hl, rfl⟩ <;> omega

/-- Capacity of a spin-orbit doublet `(l + 1/2, l - 1/2)` for `0 < l` equals `2 * (2 * l + 1)`. -/
theorem spinOrbitDoubletCapacity (l : ℕ) (hl : 0 < l) :
    halfIntegerCapacity (2 * l + 1) + halfIntegerCapacity (2 * l - 1) = 2 * (2 * l + 1) := by
  unfold halfIntegerCapacity
  omega

/-- Eigenvalue of `l · s = (1/2) (j(j+1) - l(l+1) - 3/4)` in `ℚ`. -/
def spinOrbitExpectation (l twoJ : ℕ) : ℚ :=
  ((twoJ : ℚ) / 2 * ((twoJ : ℚ) / 2 + 1) - (l : ℚ) * ((l : ℚ) + 1) - 3 / 4) / 2

theorem spinOrbitExpectation_plus (l : ℕ) :
    spinOrbitExpectation l (2 * l + 1) = (l : ℚ) / 2 := by
  unfold spinOrbitExpectation
  push_cast
  ring

theorem spinOrbitExpectation_minus (l : ℕ) (hl : 0 < l) :
    spinOrbitExpectation l (2 * l - 1) = -((l : ℚ) + 1) / 2 := by
  unfold spinOrbitExpectation
  have hcast : ((2 * l - 1 : ℕ) : ℚ) = 2 * (l : ℚ) - 1 := by
    have h1 : 1 ≤ 2 * l := by omega
    rw [Nat.cast_sub h1]
    push_cast
    ring
  rw [hcast]
  ring

/-- Attractive nuclear spin-orbit interaction energy `V_ls = -2 κ ⟨l · s⟩`. -/
def spinOrbitSplittingEnergy (κ : ℚ) (l twoJ : ℕ) : ℚ :=
  -2 * κ * spinOrbitExpectation l twoJ

/-- Exact spin-orbit energy gap between `j = l - 1/2` and `j = l + 1/2`. -/
theorem spinOrbit_splitting_gap (κ : ℚ) (l : ℕ) (hl : 0 < l) :
    spinOrbitSplittingEnergy κ l (2 * l - 1) - spinOrbitSplittingEnergy κ l (2 * l + 1) =
      κ * (2 * (l : ℚ) + 1) := by
  unfold spinOrbitSplittingEnergy
  rw [spinOrbitExpectation_minus l hl, spinOrbitExpectation_plus l]
  ring

/-- For attractive nuclear spin-orbit coupling (`κ > 0`), the stretched partner `j = l + 1/2`
lies strictly lower in energy than `j = l - 1/2`, driving the intruder shells. -/
theorem spinOrbit_j_plus_lower_than_j_minus (κ : ℚ) (hκ : 0 < κ) (l : ℕ) (hl : 0 < l) :
    spinOrbitSplittingEnergy κ l (2 * l + 1) < spinOrbitSplittingEnergy κ l (2 * l - 1) := by
  have hgap := spinOrbit_splitting_gap κ l hl
  have hpos : 0 < κ * (2 * (l : ℚ) + 1) := by positivity
  linarith

/-- Total degeneracy `(N + 1)(N + 2)` of the `N`-th 3D isotropic harmonic oscillator major shell. -/
def hoMajorShellCapacity (N : ℕ) : ℕ := (N + 1) * (N + 2)

private theorem hoFilter_card (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun l => (n - l) % 2 = 0)).card = n / 2 + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    match n with
    | 0 => simp
    | 1 => decide
    | k + 2 =>
      let Sk := (Finset.range (k + 1)).filter (fun l => (k - l) % 2 = 0)
      have hdecomp : (Finset.range (k + 3)).filter (fun l => (k + 2 - l) % 2 = 0) =
          insert (k + 2) Sk := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Sk]
        omega
      have hnot : k + 2 ∉ Sk := by simp [Sk]
      rw [hdecomp, Finset.card_insert_of_notMem hnot, ihn k (by omega)]
      omega

/-- Exact proof that summing `2 * (2 * l + 1)` over all orbital angular momenta `l ≤ N`
with `l ≡ N (mod 2)` produces `(N + 1)(N + 2)`. -/
theorem hoMajorShell_subshell_sum (N : ℕ) :
    ∑ l ∈ (Finset.range (N + 1)).filter (fun l => (N - l) % 2 = 0), 2 * (2 * l + 1) =
      hoMajorShellCapacity N := by
  induction N with
  | zero =>
      simp [hoMajorShellCapacity]
  | succ N ih =>
      let S := (Finset.range (N + 1)).filter (fun l => (N - l) % 2 = 0)
      let T := (Finset.range (N + 2)).filter (fun l => (N + 1 - l) % 2 = 0)
      have hcardS : S.card = N / 2 + 1 := hoFilter_card N
      have himg_inj : Function.Injective (fun l : ℕ => l + 1) := by
        intro a b h
        dsimp only at h
        omega
      have hsum_shift : ∑ l ∈ S.image (fun l => l + 1), 2 * (2 * l + 1) =
          ∑ l ∈ S, 2 * (2 * l + 1) + 4 * S.card := by
        rw [Finset.sum_image (fun a _ b _ h => himg_inj h)]
        have hpt : ∀ l ∈ S, 2 * (2 * (l + 1) + 1) = 2 * (2 * l + 1) + 4 := by
          intro l _; ring
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
        ring
      by_cases hpar : (N + 1) % 2 = 0
      · have hT : T = insert 0 (S.image (fun l => l + 1)) := by
          ext l
          simp only [T, S, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_image]
          constructor
          · rintro ⟨hl1, hl2⟩
            rcases Nat.eq_zero_or_pos l with rfl | hlpos
            · exact Or.inl rfl
            · exact Or.inr ⟨l - 1, ⟨by omega, by omega⟩, by omega⟩
          · rintro (rfl | ⟨a, ⟨ha1, ha2⟩, rfl⟩)
            · exact ⟨by omega, hpar⟩
            · exact ⟨by omega, by omega⟩
        have h0not : 0 ∉ S.image (fun l => l + 1) := by simp
        rw [show (Finset.range (N + 2)).filter (fun l => (N + 1 - l) % 2 = 0) = T from rfl,
          hT, Finset.sum_insert h0not, hsum_shift, ih, hcardS]
        unfold hoMajorShellCapacity
        rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
        · omega
        · have hdiv : (2 * m + 1) / 2 = m := by omega
          rw [hdiv]; ring
      · have hT : T = S.image (fun l => l + 1) := by
          ext l
          simp only [T, S, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
          constructor
          · rintro ⟨hl1, hl2⟩
            have hlpos : 0 < l := by
              by_contra h0
              have : l = 0 := by omega
              subst this; exact hpar (by simpa using hl2)
            exact ⟨l - 1, ⟨by omega, by omega⟩, by omega⟩
          · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
            exact ⟨by omega, by omega⟩
        rw [show (Finset.range (N + 2)).filter (fun l => (N + 1 - l) % 2 = 0) = T from rfl,
          hT, hsum_shift, ih, hcardS]
        unfold hoMajorShellCapacity
        rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
        · have hdiv : (2 * m) / 2 = m := by omega
          rw [hdiv]; ring
        · omega

/-- Cumulative nucleon capacity of the first `k` harmonic oscillator shells `N = 0, ..., k - 1`. -/
def hoCumulativeCapacity (k : ℕ) : ℕ :=
  ∑ N ∈ Finset.range k, hoMajorShellCapacity N

theorem hoCumulativeCapacity_list :
    (List.range' 1 7).map hoCumulativeCapacity = [2, 8, 20, 40, 70, 112, 168] := by
  decide

/-- A single-particle `(N, l, 2j)` subshell in the Mayer--Jensen shell ordering. -/
structure ShellSubshell where
  N : ℕ
  l : ℕ
  twoJ : ℕ
  deriving DecidableEq, Repr

def ShellSubshell.IsValid (s : ShellSubshell) : Prop :=
  s.l ≤ s.N ∧ (s.N - s.l) % 2 = 0 ∧ spinOrbitCoupled s.l s.twoJ

def ShellSubshell.capacity (s : ShellSubshell) : ℕ :=
  halfIntegerCapacity s.twoJ

/-- The seven Mayer--Jensen spin-orbit major shells up to nucleon number `126`. -/
def nuclearMajorShells : List (List ShellSubshell) :=
  [ [⟨0, 0, 1⟩],
    [⟨1, 1, 3⟩, ⟨1, 1, 1⟩],
    [⟨2, 2, 5⟩, ⟨2, 0, 1⟩, ⟨2, 2, 3⟩],
    [⟨3, 3, 7⟩],
    [⟨3, 1, 3⟩, ⟨3, 3, 5⟩, ⟨3, 1, 1⟩, ⟨4, 4, 9⟩],
    [⟨4, 2, 5⟩, ⟨4, 4, 7⟩, ⟨4, 0, 1⟩, ⟨4, 2, 3⟩, ⟨5, 5, 11⟩],
    [⟨5, 3, 7⟩, ⟨5, 1, 3⟩, ⟨5, 5, 9⟩, ⟨5, 3, 5⟩, ⟨5, 1, 1⟩, ⟨6, 6, 13⟩] ]

/-- Every subshell appearing in `nuclearMajorShells` is physically valid (`l ≤ N`,
`N - l` even, `twoJ = 2*l ± 1`). -/
theorem nuclearMajorShells_all_valid :
    ∀ shell ∈ nuclearMajorShells, ∀ s ∈ shell, s.IsValid := by
  intro shell hshell s hs
  simp only [nuclearMajorShells, List.mem_cons, List.not_mem_nil, or_false] at hshell
  rcases hshell with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ShellSubshell.IsValid, spinOrbitCoupled]

/-- No subshell is duplicated across the seven Mayer--Jensen major shells. -/
theorem nuclearMajorShells_nodup : nuclearMajorShells.flatten.Nodup := by
  decide

/-- Capacity of a single major shell computed as the sum of `2j + 1` over its subshells. -/
def majorShellCapacity (shell : List ShellSubshell) : ℕ :=
  (shell.map ShellSubshell.capacity).sum

/-- Individual major-shell capacities `[2, 6, 12, 8, 22, 32, 44]`. -/
theorem nuclearMajorShells_capacities :
    nuclearMajorShells.map majorShellCapacity = [2, 6, 12, 8, 22, 32, 44] := by
  decide

/-- Cumulative magic numbers computed by summing `majorShellCapacity` prefix-by-prefix. -/
def nuclearMagicNumbers : List ℕ :=
  (List.range' 1 7).map fun k => ((nuclearMajorShells.take k).map majorShellCapacity).sum

/-- **Nuclear Shell Model Magic Numbers Theorem**:
Explicit harmonic-oscillator + spin-orbit shell-closure sums yield `[2, 8, 20, 28, 50, 82, 126]`. -/
theorem nuclear_magic_numbers_eq :
    nuclearMagicNumbers = [2, 8, 20, 28, 50, 82, 126] := by
  decide

/-- For shells `k ∈ {3, 4, 5, 6}`, the Mayer--Jensen spin-orbit magic number equals the
cumulative harmonic-oscillator shell closure `hoCumulativeCapacity k` plus the descending
spin-orbit intruder `j = k + 1/2` (`halfIntegerCapacity (2 * k + 1)`). -/
theorem spinOrbitMagicNumber_eq_ho_plus_intruder :
    [3, 4, 5, 6].map (fun k => hoCumulativeCapacity k + halfIntegerCapacity (2 * k + 1)) =
      [28, 50, 82, 126] := by
  decide

-- -----------------------------------------------------------------------------
-- SECTION 5: Nilsson asymptotic quantum numbers [N, n_z, Lambda] Omega
-- -----------------------------------------------------------------------------

/-- Nilsson asymptotic cylindrical state `[N, n_z, Lambda] Omega` with `twoOmega = 2 * Omega`. -/
structure NilssonAsymptoticState where
  n_z : ℕ
  n_perp : ℕ
  Lambda : ℕ
  twoOmega : ℕ
  omega_coupling : twoOmega = 2 * Lambda + 1 ∨ (0 < Lambda ∧ twoOmega = 2 * Lambda - 1)
  deriving DecidableEq, Repr

/-- Principal oscillator quantum number `N = n_z + 2 * n_perp + Lambda`. -/
def NilssonAsymptoticState.N (s : NilssonAsymptoticState) : ℕ :=
  s.n_z + 2 * s.n_perp + s.Lambda

theorem NilssonAsymptoticState.twoOmega_odd (s : NilssonAsymptoticState) :
    s.twoOmega % 2 = 1 := by
  rcases s.omega_coupling with h | ⟨_, h⟩ <;> omega

theorem NilssonAsymptoticState.twoOmega_pos (s : NilssonAsymptoticState) :
    0 < s.twoOmega := by
  rcases s.omega_coupling with h | ⟨_, h⟩ <;> omega

/-- Nilsson asymptotic spatial parity `(-1)^N`. -/
def NilssonAsymptoticState.parity (s : NilssonAsymptoticState) : SpatialParity :=
  orbitalSpatialParity s.N

theorem NilssonAsymptoticState.parity_sign (s : NilssonAsymptoticState) :
    s.parity.sign = (-1 : ℝ) ^ s.N :=
  orbitalSpatialParity_sign s.N

/-- Deformed harmonic oscillator asymptotic energy
`E = ħω₀ (N + 3/2 + ε (N/3 - n_z))`. -/
def nilssonAsymptoticEnergy (hbarOmega0 eps : 𝒦) (s : NilssonAsymptoticState) : 𝒦 :=
  hbarOmega0 * ((s.N : 𝒦) + 3 / 2 + eps * ((s.N : 𝒦) / 3 - (s.n_z : 𝒦)))

theorem nilssonAsymptoticEnergy_diff_same_shell (hbarOmega0 eps : 𝒦)
    (s₁ s₂ : NilssonAsymptoticState) (hN : s₁.N = s₂.N) :
    nilssonAsymptoticEnergy hbarOmega0 eps s₁ - nilssonAsymptoticEnergy hbarOmega0 eps s₂ =
      hbarOmega0 * eps * ((s₂.n_z : 𝒦) - (s₁.n_z : 𝒦)) := by
  unfold nilssonAsymptoticEnergy
  rw [hN]
  ring

/-- For prolate deformation (`ε > 0`), states with larger `n_z` lie lower in energy. -/
theorem nilsson_prolate_splitting (hbarOmega0 eps : ℝ)
    (hw : 0 < hbarOmega0) (heps : 0 < eps)
    (s₁ s₂ : NilssonAsymptoticState) (hN : s₁.N = s₂.N) (hnz : s₂.n_z < s₁.n_z) :
    nilssonAsymptoticEnergy hbarOmega0 eps s₁ < nilssonAsymptoticEnergy hbarOmega0 eps s₂ := by
  have hdiff := nilssonAsymptoticEnergy_diff_same_shell hbarOmega0 eps s₁ s₂ hN
  have hneg : (s₂.n_z : ℝ) - (s₁.n_z : ℝ) < 0 := by
    have : (s₂.n_z : ℝ) < (s₁.n_z : ℝ) := by exact_mod_cast hnz
    linarith
  have hpe : 0 < hbarOmega0 * eps := mul_pos hw heps
  have hprod : hbarOmega0 * eps * ((s₂.n_z : ℝ) - (s₁.n_z : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg hpe hneg
  linarith

/-- For oblate deformation (`ε < 0`), the splitting reverses sign: larger `n_z` lies higher. -/
theorem nilsson_oblate_splitting (hbarOmega0 eps : ℝ)
    (hw : 0 < hbarOmega0) (heps : eps < 0)
    (s₁ s₂ : NilssonAsymptoticState) (hN : s₁.N = s₂.N) (hnz : s₂.n_z < s₁.n_z) :
    nilssonAsymptoticEnergy hbarOmega0 eps s₂ < nilssonAsymptoticEnergy hbarOmega0 eps s₁ := by
  have hdiff := nilssonAsymptoticEnergy_diff_same_shell hbarOmega0 eps s₁ s₂ hN
  have hneg : (s₂.n_z : ℝ) - (s₁.n_z : ℝ) < 0 := by
    have : (s₂.n_z : ℝ) < (s₁.n_z : ℝ) := by exact_mod_cast hnz
    linarith
  have hpe : hbarOmega0 * eps < 0 := mul_neg_of_pos_of_neg hw heps
  have hprod : 0 < hbarOmega0 * eps * ((s₂.n_z : ℝ) - (s₁.n_z : ℝ)) :=
    mul_pos_of_neg_of_neg hpe hneg
  linarith

/-- Exact prolate/oblate splitting sign reversal `ΔE(ε) = -ΔE(-ε)`. -/
theorem nilsson_prolate_oblate_sign_reversal (hbarOmega0 eps : 𝒦)
    (s₁ s₂ : NilssonAsymptoticState) (hN : s₁.N = s₂.N) :
    nilssonAsymptoticEnergy hbarOmega0 (-eps) s₁ - nilssonAsymptoticEnergy hbarOmega0 (-eps) s₂ =
      -(nilssonAsymptoticEnergy hbarOmega0 eps s₁ - nilssonAsymptoticEnergy hbarOmega0 eps s₂) := by
  rw [nilssonAsymptoticEnergy_diff_same_shell hbarOmega0 (-eps) s₁ s₂ hN,
    nilssonAsymptoticEnergy_diff_same_shell hbarOmega0 eps s₁ s₂ hN]
  ring

/-- Asymptotic Nilsson `K = 1/2` decoupling parameter:
`a = (-1)^N (N + 1/2)` when `Λ = 0` and `2Ω = 1` (and `0` otherwise). -/
def nilssonDecouplingParameter (s : NilssonAsymptoticState) : ℝ :=
  if s.Lambda = 0 ∧ s.twoOmega = 1 then (-1 : ℝ) ^ s.N * ((s.N : ℝ) + 1 / 2) else 0

theorem nilssonDecouplingParameter_Lambda_zero (s : NilssonAsymptoticState)
    (hL : s.Lambda = 0) (hO : s.twoOmega = 1) :
    nilssonDecouplingParameter s = (-1 : ℝ) ^ s.N * ((s.N : ℝ) + 1 / 2) := by
  simp [nilssonDecouplingParameter, hL, hO]

theorem nilssonDecouplingParameter_eq_zero_of_Lambda_ne_zero (s : NilssonAsymptoticState)
    (hL : s.Lambda ≠ 0) :
    nilssonDecouplingParameter s = 0 := by
  simp [nilssonDecouplingParameter, hL]

theorem nilsson_Lambda_zero_parity_eq_nz (s : NilssonAsymptoticState) (hL : s.Lambda = 0) :
    (-1 : ℝ) ^ s.N = (-1 : ℝ) ^ s.n_z := by
  rw [NilssonAsymptoticState.N, hL, add_zero, pow_add, pow_mul]
  norm_num

end HalfIntegerAndMagicNumbers

/-! ## Section 5: Canonical inhabitants, Nilsson `[N, n_z, Λ] Ω` orbitals & Taxonomy Bridge -/

section NilssonOrbitalsAndTaxonomy

open InfoGeometry.Physics.NuclearSymmetrySectors

/-- Canonical `1s_{1/2}` shell orbital inhabitant (`n = 0, l = 0, j = 1, m = 1`). -/
def defaultShellOrbital : ShellOrbital where
  n := 0
  l := 0
  j := 1
  m := 1

/-- Canonical `1s_{1/2}` half-integer orbital inhabitant (`n = 0, l = 0, 2j = 1, 2m = 1`). -/
def defaultHalfIntegerOrbital : HalfIntegerOrbital where
  n := 0
  l := 0
  twoJ := 1
  twoM := 1

/-- Canonical `1s_{1/2}` subshell inhabitant (`N = 0, l = 0, 2j = 1`). -/
def defaultShellSubshell : ShellSubshell where
  N := 0
  l := 0
  twoJ := 1

/-- Canonical `[0, 0, 0] 1/2` Nilsson asymptotic state inhabitant. -/
def defaultNilssonAsymptoticState : NilssonAsymptoticState where
  n_z := 0
  n_perp := 0
  Lambda := 0
  twoOmega := 1
  omega_coupling := Or.inl rfl

/-- Nilsson cylindrical single-particle orbital `[N, n_z, Λ] Ω` with explicit
spin projection `twoSigma = ±1` (`isUp : Bool`, or integer `±1`) and `twoOmega = 2 * Ω`. -/
structure NilssonOrbital where
  N : ℕ
  n_z : ℕ
  lam : ℕ
  spinUp : Bool
  twoOmega : ℕ
  deriving DecidableEq, Repr

/-- Canonical `[0, 0, 0] 1/2^+` Nilsson orbital inhabitant. -/
def defaultNilssonOrbital : NilssonOrbital where
  N := 0
  n_z := 0
  lam := 0
  spinUp := true
  twoOmega := 1

/-- Doubled spin projection `2Σ ∈ {+1, -1}` of a `NilssonOrbital`. -/
def NilssonOrbital.twoSigma (o : NilssonOrbital) : ℤ :=
  if o.spinUp then 1 else -1

/-- Quantum-number validity predicate for a Nilsson asymptotic orbital `[N, n_z, Λ] Ω`:
1. `n_z + Λ ≤ N` with even radial quanta `(N - n_z - Λ) % 2 = 0`;
2. `2Ω = 2Λ + 2Σ` (`> 0`, prohibiting `Λ = 0, Σ = -1/2` unphysical sign). -/
def validNilsson (o : NilssonOrbital) :
    Prop :=
  o.n_z + o.lam ≤ o.N ∧ (o.N - o.n_z - o.lam) % 2 = 0 ∧
    (o.twoOmega : ℤ) = 2 * (o.lam : ℤ) + o.twoSigma ∧ 0 < o.twoOmega

/-- Radial oscillator quantum number `n_⊥ = (N - n_z - Λ) / 2`. -/
def nilssonRadialQuanta (o : NilssonOrbital) : ℕ :=
  (o.N - o.n_z - o.lam) / 2

/-- Spatial parity `(-1)^N` of a Nilsson orbital. -/
def nilssonParity (o : NilssonOrbital) : SpatialParity :=
  orbitalSpatialParity o.N

/-- Generalized Nilsson oscillator energy `E = ħω₀ ((N + 3/2) + δ (N/3 - n_z))`
over any characteristic-zero field `𝒦`. -/
def nilssonOscillatorEnergy (hbarOmega0 delta : 𝒦) (o : NilssonOrbital) : 𝒦 :=
  hbarOmega0 * ((o.N : 𝒦) + 3 / 2 + delta * ((o.N : 𝒦) / 3 - (o.n_z : 𝒦)))

/-- Axial angular-momentum conservation `2Ω = 2Λ + 2Σ` and `2Ω ≤ 2N + 1` in any valid Nilsson orbital. -/
theorem nilsson_axial_conservation (o : NilssonOrbital) (h : validNilsson o) :
    (o.twoOmega : ℤ) = 2 * (o.lam : ℤ) + o.twoSigma ∧ o.twoOmega ≤ 2 * o.N + 1 := by
  unfold validNilsson at h
  unfold NilssonOrbital.twoSigma at h ⊢
  rcases h with ⟨hbound, _, hax, _⟩
  refine ⟨hax, ?_⟩
  cases hup : o.spinUp <;> simp [hup] at hax <;> omega

/-- Radial oscillator decomposition `N = n_z + 2 n_⊥ + Λ` for any valid Nilsson orbital. -/
theorem nilsson_radial_decomposition (o : NilssonOrbital) (h : validNilsson o) :
    o.N = o.n_z + 2 * nilssonRadialQuanta o + o.lam := by
  unfold validNilsson at h
  unfold nilssonRadialQuanta
  rcases h with ⟨hbound, heven, _, _⟩
  omega

/-- Half-integer nature of Nilsson projection `2Ω` (`2Ω ≡ 1 mod 2`). -/
theorem nilsson_twoOmega_odd (o : NilssonOrbital) (h : validNilsson o) :
    o.twoOmega % 2 = 1 := by
  unfold validNilsson NilssonOrbital.twoSigma at h
  rcases h with ⟨_, _, hax, _⟩
  cases hup : o.spinUp <;> simp [hup] at hax <;> omega

/-- Sharp upper bound `2Ω ≤ 2N + 1` on axial projection within major shell `N`. -/
theorem nilsson_twoOmega_bound (o : NilssonOrbital) (h : validNilsson o) :
    o.twoOmega ≤ 2 * o.N + 1 := by
  have hc := nilsson_axial_conservation o h
  exact hc.2

theorem nilssonParity_sign (o : NilssonOrbital) :
    (nilssonParity o).sign = (-1 : ℝ) ^ o.N := by
  unfold nilssonParity
  exact orbitalSpatialParity_sign o.N

/-- Nilsson cylindrical parity matches spherical parity `(-1)^{2 n + l}` whenever `N = 2n + l`. -/
theorem nilssonParity_matches_spherical (o : NilssonOrbital) (n l : ℕ)
    (hN : o.N = 2 * n + l) :
    (nilssonParity o).sign = orbitalParity l := by
  rw [nilssonParity_sign, hN, orbitalParity, pow_add, pow_mul]
  norm_num

/-- Isotropic spherical limit (`δ = 0`): Nilsson energy collapses to `ħω₀ (N + 3/2)`. -/
theorem nilssonOscillatorEnergy_isotropic (hbarOmega0 : 𝒦) (o : NilssonOrbital) :
    nilssonOscillatorEnergy hbarOmega0 0 o = hbarOmega0 * ((o.N : 𝒦) + 3 / 2) := by
  unfold nilssonOscillatorEnergy
  ring

/-- Total nucleon degeneracy `(N + 1)(N + 2)` of harmonic-oscillator major shell `N`,
matching the summed spherical subshell capacities `∑_{l, j} (2j + 1)`. -/
theorem oscillator_shell_degeneracy (N : ℕ) :
    hoMajorShellCapacity N = (N + 1) * (N + 2) := by
  rfl

/-- Convert any valid `NilssonOrbital` into its `NilssonAsymptoticState`. -/
def NilssonOrbital.toAsymptoticState (o : NilssonOrbital) (h : validNilsson o) :
    NilssonAsymptoticState where
  n_z := o.n_z
  n_perp := nilssonRadialQuanta o
  Lambda := o.lam
  twoOmega := o.twoOmega
  omega_coupling := by
    have hax := (nilsson_axial_conservation o h).1
    unfold NilssonOrbital.twoSigma at hax
    cases hup : o.spinUp
    · simp only [hup, Bool.false_eq_true, ↓reduceIte] at hax
      right
      have hpos : 0 < o.lam := by
        have hgt : 0 < o.twoOmega := h.2.2.2
        omega
      refine ⟨hpos, ?_⟩
      omega
    · simp only [hup, ↓reduceIte] at hax
      left
      omega

theorem NilssonOrbital.toAsymptoticState_N (o : NilssonOrbital) (h : validNilsson o) :
    (o.toAsymptoticState h).N = o.N := by
  unfold NilssonAsymptoticState.N toAsymptoticState
  dsimp only
  exact (nilsson_radial_decomposition o h).symm

/-- Embed a `NilssonOrbital` and base `QuantumNumbers` into `NuclearTaxonomyPacket`. -/
def NilssonOrbital.toTaxonomyPacket (o : NilssonOrbital) (q : QuantumNumbers) :
    NuclearTaxonomyPacket where
  base := q
  twoK := o.twoOmega
  twoOmega := o.twoOmega
  spatialParitySign := if o.N % 2 = 0 then 1 else -1
  spatial_parity_sq := by split_ifs <;> norm_num
  wmSector := .wmEven
  chitureSector := .chiEven
  spinPairing := .spinSinglet
  isospinPairing := .isoTriplet

theorem nilsson_taxonomy_parity_eq (o : NilssonOrbital) (q : QuantumNumbers) :
    ((o.toTaxonomyPacket q).spatialParitySign : ℝ) = (nilssonParity o).sign := by
  unfold NilssonOrbital.toTaxonomyPacket
  dsimp only
  rw [nilssonParity_sign]
  rcases Nat.even_or_odd' o.N with ⟨k, hk | hk⟩
  · rw [hk]
    have hmod : (2 * k) % 2 = 0 := by omega
    simp only [hmod, ↓reduceIte]
    rw [pow_mul]
    norm_num
  · rw [hk]
    have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
    simp only [hmod, ↓reduceIte]
    rw [pow_add, pow_mul]
    norm_num

section ParitySegregationBridge

open InfoGeometry.Physics.NuclearSymmetrySectors

/-- **Parity Segregation Theorem (Spatial vs Quasiparticle Fermion Parity)**:
Given any `NuclearQuantumNumberPacket.QuantumNumbers` packet `q`, the quasiparticle
fermion parity `q.quasiparticleParity = (-1)^n` does NOT determine `SpatialParity`:
there exist two single-particle `SpinParitySector` states sharing the same `twoJ = q.twoJ`
and compatible with the identical `q` packet (same occupation number and quasiparticle parity)
that carry opposite `SpatialParity` (`orbitalSpatialParity 0` vs `orbitalSpatialParity 1`),
and a parity-preserving Hamiltonian cannot mix them. -/
theorem spatialParity_segregated_from_quasiparticleParity
    (q : QuantumNumbers) :
    let sPos : SpinParitySector := ⟨q.twoJ, orbitalSpatialParity 0⟩
    let sNeg : SpinParitySector := ⟨q.twoJ, orbitalSpatialParity 1⟩
    sPos.twoJ = sNeg.twoJ ∧
    sPos.parity ≠ sNeg.parity ∧
    (q.quasiparticleParity = 1 - 2 * q.occupationNumber) ∧
    (∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
      (P H Pi Pf : Module.End ℝ V),
      P.comp Pi = sPos.parity.sign • Pi →
      Pf.comp P = sNeg.parity.sign • Pf →
      P.comp H = H.comp P →
      Pf.comp (H.comp Pi) = 0) := by
  refine ⟨rfl, ?_, q.quasiparticleParity_formula, ?_⟩
  · simp [orbitalSpatialParity]
  · intro V _ _ P H Pi Pf hPi hPf hcomm
    exact hamiltonian_no_parity_mixing P H Pi Pf _ _ hPi hPf hcomm
      (by simp [orbitalSpatialParity])

end ParitySegregationBridge

end NilssonOrbitalsAndTaxonomy

end InfoGeometry.Physics.NuclearShellModel
