import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Volume.Pfaffian
import Mathlib.Data.Sign.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Order.IntermediateValue
set_option linter.unnecessarySimpa false

/-!
# Majorana Kitaev Chains and Tiling

Finite chain layer where macroscopic volume is the product of local Pfaffians.
-/

namespace InfoGeometry.Quantum.KitaevChain

open InfoGeometry.Krein

open RealMajoranaCategory
open InfoGeometry.Volume.Pfaffian

/-- A Kitaev cell: a real Majorana core with a skew channel operator. -/
structure KitaevCell where
  core : RealMajoranaCore
  [instV : NormedAddCommGroup core.V]
  [instInner : InnerProductSpace ℝ core.V]
  [instComp : CompleteSpace core.V]
  [instKrein : KreinSpace core.V]
  [instFinite : FiniteDimensional ℝ core.V]
  pairing : core.V →ₗ[ℝ] core.V
  is_skew : InfoGeometry.Volume.Pfaffian.IsSkewSymmetric pairing

/--
One-parameter cocycle on a single Kitaev cell.
The cocycle law is expressed by composition in `End(core.V)`.
-/
structure KitaevCocycle (C : KitaevCell) where
  U : ℝ → C.core.V →ₗ[ℝ] C.core.V
  cocycle : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)

/-- Trivial identity cocycle (useful neutral element in the finite scaffold). -/
def trivialKitaevCocycle (C : KitaevCell) : KitaevCocycle C where
  U := fun _ => LinearMap.id
  cocycle := by
    intro s t
    simp

/-- Pfaffian attached to a Kitaev cell. -/
noncomputable def KitaevCell.pfaffian (c : KitaevCell) : ℝ := by
  let _ : NormedAddCommGroup c.core.V := c.instV
  let _ : InnerProductSpace ℝ c.core.V := c.instInner
  let _ : CompleteSpace c.core.V := c.instComp
  let _ : KreinSpace c.core.V := c.instKrein
  let _ : FiniteDimensional ℝ c.core.V := c.instFinite
  exact InfoGeometry.Volume.Pfaffian.pfaffian (H := c.core.V) c.pairing

/-- Macroscopic volume proxy: product of microscopic cell Pfaffians. -/
noncomputable def macroscopicVolume (chain : List KitaevCell) : ℝ :=
  (chain.map (fun c : KitaevCell => c.pfaffian)).prod

/-- Definitional form of the tiling identity. -/
theorem macroscopicVolume_eq_prod_pfaffians (chain : List KitaevCell) :
    macroscopicVolume chain = (chain.map (fun c : KitaevCell => c.pfaffian)).prod := rfl

/--
Concatenation law for the finite tiling volume: the macroscopic volume of two
concatenated chains factors as the product of their macroscopic volumes.
-/
theorem macroscopicVolume_append (chain₁ chain₂ : List KitaevCell) :
    macroscopicVolume (chain₁ ++ chain₂) = macroscopicVolume chain₁ * macroscopicVolume chain₂ := by
  simp [macroscopicVolume, List.map_append, List.prod_append]

/-- Singleton normalization: a one-cell chain has macroscopic volume equal to its Pfaffian. -/
theorem macroscopicVolume_singleton (c : KitaevCell) :
    macroscopicVolume [c] = c.pfaffian := by
  simp [macroscopicVolume]

/--
Sign-valued (`{-1,0,1}`) topological index of a finite Kitaev chain, obtained
as the sign of the macroscopic Pfaffian product.
-/
noncomputable def topologicalIndex (chain : List KitaevCell) : SignType :=
  SignType.sign (macroscopicVolume chain)

/--
The chain topological sign index is multiplicative under concatenation.
This is the sign-level counterpart of `macroscopicVolume_append`.
-/
theorem topologicalIndex_append (chain₁ chain₂ : List KitaevCell) :
    topologicalIndex (chain₁ ++ chain₂) = topologicalIndex chain₁ * topologicalIndex chain₂ := by
  simpa [topologicalIndex, macroscopicVolume_append] using
    (sign_mul (macroscopicVolume chain₁) (macroscopicVolume chain₂))



/-- A chain is gapped iff its macroscopic Pfaffian product is nonzero. -/
def IsGapped (chain : List KitaevCell) : Prop :=
  macroscopicVolume chain ≠ 0

/-- A chain is critical iff its macroscopic Pfaffian product vanishes. -/
def IsCritical (chain : List KitaevCell) : Prop :=
  macroscopicVolume chain = 0

/-- A microscopic defect is a cell whose Pfaffian vanishes. -/
def IsDefect (c : KitaevCell) : Prop :=
  c.pfaffian = 0

/-- A chain carries a defect iff one of its cells is critical. -/
def HasDefect (chain : List KitaevCell) : Prop :=
  ∃ c ∈ chain, IsDefect c

/-- Gapped chains lie in the binary topological sector `{-1, 1}`. -/
theorem gapped_topologicalIndex_binary
    (chain : List KitaevCell) (hgap : IsGapped chain) :
    topologicalIndex chain = -1 ∨ topologicalIndex chain = 1 := by
  rcases lt_trichotomy (macroscopicVolume chain) 0 with hneg | hzero | hpos
  · left
    simp [topologicalIndex, sign_neg hneg]
  · exact (hgap hzero).elim
  · right
    simp [topologicalIndex, sign_pos hpos]

/-- Critical chains are exactly the chains with vanishing sign index. -/
theorem isCritical_iff_topologicalIndex_eq_zero (chain : List KitaevCell) :
    IsCritical chain ↔ topologicalIndex chain = 0 := by
  unfold IsCritical topologicalIndex
  simpa using
    (sign_eq_zero_iff : SignType.sign (macroscopicVolume chain) = 0 ↔ macroscopicVolume chain = 0).symm

/-- A one-cell chain is defective exactly when it is critical. -/
theorem hasDefect_singleton_iff_isCritical (c : KitaevCell) :
    HasDefect [c] ↔ IsCritical [c] := by
  simp [HasDefect, IsDefect, IsCritical, macroscopicVolume_singleton]

/-- A chain has a defect exactly when its macroscopic Pfaffian product vanishes. -/
theorem hasDefect_iff_isCritical (chain : List KitaevCell) :
    HasDefect chain ↔ IsCritical chain := by
  induction chain with
  | nil =>
      simp [HasDefect, IsCritical, macroscopicVolume]
  | cons c cs ih =>
      simp [HasDefect, IsDefect, IsCritical, macroscopicVolume, mul_eq_zero]

/-- A finite chain is gapless in this scaffold iff its sign index vanishes. -/
theorem topologicalIndex_eq_zero_iff (chain : List KitaevCell) :
    topologicalIndex chain = 0 ↔ macroscopicVolume chain = 0 := by
  simpa [topologicalIndex] using
    (sign_eq_zero_iff :
      SignType.sign (macroscopicVolume chain) = 0 ↔ macroscopicVolume chain = 0)

/--
In the gapped case (`macroscopicVolume ≠ 0`), the sign index is necessarily
binary (`-1` or `1`), matching the usual finite `ℤ₂` phase dichotomy.
-/
theorem topologicalIndex_eq_neg_one_or_one_of_macroscopicVolume_ne_zero
    (chain : List KitaevCell) (hVol : macroscopicVolume chain ≠ 0) :
    topologicalIndex chain = -1 ∨ topologicalIndex chain = 1 := by
  rcases lt_trichotomy (macroscopicVolume chain) 0 with hneg | hzero | hpos
  · left
    simp [topologicalIndex, sign_neg hneg]
  · exact (hVol hzero).elim
  · right
    simp [topologicalIndex, sign_pos hpos]

/--
`SignType` to `ZMod 2` phase map: `-1 ↦ 1`, `0 ↦ 0`, `1 ↦ 0`.
In the gapped regime (`±1` only), this is the usual finite `ℤ₂` index.
-/
def signTypeToZ2 : SignType → ZMod 2
  | SignType.neg => 1
  | _ => 0

/--
Multiplicativity-to-additivity bridge for nonzero signs (`±1` sector):
the `signTypeToZ2` map sends multiplication in `SignType` to addition in `ZMod 2`.
-/
theorem signTypeToZ2_mul_of_ne_zero {s₁ s₂ : SignType}
    (h₁ : s₁ ≠ 0) (h₂ : s₂ ≠ 0) :
    signTypeToZ2 (s₁ * s₂) = signTypeToZ2 s₁ + signTypeToZ2 s₂ := by
  rcases SignType.trichotomy s₁ with hs₁ | hs₁ | hs₁
  · rcases SignType.trichotomy s₂ with hs₂ | hs₂ | hs₂
    · subst hs₁
      subst hs₂
      decide
    · exact (h₂ hs₂).elim
    · subst hs₁
      subst hs₂
      decide
  · exact (h₁ hs₁).elim
  · rcases SignType.trichotomy s₂ with hs₂ | hs₂ | hs₂
    · subst hs₁
      subst hs₂
      decide
    · exact (h₂ hs₂).elim
    · subst hs₁
      subst hs₂
      decide

/-- `ZMod 2`-valued chain phase index induced from the sign index. -/
noncomputable def topologicalIndexZ2 (chain : List KitaevCell) : ZMod 2 :=
  signTypeToZ2 (topologicalIndex chain)

/--
Append law for the `ZMod 2` chain index in the gapped regime.
This is the finite chain version of the `ℤ₂` topological phase fusion rule.
-/
theorem topologicalIndexZ2_append_of_macroscopicVolume_ne_zero
    (chain₁ chain₂ : List KitaevCell)
    (h₁ : macroscopicVolume chain₁ ≠ 0)
    (h₂ : macroscopicVolume chain₂ ≠ 0) :
    topologicalIndexZ2 (chain₁ ++ chain₂)
      = topologicalIndexZ2 chain₁ + topologicalIndexZ2 chain₂ := by
  have hs₁ : topologicalIndex chain₁ ≠ 0 := by
    intro hs₁zero
    exact h₁ ((topologicalIndex_eq_zero_iff chain₁).1 hs₁zero)
  have hs₂ : topologicalIndex chain₂ ≠ 0 := by
    intro hs₂zero
    exact h₂ ((topologicalIndex_eq_zero_iff chain₂).1 hs₂zero)
  unfold topologicalIndexZ2
  rw [topologicalIndex_append]
  exact signTypeToZ2_mul_of_ne_zero hs₁ hs₂



/-- A continuous scalar path crossing from negative to positive must hit zero. -/
lemma zero_exists_of_opposite_sign
    {f : ℝ → ℝ} {t : ℝ}
    (hf : Continuous f)
    (hneg : f 0 < 0)
    (hpos : 0 < f t) :
    ∃ s ∈ Set.uIcc 0 t, f s = 0 := by
  have hsurj : Set.SurjOn f (Set.uIcc 0 t) (Set.uIcc (f 0) (f t)) := by
    exact (hf.continuousOn).surjOn_uIcc Set.left_mem_uIcc Set.right_mem_uIcc
  have hzero : (0 : ℝ) ∈ Set.uIcc (f 0) (f t) := by
    exact Set.mem_uIcc.mpr <| Or.inl ⟨hneg.le, hpos.le⟩
  rcases hsurj hzero with ⟨s, hs, hs0⟩
  exact ⟨s, hs, hs0⟩

/-- A continuous scalar path crossing from positive to negative must hit zero. -/
lemma zero_exists_of_opposite_sign_symm
    {f : ℝ → ℝ} {t : ℝ}
    (hf : Continuous f)
    (hpos : 0 < f 0)
    (hneg : f t < 0) :
    ∃ s ∈ Set.uIcc 0 t, f s = 0 := by
  have hzero := zero_exists_of_opposite_sign
    (f := fun s => -f s) (t := t) hf.neg
    (by simpa using (neg_lt_zero.mpr hpos))
    (by simpa using (neg_pos.mpr hneg))
  rcases hzero with ⟨s, hs, hs0⟩
  have hs0' : f s = 0 := by
    linarith
  exact ⟨s, hs, hs0'⟩

/--
If a continuous path of gapped chains changes topological sector, then it must
cross the critical set and therefore carry a defect at some intermediate time.
-/
theorem index_change_forces_defect_crossing
    {γ : ℝ → List KitaevCell} {t : ℝ}
    (hcont : Continuous fun s => macroscopicVolume (γ s))
    (hstart : IsGapped (γ 0))
    (hend : IsGapped (γ t))
    (hjump : topologicalIndex (γ 0) ≠ topologicalIndex (γ t)) :
    ∃ s ∈ Set.uIcc 0 t, HasDefect (γ s) := by
  rcases gapped_topologicalIndex_binary (γ 0) hstart with h0 | h0
  · rcases gapped_topologicalIndex_binary (γ t) hend with ht | ht
    · exfalso
      exact hjump (h0.trans ht.symm)
    · have hneg : macroscopicVolume (γ 0) < 0 := by
        exact sign_eq_neg_one_iff.mp (by simpa [topologicalIndex] using h0)
      have hpos : 0 < macroscopicVolume (γ t) := by
        exact sign_eq_one_iff.mp (by simpa [topologicalIndex] using ht)
      rcases zero_exists_of_opposite_sign (f := fun s => macroscopicVolume (γ s))
          (t := t) hcont hneg hpos with ⟨s, hs, hs0⟩
      exact ⟨s, hs, (hasDefect_iff_isCritical (γ s)).mpr (by simpa [IsCritical] using hs0)⟩
  · rcases gapped_topologicalIndex_binary (γ t) hend with ht | ht
    · have hpos : 0 < macroscopicVolume (γ 0) := by
        exact sign_eq_one_iff.mp (by simpa [topologicalIndex] using h0)
      have hneg : macroscopicVolume (γ t) < 0 := by
        exact sign_eq_neg_one_iff.mp (by simpa [topologicalIndex] using ht)
      rcases zero_exists_of_opposite_sign_symm (f := fun s => macroscopicVolume (γ s))
          (t := t) hcont hpos hneg with ⟨s, hs, hs0⟩
      exact ⟨s, hs, (hasDefect_iff_isCritical (γ s)).mpr (by simpa [IsCritical] using hs0)⟩
    · exfalso
      exact hjump (h0.trans ht.symm)

/--
Kitaev tiling identity: the macroscopic volume is the product
of microscopic cell Pfaffians.
-/
theorem kitaev_tiling_identity (chain : List KitaevCell) :
    ∃ (Vol : ℝ), Vol = (chain.map (fun (c : KitaevCell) => c.pfaffian)).prod :=
  ⟨macroscopicVolume chain, rfl⟩

/--
If each microscopic cell has normalized Pfaffian `1`, then the macroscopic
volume proxy is pinned to `1`.
-/
theorem macroscopicVolume_eq_one_of_pfaffian_one
    (chain : List KitaevCell)
    (hPf : ∀ c : KitaevCell, c ∈ chain → c.pfaffian = 1) :
    macroscopicVolume chain = 1 := by
  induction chain with
  | nil =>
      simp [macroscopicVolume]
  | cons c cs ih =>
      have hc : c.pfaffian = 1 := hPf c (by simp)
      have hcs : macroscopicVolume cs = 1 := by
        apply ih
        intro c' hc'
        exact hPf c' (by simp [hc'])
      have hcs' : (cs.map (fun c : KitaevCell => c.pfaffian)).prod = 1 := by
        simpa [macroscopicVolume] using hcs
      simp [macroscopicVolume, hc, hcs']

/-! ## Operator Algebra & Boundary Majorana Zero Mode -/

open BigOperators

/-- Commutator of two operators in a ring: `[A, B] = A * B - B * A`. -/
def commutator {A : Type*} [Ring A] (a b : A) : A := a * b - b * a

/-- Structure representing an `N`-site chain with `2N` Majorana operators `γ`. -/
structure MajoranaOperators (N : ℕ) (A : Type*) [Ring A] where
  γ : Fin (2 * N) → A
  h_ortho : ∀ m n, m ≠ n → γ m * γ n + γ n * γ m = 0

/-! ## Noncommutative two-mode commutation owner -/

/--
Moving a Majorana generator past a product of two distinct modes produces two
sign changes.  This is the reusable noncommutative Clifford calculation behind
both boundary zero-mode theorems below.
-/
lemma gamma_comm_product_of_avoids {A : Type*} [Ring A] {N : ℕ}
    (ops : MajoranaOperators N A) (k a b : Fin (2 * N))
    (hka : k ≠ a) (hkb : k ≠ b) :
    ops.γ k * (ops.γ a * ops.γ b) =
      (ops.γ a * ops.γ b) * ops.γ k := by
  have h_anti_a : ops.γ k * ops.γ a = -(ops.γ a * ops.γ k) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho k a hka)
  have h_anti_b : ops.γ k * ops.γ b = -(ops.γ b * ops.γ k) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho k b hkb)
  calc
    ops.γ k * (ops.γ a * ops.γ b)
        = (ops.γ k * ops.γ a) * ops.γ b := by rw [mul_assoc]
    _ = (-(ops.γ a * ops.γ k)) * ops.γ b := by rw [h_anti_a]
    _ = -(ops.γ a * (ops.γ k * ops.γ b)) := by
      rw [neg_mul, mul_assoc]
    _ = -(ops.γ a * (-(ops.γ b * ops.γ k))) := by rw [h_anti_b]
    _ = (ops.γ a * ops.γ b) * ops.γ k := by
      rw [mul_neg, neg_neg, mul_assoc]

/-- The Kitaev Hamiltonian at the topological sweet spot (`μ = 0`, `t = Δ`). -/
noncomputable def sweetSpotHamiltonian {A : Type*} [Ring A] {N : ℕ}
    (ops : MajoranaOperators N A) (it : A) : A :=
  ∑ j ∈ Finset.attach (Finset.range (N - 1)),
    have hj : j.1 < N - 1 := Finset.mem_range.mp j.2
    have hjN : j.1 + 1 < N := by omega
    it * (ops.γ ⟨2 * j.1 + 1, by omega⟩ * ops.γ ⟨2 * j.1 + 2, by omega⟩)

/-- An operator `γ ⟨0, _⟩` commutes with a product `γ_a * γ_b` if `⟨0, _⟩ ≠ a` and `⟨0, _⟩ ≠ b`. -/
lemma gamma_comm_product {A : Type*} [Ring A] {N : ℕ} (hN : 0 < N)
    (ops : MajoranaOperators N A) (a b : Fin (2 * N))
    (ha : (⟨0, by omega⟩ : Fin (2 * N)) ≠ a) (hb : (⟨0, by omega⟩ : Fin (2 * N)) ≠ b) :
    ops.γ ⟨0, by omega⟩ * (ops.γ a * ops.γ b) = (ops.γ a * ops.γ b) * ops.γ ⟨0, by omega⟩ := by
  exact gamma_comm_product_of_avoids ops _ a b ha hb

/-- **Left Boundary Majorana Zero Mode Theorem**:

The uncoupled boundary Majorana mode `γ₀` strictly commutes with the sweet-spot
Hamiltonian: `[H_sweet, γ₀] = 0`. -/
theorem left_majorana_zero_mode {A : Type*} [CommRing A] {N : ℕ} (hN : 0 < N)
    (ops : MajoranaOperators N A) (it : A) :
    commutator (sweetSpotHamiltonian ops it) (ops.γ ⟨0, by omega⟩) = 0 := by
  unfold sweetSpotHamiltonian commutator
  rw [Finset.sum_mul, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl ?_
  intro ⟨j, hj_mem⟩ _
  have hj : j < N - 1 := Finset.mem_range.mp hj_mem
  have ha : (⟨0, by omega⟩ : Fin (2 * N)) ≠ ⟨2 * j + 1, by omega⟩ := by
    intro h; have h_val := congrArg Fin.val h; dsimp at h_val; omega
  have hb : (⟨0, by omega⟩ : Fin (2 * N)) ≠ ⟨2 * j + 2, by omega⟩ := by
    intro h; have h_val := congrArg Fin.val h; dsimp at h_val; omega
  have h_comm := gamma_comm_product hN ops ⟨2 * j + 1, by omega⟩ ⟨2 * j + 2, by omega⟩ ha hb
  calc it * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩) * ops.γ ⟨0, _⟩
    _ = it * ((ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩) * ops.γ ⟨0, _⟩) := by rw [mul_assoc]
    _ = it * (ops.γ ⟨0, _⟩ * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩)) := by rw [h_comm]
    _ = ops.γ ⟨0, _⟩ * (it * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩)) := by ring

/-- An operator `γ ⟨2 * N - 1, _⟩` commutes with a product `γ_a * γ_b` if `⟨2 * N - 1, _⟩ ≠ a` and `⟨2 * N - 1, _⟩ ≠ b`. -/
lemma gamma_right_comm_product {A : Type*} [Ring A] {N : ℕ} (hN : 0 < N)
    (ops : MajoranaOperators N A) (a b : Fin (2 * N))
    (ha : (⟨2 * N - 1, by omega⟩ : Fin (2 * N)) ≠ a)
    (hb : (⟨2 * N - 1, by omega⟩ : Fin (2 * N)) ≠ b) :
    ops.γ ⟨2 * N - 1, by omega⟩ * (ops.γ a * ops.γ b) = (ops.γ a * ops.γ b) * ops.γ ⟨2 * N - 1, by omega⟩ := by
  exact gamma_comm_product_of_avoids ops _ a b ha hb

/-- **Right Boundary Majorana Zero Mode Theorem**:

The uncoupled right boundary Majorana mode `γ₂ₙ₋₁` strictly commutes with the sweet-spot
Hamiltonian: `[H_sweet, γ₂ₙ₋₁] = 0`. -/
theorem right_majorana_zero_mode {A : Type*} [CommRing A] {N : ℕ} (hN : 0 < N)
    (ops : MajoranaOperators N A) (it : A) :
    commutator (sweetSpotHamiltonian ops it) (ops.γ ⟨2 * N - 1, by omega⟩) = 0 := by
  unfold sweetSpotHamiltonian commutator
  rw [Finset.sum_mul, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl ?_
  intro ⟨j, hj_mem⟩ _
  have hj : j < N - 1 := Finset.mem_range.mp hj_mem
  have ha : (⟨2 * N - 1, by omega⟩ : Fin (2 * N)) ≠ ⟨2 * j + 1, by omega⟩ := by
    intro h; have h_val := congrArg Fin.val h; dsimp at h_val; omega
  have hb : (⟨2 * N - 1, by omega⟩ : Fin (2 * N)) ≠ ⟨2 * j + 2, by omega⟩ := by
    intro h; have h_val := congrArg Fin.val h; dsimp at h_val; omega
  have h_comm := gamma_right_comm_product hN ops ⟨2 * j + 1, by omega⟩ ⟨2 * j + 2, by omega⟩ ha hb
  calc it * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩) * ops.γ ⟨2 * N - 1, _⟩
    _ = it * ((ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩) * ops.γ ⟨2 * N - 1, _⟩) := by rw [mul_assoc]
    _ = it * (ops.γ ⟨2 * N - 1, _⟩ * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩)) := by rw [h_comm]
    _ = ops.γ ⟨2 * N - 1, _⟩ * (it * (ops.γ ⟨2 * j + 1, _⟩ * ops.γ ⟨2 * j + 2, _⟩)) := by ring

/-- Non-local Dirac fermion creation operator from boundary Majoranas. -/
noncomputable def boundaryDiracFermion {A : Type*} [Ring A] {N : ℕ} (hN : 0 < N)
    (ops : MajoranaOperators N A) (inv_2 I_complex : A) : A :=
  inv_2 * (ops.γ ⟨0, by omega⟩ + I_complex * ops.γ ⟨2 * N - 1, by omega⟩)

/-! ## Non-Abelian Majorana Braiding Operators -/

/-- Majorana Clifford operators with normalization `γ_i² = 1`. -/
structure MajoranaCliffordOperators (N : ℕ) (A : Type*) [Ring A] extends MajoranaOperators N A where
  h_sq : ∀ i, γ i * γ i = 1

/-- Elementary Majorana braid generator: `U_ij = inv_sqrt2 * (1 + γ_i * γ_j)`. -/
def braidOperator {A : Type*} [Ring A] {N : ℕ} (inv_sqrt2 : A)
    (ops : MajoranaCliffordOperators N A) (i j : Fin (2 * N)) : A :=
  inv_sqrt2 * (1 + ops.γ i * ops.γ j)

/-- Scalar parameters satisfying the normalization used by the braid inverse
law. -/
def braidNormalizationLocus {A : Type*} [Ring A] : Set A :=
  {r | r * r + r * r = 1}

/-- The normalization domain is closed in a `T₁` topological ring. -/
theorem braidNormalizationLocus_isClosed {A : Type*} [Ring A]
    [TopologicalSpace A] [ContinuousMul A] [ContinuousAdd A] [T1Space A] :
    IsClosed (braidNormalizationLocus (A := A)) := by
  change IsClosed {r : A | r * r + r * r = 1}
  have hcont : Continuous (fun r : A => r * r + r * r) := by
    exact (continuous_id.mul continuous_id).add
      (continuous_id.mul continuous_id)
  exact IsClosed.preimage hcont isClosed_singleton

/-- The physical real normalization `1 / √2` is a genuine point of the
normalization locus. -/
theorem real_mem_braidNormalizationLocus :
    (1 / Real.sqrt 2 : ℝ) ∈ braidNormalizationLocus := by
  change (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) +
      (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsq : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hs]
  nlinarith

/-- Over the reals, the normalization locus consists of exactly the two
possible signs of `1 / √2`. -/
theorem real_braidNormalizationLocus_eq_two_points :
    braidNormalizationLocus (A := ℝ) =
      ({(1 / Real.sqrt 2 : ℝ), -(1 / Real.sqrt 2 : ℝ)} : Set ℝ) := by
  ext r
  constructor
  · intro hr
    change r * r + r * r = 1 at hr
    have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
    have hsq : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
      rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have htarget : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) =
        (1 / 2 : ℝ) := by
      field_simp [hs]
      nlinarith
    have hrhalf : r * r = (1 / 2 : ℝ) := by nlinarith
    have heq : r * r = (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) := by
      rw [hrhalf, htarget]
    rcases (mul_self_eq_mul_self_iff.mp heq) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hr
    rcases hr with (rfl | rfl)
    · exact real_mem_braidNormalizationLocus
    · change (-(1 / Real.sqrt 2 : ℝ)) * (-(1 / Real.sqrt 2 : ℝ)) +
        (-(1 / Real.sqrt 2 : ℝ)) * (-(1 / Real.sqrt 2 : ℝ)) = 1
      have h := real_mem_braidNormalizationLocus
      change (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) +
        (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 at h
      nlinarith

/-- The real normalization locus is compact, since it is a two-point set. -/
theorem real_braidNormalizationLocus_isCompact :
    IsCompact (braidNormalizationLocus (A := ℝ)) := by
  rw [real_braidNormalizationLocus_eq_two_points]
  exact (Set.Finite.insert _ (Set.finite_singleton _)).isCompact

/-- The braid family is continuous in its scalar parameter whenever the
ambient multiplication is continuous. -/
theorem continuous_braidOperator {A : Type*} [Ring A] [TopologicalSpace A]
    [ContinuousMul A] {N : ℕ} (ops : MajoranaCliffordOperators N A)
    (i j : Fin (2 * N)) :
    Continuous (fun r : A => braidOperator r ops i j) := by
  unfold braidOperator
  exact continuous_id.mul continuous_const

/-- The commutator of two braid generators varies continuously with the
scalar parameter. -/
theorem continuous_braid_commutator {A : Type*} [Ring A] [TopologicalSpace A]
    [ContinuousMul A] [ContinuousSub A] {N : ℕ}
    (ops : MajoranaCliffordOperators N A)
    (i1 i2 i3 : Fin (2 * N)) :
    Continuous (fun r : A =>
      braidOperator r ops i1 i2 * braidOperator r ops i2 i3 -
        braidOperator r ops i2 i3 * braidOperator r ops i1 i2) := by
  exact (continuous_braidOperator ops i1 i2).mul
      (continuous_braidOperator ops i2 i3) |>.sub
    ((continuous_braidOperator ops i2 i3).mul
      (continuous_braidOperator ops i1 i2))

/-- The real braid family has a compact image when its scalar parameter is
restricted to the normalized locus. -/
theorem real_braidOperator_image_isCompact {N : ℕ}
    (ops : MajoranaCliffordOperators N ℝ) (i j : Fin (2 * N)) :
    IsCompact ((fun r : ℝ => braidOperator r ops i j) ''
      braidNormalizationLocus (A := ℝ)) := by
  exact real_braidNormalizationLocus_isCompact.image
    (continuous_braidOperator ops i j)

/-- The corresponding commutator values also form a compact real image on the
normalized scalar domain. -/
theorem real_braid_commutator_image_isCompact {N : ℕ}
    (ops : MajoranaCliffordOperators N ℝ)
    (i1 i2 i3 : Fin (2 * N)) :
    IsCompact ((fun r : ℝ =>
      braidOperator r ops i1 i2 * braidOperator r ops i2 i3 -
        braidOperator r ops i2 i3 * braidOperator r ops i1 i2) ''
      braidNormalizationLocus (A := ℝ)) := by
  exact real_braidNormalizationLocus_isCompact.image
    (continuous_braid_commutator ops i1 i2 i3)

/-- **Non-Abelian Braiding Commutator Theorem**:

For distinct Majorana modes `γ₁`, `γ₂`, `γ₃`, the elementary exchange operators
`U₁₂` and `U₂₃` do not commute:
`U₁₂ * U₂₃ - U₂₃ * U₁₂ = (inv_sqrt2 * inv_sqrt2 * 2) • (γ₁ * γ₃)`.

When `inv_sqrt2 = 1 / √2`, the scalar factor is `1`, yielding
`[U₁₂, U₂₃] = γ₁ * γ₃`.  Non-vanishing requires a separate hypothesis on
the chosen representation. -/
theorem braid_non_abelian_commutator {A : Type*} [Ring A] {N : ℕ}
    (inv_sqrt2 : A) (h_comm : ∀ x : A, inv_sqrt2 * x = x * inv_sqrt2)
    (ops : MajoranaCliffordOperators N A)
    (i1 i2 i3 : Fin (2 * N))
    (h23 : i2 ≠ i3) (h21 : i2 ≠ i1) (h31 : i3 ≠ i1) :
    braidOperator inv_sqrt2 ops i1 i2 * braidOperator inv_sqrt2 ops i2 i3 -
    braidOperator inv_sqrt2 ops i2 i3 * braidOperator inv_sqrt2 ops i1 i2 =
    (inv_sqrt2 * inv_sqrt2 + inv_sqrt2 * inv_sqrt2) * (ops.γ i1 * ops.γ i3) := by
  unfold braidOperator
  have h31_anti : ops.γ i3 * ops.γ i1 = - (ops.γ i1 * ops.γ i3) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho i3 i1 h31)
  have h21_anti : ops.γ i2 * ops.γ i1 = - (ops.γ i1 * ops.γ i2) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho i2 i1 h21)
  have h23_anti : ops.γ i2 * ops.γ i3 = - (ops.γ i3 * ops.γ i2) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho i2 i3 h23)
  have h22_sq : ops.γ i2 * ops.γ i2 = 1 := ops.h_sq i2

  have h_prod1 : (1 + ops.γ i1 * ops.γ i2) * (1 + ops.γ i2 * ops.γ i3) =
      1 + ops.γ i1 * ops.γ i2 + ops.γ i2 * ops.γ i3 + ops.γ i1 * ops.γ i3 := by
    calc (1 + ops.γ i1 * ops.γ i2) * (1 + ops.γ i2 * ops.γ i3)
      _ = 1 + ops.γ i2 * ops.γ i3 + ops.γ i1 * ops.γ i2 + ops.γ i1 * (ops.γ i2 * ops.γ i2) * ops.γ i3 := by noncomm_ring
      _ = 1 + ops.γ i1 * ops.γ i2 + ops.γ i2 * ops.γ i3 + ops.γ i1 * ops.γ i3 := by rw [h22_sq]; noncomm_ring

  have h_mid : ops.γ i2 * ops.γ i3 * (ops.γ i1 * ops.γ i2) = - (ops.γ i1 * ops.γ i3) := by
    calc ops.γ i2 * ops.γ i3 * (ops.γ i1 * ops.γ i2)
      _ = ops.γ i2 * (ops.γ i3 * ops.γ i1) * ops.γ i2 := by noncomm_ring
      _ = ops.γ i2 * (- (ops.γ i1 * ops.γ i3)) * ops.γ i2 := by rw [h31_anti]
      _ = - (ops.γ i2 * ops.γ i1) * ops.γ i3 * ops.γ i2 := by noncomm_ring
      _ = - (- (ops.γ i1 * ops.γ i2)) * ops.γ i3 * ops.γ i2 := by rw [h21_anti]
      _ = ops.γ i1 * (ops.γ i2 * ops.γ i3 * ops.γ i2) := by noncomm_ring
      _ = ops.γ i1 * (- (ops.γ i3 * ops.γ i2) * ops.γ i2) := by rw [← h23_anti]
      _ = ops.γ i1 * (- (ops.γ i3 * (ops.γ i2 * ops.γ i2))) := by noncomm_ring
      _ = ops.γ i1 * (- (ops.γ i3 * 1)) := by rw [h22_sq]
      _ = - (ops.γ i1 * ops.γ i3) := by noncomm_ring

  have h_prod2 : (1 + ops.γ i2 * ops.γ i3) * (1 + ops.γ i1 * ops.γ i2) =
      1 + ops.γ i1 * ops.γ i2 + ops.γ i2 * ops.γ i3 - ops.γ i1 * ops.γ i3 := by
    calc (1 + ops.γ i2 * ops.γ i3) * (1 + ops.γ i1 * ops.γ i2)
      _ = 1 + ops.γ i1 * ops.γ i2 + ops.γ i2 * ops.γ i3 + ops.γ i2 * ops.γ i3 * (ops.γ i1 * ops.γ i2) := by noncomm_ring
      _ = 1 + ops.γ i1 * ops.γ i2 + ops.γ i2 * ops.γ i3 - ops.γ i1 * ops.γ i3 := by rw [h_mid]; noncomm_ring

  have h_scalar : ∀ A_op B_op : A, inv_sqrt2 * A_op * (inv_sqrt2 * B_op) = (inv_sqrt2 * inv_sqrt2) * (A_op * B_op) := by
    intro A_op B_op
    calc inv_sqrt2 * A_op * (inv_sqrt2 * B_op)
      _ = inv_sqrt2 * (A_op * inv_sqrt2) * B_op := by simp only [mul_assoc]
      _ = inv_sqrt2 * (inv_sqrt2 * A_op) * B_op := by rw [← h_comm A_op]
      _ = (inv_sqrt2 * inv_sqrt2) * (A_op * B_op) := by noncomm_ring

  rw [h_scalar (1 + ops.γ i1 * ops.γ i2) (1 + ops.γ i2 * ops.γ i3)]
  rw [h_scalar (1 + ops.γ i2 * ops.γ i3) (1 + ops.γ i1 * ops.γ i2)]
  rw [h_prod1, h_prod2]
  noncomm_ring

/-- Non-vanishing of the braid commutator once a representation supplies a
nonzero product of the two outer Majorana modes.

The preceding formula is representation-independent.  This corollary keeps
the required non-vanishing witness explicit instead of silently asserting it
for every abstract `MajoranaCliffordOperators` datum. -/
theorem braid_commutator_ne_zero_of_outer_product_ne_zero
    {A : Type*} [Ring A] {N : ℕ}
    (r : A) (h_comm : ∀ x : A, r * x = x * r)
    (h_norm : r * r + r * r = 1)
    (ops : MajoranaCliffordOperators N A)
    (i1 i2 i3 : Fin (2 * N))
    (h23 : i2 ≠ i3) (h21 : i2 ≠ i1) (h31 : i3 ≠ i1)
    (h_outer : ops.γ i1 * ops.γ i3 ≠ 0) :
    braidOperator r ops i1 i2 * braidOperator r ops i2 i3 -
      braidOperator r ops i2 i3 * braidOperator r ops i1 i2 ≠ 0 := by
  rw [braid_non_abelian_commutator r h_comm ops i1 i2 i3 h23 h21 h31]
  simpa [h_norm] using h_outer

/-- Real normalized braids have exactly the outer-Majorana commutator.

Membership in `braidNormalizationLocus` supplies the scalar normalization;
the only representation-specific input remains the explicit nonzero outer
product witness. -/
theorem real_braid_commutator_eq_outer_product
    {N : ℕ} (r : ℝ) (hr : r ∈ braidNormalizationLocus (A := ℝ))
    (ops : MajoranaCliffordOperators N ℝ)
    (i1 i2 i3 : Fin (2 * N))
    (h23 : i2 ≠ i3) (h21 : i2 ≠ i1) (h31 : i3 ≠ i1) :
    braidOperator r ops i1 i2 * braidOperator r ops i2 i3 -
      braidOperator r ops i2 i3 * braidOperator r ops i1 i2 =
      ops.γ i1 * ops.γ i3 := by
  change r * r + r * r = 1 at hr
  rw [braid_non_abelian_commutator r (fun x => mul_comm r x) ops
    i1 i2 i3 h23 h21 h31]
  rw [hr]
  simp

/-- The real normalized commutator is nonzero whenever the chosen Majorana
representation makes the outer product nonzero. -/
theorem real_braid_commutator_ne_zero
    {N : ℕ} (r : ℝ) (hr : r ∈ braidNormalizationLocus (A := ℝ))
    (ops : MajoranaCliffordOperators N ℝ)
    (i1 i2 i3 : Fin (2 * N))
    (h23 : i2 ≠ i3) (h21 : i2 ≠ i1) (h31 : i3 ≠ i1)
    (h_outer : ops.γ i1 * ops.γ i3 ≠ 0) :
    braidOperator r ops i1 i2 * braidOperator r ops i2 i3 -
      braidOperator r ops i2 i3 * braidOperator r ops i1 i2 ≠ 0 := by
  rw [real_braid_commutator_eq_outer_product r hr ops i1 i2 i3 h23 h21 h31]
  exact h_outer

/-- **Majorana Braid Inverse Law**:

For distinct Majorana indices `i ≠ j`, under the scalar normalization `r * r + r * r = 1`
(where `r = 1 / √2`), the braid generator `U_ij` satisfies `U_ij * U_ji = 1` and `U_ji * U_ij = 1`. -/
theorem braidOperator_inverse_law {A : Type*} [Ring A] {N : ℕ}
    (r : A) (h_comm : ∀ x : A, r * x = x * r)
    (h_norm : r * r + r * r = 1)
    (ops : MajoranaCliffordOperators N A)
    (i j : Fin (2 * N)) (hji : j ≠ i) (hij : i ≠ j) :
    braidOperator r ops i j * braidOperator r ops j i = 1 ∧
    braidOperator r ops j i * braidOperator r ops i j = 1 := by
  have hji_anti : ops.γ j * ops.γ i = - (ops.γ i * ops.γ j) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho j i hji)
  have hij_anti : ops.γ i * ops.γ j = - (ops.γ j * ops.γ i) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho i j hij)
  have hii_sq : ops.γ i * ops.γ i = 1 := ops.h_sq i
  have hjj_sq : ops.γ j * ops.γ j = 1 := ops.h_sq j

  have h_scalar : ∀ X Y : A, r * X * (r * Y) = (r * r) * (X * Y) := by
    intro X Y
    calc r * X * (r * Y)
      _ = r * (X * r) * Y := by noncomm_ring
      _ = r * (r * X) * Y := by rw [← h_comm X]
      _ = (r * r) * (X * Y) := by noncomm_ring

  have h_prod1 : (1 + ops.γ i * ops.γ j) * (1 + ops.γ j * ops.γ i) = 1 + 1 := by
    calc (1 + ops.γ i * ops.γ j) * (1 + ops.γ j * ops.γ i)
      _ = 1 + ops.γ j * ops.γ i + ops.γ i * ops.γ j + ops.γ i * (ops.γ j * ops.γ j) * ops.γ i := by noncomm_ring
      _ = 1 + ops.γ j * ops.γ i + ops.γ i * ops.γ j + ops.γ i * 1 * ops.γ i := by rw [hjj_sq]
      _ = 1 + (- (ops.γ i * ops.γ j)) + ops.γ i * ops.γ j + (ops.γ i * ops.γ i) := by rw [hji_anti]; noncomm_ring
      _ = 1 + (- (ops.γ i * ops.γ j)) + ops.γ i * ops.γ j + 1 := by rw [hii_sq]
      _ = 1 + 1 := by abel

  have h_prod2 : (1 + ops.γ j * ops.γ i) * (1 + ops.γ i * ops.γ j) = 1 + 1 := by
    calc (1 + ops.γ j * ops.γ i) * (1 + ops.γ i * ops.γ j)
      _ = 1 + ops.γ i * ops.γ j + ops.γ j * ops.γ i + ops.γ j * (ops.γ i * ops.γ i) * ops.γ j := by noncomm_ring
      _ = 1 + ops.γ i * ops.γ j + ops.γ j * ops.γ i + ops.γ j * 1 * ops.γ j := by rw [hii_sq]
      _ = 1 + (- (ops.γ j * ops.γ i)) + ops.γ j * ops.γ i + (ops.γ j * ops.γ j) := by rw [hij_anti]; noncomm_ring
      _ = 1 + (- (ops.γ j * ops.γ i)) + ops.γ j * ops.γ i + 1 := by rw [hjj_sq]
      _ = 1 + 1 := by abel

  constructor
  · unfold braidOperator
    rw [h_scalar (1 + ops.γ i * ops.γ j) (1 + ops.γ j * ops.γ i)]
    rw [h_prod1]
    calc (r * r) * (1 + 1)
      _ = r * r + r * r := by noncomm_ring
      _ = 1 := h_norm
  · unfold braidOperator
    rw [h_scalar (1 + ops.γ j * ops.γ i) (1 + ops.γ i * ops.γ j)]
    rw [h_prod2]
    calc (r * r) * (1 + 1)
      _ = r * r + r * r := by noncomm_ring
      _ = 1 := h_norm

/-- Conjugation by a normalized braid exchanges the two Majorana modes.

This is the algebraic action law behind the braid operator: the inverse used
here is the one proved in `braidOperator_inverse_law`, and no representation
or analytic phase convention is hidden in the statement. -/
theorem braidOperator_conjugates_left {A : Type*} [Ring A] {N : ℕ}
    (r : A) (h_comm : ∀ x : A, r * x = x * r)
    (h_norm : r * r + r * r = 1)
    (ops : MajoranaCliffordOperators N A)
    (i j : Fin (2 * N)) (hji : j ≠ i) :
    braidOperator r ops i j * ops.γ i * braidOperator r ops j i = -ops.γ j := by
  have hji_anti : ops.γ j * ops.γ i = - (ops.γ i * ops.γ j) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho j i hji)
  have hii_sq : ops.γ i * ops.γ i = 1 := ops.h_sq i
  have hjj_sq : ops.γ j * ops.γ j = 1 := ops.h_sq j
  have h_scalar : ∀ X Y : A, r * X * (r * Y) = (r * r) * (X * Y) := by
    intro X Y
    calc r * X * (r * Y)
      _ = r * (X * r) * Y := by noncomm_ring
      _ = r * (r * X) * Y := by rw [← h_comm X]
      _ = (r * r) * (X * Y) := by noncomm_ring
  have h_inner :
      ((1 + ops.γ i * ops.γ j) * ops.γ i) *
          (1 + ops.γ j * ops.γ i) = - (ops.γ j + ops.γ j) := by
    have h_aba : ops.γ i * ops.γ j * ops.γ i = -ops.γ j := by
      calc
        ops.γ i * ops.γ j * ops.γ i =
            ops.γ i * (ops.γ j * ops.γ i) := by noncomm_ring
        _ = ops.γ i * (-(ops.γ i * ops.γ j)) := by rw [hji_anti]
        _ = -(ops.γ i * (ops.γ i * ops.γ j)) := by noncomm_ring
        _ = -ops.γ j := by
          rw [show ops.γ i * (ops.γ i * ops.γ j) =
            (ops.γ i * ops.γ i) * ops.γ j by noncomm_ring, hii_sq]
          simp
    have h_bba : ops.γ j * ops.γ j * ops.γ i = ops.γ i := by
      rw [hjj_sq]
      noncomm_ring
    calc
      ((1 + ops.γ i * ops.γ j) * ops.γ i) *
          (1 + ops.γ j * ops.γ i)
          = (ops.γ i + ops.γ i * ops.γ j * ops.γ i) *
              (1 + ops.γ j * ops.γ i) := by noncomm_ring
      _ = (ops.γ i - ops.γ j) * (1 + ops.γ j * ops.γ i) := by
            rw [h_aba]
            simp only [sub_eq_add_neg]
      _ = - (ops.γ j + ops.γ j) := by
            calc
              (ops.γ i - ops.γ j) * (1 + ops.γ j * ops.γ i) =
                  ops.γ i - ops.γ j + ops.γ i * ops.γ j * ops.γ i -
                    ops.γ j * ops.γ j * ops.γ i := by noncomm_ring
              _ = - (ops.γ j + ops.γ j) := by rw [h_aba, h_bba]; noncomm_ring
  calc
    r * (1 + ops.γ i * ops.γ j) * ops.γ i *
        (r * (1 + ops.γ j * ops.γ i)) =
        r * ((1 + ops.γ i * ops.γ j) * ops.γ i) *
          (r * (1 + ops.γ j * ops.γ i)) := by noncomm_ring
    _ = (r * r) * (((1 + ops.γ i * ops.γ j) * ops.γ i) *
        (1 + ops.γ j * ops.γ i)) :=
      h_scalar ((1 + ops.γ i * ops.γ j) * ops.γ i)
        (1 + ops.γ j * ops.γ i)
    _ = (r * r) * -(ops.γ j + ops.γ j) := by rw [h_inner]
    _ = -((r * r + r * r) * ops.γ j) := by noncomm_ring
    _ = -ops.γ j := by rw [h_norm]; noncomm_ring

/-- The companion exchange law: the second Majorana is transported to the
first one under the same normalized braid conjugation. -/
theorem braidOperator_conjugates_right {A : Type*} [Ring A] {N : ℕ}
    (r : A) (h_comm : ∀ x : A, r * x = x * r)
    (h_norm : r * r + r * r = 1)
    (ops : MajoranaCliffordOperators N A)
    (i j : Fin (2 * N)) (hji : j ≠ i) :
    braidOperator r ops i j * ops.γ j * braidOperator r ops j i = ops.γ i := by
  have hji_anti : ops.γ j * ops.γ i = - (ops.γ i * ops.γ j) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho j i hji)
  have hij : i ≠ j := Ne.symm hji
  have hij_anti : ops.γ i * ops.γ j = - (ops.γ j * ops.γ i) :=
    eq_neg_of_add_eq_zero_left (ops.h_ortho i j hij)
  have hii_sq : ops.γ i * ops.γ i = 1 := ops.h_sq i
  have hjj_sq : ops.γ j * ops.γ j = 1 := ops.h_sq j
  have h_scalar : ∀ X Y : A, r * X * (r * Y) = (r * r) * (X * Y) := by
    intro X Y
    calc r * X * (r * Y)
      _ = r * (X * r) * Y := by noncomm_ring
      _ = r * (r * X) * Y := by rw [← h_comm X]
      _ = (r * r) * (X * Y) := by noncomm_ring
  have h_bab : ops.γ j * ops.γ i * ops.γ j = -ops.γ i := by
    calc
      ops.γ j * ops.γ i * ops.γ j =
          ops.γ j * (ops.γ i * ops.γ j) := by noncomm_ring
      _ = ops.γ j * (-(ops.γ j * ops.γ i)) := by rw [hij_anti]
      _ = -(ops.γ j * (ops.γ j * ops.γ i)) := by noncomm_ring
      _ = -ops.γ i := by
        rw [show ops.γ j * (ops.γ j * ops.γ i) =
          (ops.γ j * ops.γ j) * ops.γ i by noncomm_ring, hjj_sq]
        simp
  have h_inner :
      ((1 + ops.γ i * ops.γ j) * ops.γ j) *
          (1 + ops.γ j * ops.γ i) = ops.γ i + ops.γ i := by
    have h_abb : ops.γ i * ops.γ j * ops.γ j = ops.γ i := by
      rw [show ops.γ i * ops.γ j * ops.γ j =
        ops.γ i * (ops.γ j * ops.γ j) by noncomm_ring, hjj_sq]
      simp
    have h_aba : ops.γ i * ops.γ j * ops.γ i = -ops.γ j := by
      calc
        ops.γ i * ops.γ j * ops.γ i =
            ops.γ i * (ops.γ j * ops.γ i) := by noncomm_ring
        _ = ops.γ i * (-(ops.γ i * ops.γ j)) := by rw [hji_anti]
        _ = -(ops.γ i * (ops.γ i * ops.γ j)) := by noncomm_ring
        _ = -ops.γ j := by
          rw [show ops.γ i * (ops.γ i * ops.γ j) =
            (ops.γ i * ops.γ i) * ops.γ j by noncomm_ring, hii_sq]
          simp
    have h_bba : ops.γ j * ops.γ j * ops.γ i = ops.γ i := by
      rw [hjj_sq]
      noncomm_ring
    calc
      ((1 + ops.γ i * ops.γ j) * ops.γ j) *
          (1 + ops.γ j * ops.γ i) =
          (ops.γ j + ops.γ i * ops.γ j * ops.γ j) *
            (1 + ops.γ j * ops.γ i) := by noncomm_ring
      _ = (ops.γ j + ops.γ i) * (1 + ops.γ j * ops.γ i) := by
            rw [h_abb]
      _ = ops.γ i + ops.γ i := by
            calc
              (ops.γ j + ops.γ i) * (1 + ops.γ j * ops.γ i) =
                  ops.γ j + ops.γ i + ops.γ j * ops.γ j * ops.γ i +
                    ops.γ i * ops.γ j * ops.γ i := by noncomm_ring
              _ = ops.γ i + ops.γ i := by rw [h_bba, h_aba]; abel
  calc
    r * (1 + ops.γ i * ops.γ j) * ops.γ j *
        (r * (1 + ops.γ j * ops.γ i)) =
        r * ((1 + ops.γ i * ops.γ j) * ops.γ j) *
          (r * (1 + ops.γ j * ops.γ i)) := by noncomm_ring
    _ = (r * r) * (((1 + ops.γ i * ops.γ j) * ops.γ j) *
        (1 + ops.γ j * ops.γ i)) :=
      h_scalar ((1 + ops.γ i * ops.γ j) * ops.γ j)
        (1 + ops.γ j * ops.γ i)
    _ = (r * r) * (ops.γ i + ops.γ i) := by rw [h_inner]
    _ = (r * r + r * r) * ops.γ i := by noncomm_ring
    _ = ops.γ i := by rw [h_norm]; simp


end InfoGeometry.Quantum.KitaevChain
