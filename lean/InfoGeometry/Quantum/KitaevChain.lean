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

open InfoGeometry.Quantum.RealMajoranaCategory
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
  is_skew : IsSkewSymmetric pairing

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

end InfoGeometry.Quantum.KitaevChain
