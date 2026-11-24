/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
import InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Grassmann–Pfaffian Syzygies, Lie's No. 503 Symplectic Assemblies, & Darboux Normal-Form Classes

Wave II formalization of Grassmann's *Ausdehnungslehre* (1862) differential/Pfaffian endmatter
(`hmath019-endmatter.pdf`, Editorial Notes 110–126 and Engel's Nos. 502–527):

1. **`GA₁₃` (`No. 512`, `p. 380`)**:
   Contraction syzygy `d w • (ι w * Z) = ι w * contractLeft d (ι w * Z)`, unit reduction over
   arbitrary commutative rings, and exact reduction of `ι w * Ω^n = 0` to `0`-indexed basis
   components when `b.repr w 0 ≠ 0`.
2. **`GA₁₄` (`Editorial Note 114, pp. 375–376`, Eq. `(5)`)**:
   Pfaffian systems of `h` equations `ω_κ = pfaffJetOneForm (U κ) α`, `Ω_κ = pfaffJetTwoForm (β κ) α`:
   any mixed product `∏ κ, ω_κ ^ ε_κ * Ω_κ ^ r_κ` with `n < ∑ κ, (ε κ + r κ)` vanishes over any
   commutative ring and module.
3. **`GA₁₅` (`No. 503` / Sophus Lie's Auxiliary Problem, `Note 110, p. 373`)**:
   Exact symplectic isotropic subspace bound `2 * finrank K W ≤ finrank K V` (`W ≤ B.orthogonal W`,
   equality iff Lagrangian `W = B.orthogonal W` when `B.IsRefl`), plus explicit nondegeneracy of
   `canonicalSymplecticForm K n` on `Fin (2 * n) → K`.
4. **`GA₁₆` (`Nos. 519, 522–527`, `pp. 384, 388–389`)**:
   Exact top power formula `(darbouxTwoForm e f)^n = n! • ιMulti (2*n) (interleaveVec e f)` and
   `(darbouxTwoForm e f)^(n + 1) = 0`, establishing both nonvanishing and termination of Grassmann's
   odd (contact `2n+1`) and even (Liouville `2n`) Darboux normal forms via `No. 511` and `No. 518`.
5. **Wave II 9-Node Causal Poset (`GrassmannWave2Archetype`) & Master Synthesis**.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra

/-! ## 1. Grassmann No. 512 Pfaffian Syzygy Reduction (`p. 380`) -/

section GrassmannNo512Syzygy

/-- **Grassmann No. 512 Contraction Syzygy (`p. 380`)**:
since `ι w * (ι w * Z) = 0`, applying any left contraction `d` gives
`d w • (ι w * Z) = ι w * contractLeft d (ι w * Z)`. -/
theorem grassmann_no512_contraction_syzygy {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (w : M) (Z : ExteriorAlgebra R M) (d : Module.Dual R M) :
    d w • (ExteriorAlgebra.ι R w * Z) =
      ExteriorAlgebra.ι R w *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
          (ExteriorAlgebra.ι R w * Z) := by
  have h0 : ExteriorAlgebra.ι R w * (ExteriorAlgebra.ι R w * Z) = 0 := by
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have h1 := congrArg (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  have hι0 : CliffordAlgebra.ι (0 : QuadraticForm R M) w = ExteriorAlgebra.ι R w := rfl
  rw [CliffordAlgebra.contractLeft_ι_mul, hι0, map_zero, sub_eq_zero] at h1
  exact h1

/-- Whenever `IsUnit (d w)`, vanishing of `ι w * Z` reduces equivalently to vanishing of its
contraction `contractLeft d (ι w * Z)`. -/
theorem grassmann_no512_unit_reduction {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {w : M} {d : Module.Dual R M} (hu : IsUnit (d w))
    (Z : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R w * Z = 0 ↔
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
        (ExteriorAlgebra.ι R w * Z) = 0 := by
  constructor
  · intro hz
    rw [hz, map_zero]
  · intro hc
    obtain ⟨u, hu'⟩ := hu
    have hsyz := grassmann_no512_contraction_syzygy w Z d
    rw [hc, mul_zero, ← hu', ← Units.smul_def] at hsyz
    have hinv := congrArg (u⁻¹ • ·) hsyz
    simpa [smul_smul] using hinv

private theorem contractLeft_ιMulti_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (d : Module.Dual K V) :
    ∀ {k : ℕ} (v : Fin k → V), (∀ i, d (v i) = 0) →
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d
        (ExteriorAlgebra.ιMulti K k v) = 0
  | 0, _, _ => by simp [CliffordAlgebra.contractLeft_one]
  | k + 1, v, hv => by
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (v 0) = ExteriorAlgebra.ι K (v 0) := rfl
    have hcm := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V)) d (v 0)
      (ExteriorAlgebra.ιMulti K k (Matrix.vecTail v))
    rw [hι0] at hcm
    rw [hcm, hv 0, zero_smul, zero_sub,
      contractLeft_ιMulti_zero d (Matrix.vecTail v) (fun i => hv i.succ), mul_zero, neg_zero]

private theorem contractLeft_dualBasis_zero_of_notMem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} (b : Module.Basis (Fin (m + 1)) K V)
    {s : Finset (Fin (m + 1))} (hs : (0 : Fin (m + 1)) ∉ s) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis 0)
        (b.ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl)
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis 0)
      (ExteriorAlgebra.ιMulti K s.card (fun i => b (g i))) = 0
  refine contractLeft_ιMulti_zero (b.dualBasis 0) (fun i => b (g i)) fun i => ?_
  have hmem : g i ∈ s :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.ofCard (s := s) rfl) (g i)).1 ⟨i, rfl⟩
  have hne : g i ≠ 0 := fun h => hs (h ▸ hmem)
  rw [b.dualBasis_apply_self, ite_eq_right hne]

private theorem basis_singleton_zero_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (b : Module.Basis (Fin (m + 1)) K V) :
    b.ExteriorAlgebra ({0} : Finset (Fin (m + 1))) = ExteriorAlgebra.ι K (b 0) := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton (0 : Fin (m + 1)))]
  let g := Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofCard (Finset.card_singleton (0 : Fin (m + 1))))
  have hg0 : g 0 = 0 := Finset.mem_singleton.mp
    ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩)
  change ExteriorAlgebra.ιMulti K 1 (fun i => b (g i)) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]

private theorem contractLeft_dualBasis_zero_of_mem {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} (b : Module.Basis (Fin (m + 1)) K V)
    {s : Finset (Fin (m + 1))} (hs : (0 : Fin (m + 1)) ∈ s) :
    ∃ u : Kˣ,
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis 0)
        (b.ExteriorAlgebra s) = (u : K) • b.ExteriorAlgebra (s.erase 0) := by
  have hd : Disjoint ({0} : Finset (Fin (m + 1))) (s.erase 0) :=
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase 0 s)
  let s0 := Set.powersetCard.ofCard (Finset.card_singleton (0 : Fin (m + 1)))
  let se := Set.powersetCard.ofCard (s := s.erase 0) rfl
  have hd' : Disjoint (s0 : Finset (Fin (m + 1))) (se : Finset (Fin (m + 1))) := hd
  have hmul := ExteriorAlgebra.basis_mul_of_disjoint b s0 se hd'
  have hunion : ({0} : Finset (Fin (m + 1))).disjUnion (s.erase 0) hd = s := by
    ext x
    simp only [Finset.mem_disjUnion, Finset.mem_singleton, Finset.mem_erase]
    by_cases hx : x = 0 <;> simp [hx, hs]
  let ε : ℤˣ := (Set.powersetCard.permOfDisjoint hd').sign
  let εK : Kˣ := Units.map (Int.castRingHom K).toMonoidHom ε
  have hmul' : ExteriorAlgebra.ι K (b 0) * b.ExteriorAlgebra (s.erase 0) =
      (εK : K) • b.ExteriorAlgebra s := by
    have hs1 : b.ExteriorAlgebra s0 = ExteriorAlgebra.ι K (b 0) := basis_singleton_zero_eq b
    have hs2 : b.ExteriorAlgebra se = b.ExteriorAlgebra (s.erase 0) := rfl
    have hs3 : b.ExteriorAlgebra (Set.powersetCard.disjUnion hd') = b.ExteriorAlgebra s :=
      congrArg b.ExteriorAlgebra hunion
    rw [hs1, hs2, hs3] at hmul
    rw [hmul]
    change (((ε : ℤ) : K) • b.ExteriorAlgebra s) = (ε : ℤ) • b.ExteriorAlgebra s
    exact Int.cast_smul_eq_zsmul K _ _
  have hbs : b.ExteriorAlgebra s =
      (εK⁻¹ : Kˣ) • (ExteriorAlgebra.ι K (b 0) * b.ExteriorAlgebra (s.erase 0)) := by
    rw [hmul', Units.smul_def, smul_smul, Units.inv_mul, one_smul]
  refine ⟨εK⁻¹, ?_⟩
  rw [hbs, Units.smul_def, LinearMap.map_smul]
  have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (b 0) = ExteriorAlgebra.ι K (b 0) := rfl
  have hcm := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V)) (b.dualBasis 0)
    (b 0) (b.ExteriorAlgebra (s.erase 0))
  rw [hι0] at hcm
  rw [hcm, b.dualBasis_apply_self, ite_eq_left rfl, one_smul,
    contractLeft_dualBasis_zero_of_notMem b (Finset.notMem_erase 0 s), mul_zero, sub_zero,
    ← Units.smul_def]

/-- Contraction by `b.dualBasis 0` annihilates `z` iff every basis coordinate of `z` containing `0`
vanishes (`Grassmann No. 512`). -/
theorem contractLeft_dualBasis_zero_eq_zero_iff {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} (b : Module.Basis (Fin (m + 1)) K V) (z : ExteriorAlgebra K V) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis 0) z = 0 ↔
      ∀ s : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∈ s → b.ExteriorAlgebra.repr z s = 0 := by
  have hz : z = ∑ s : Finset (Fin (m + 1)), b.ExteriorAlgebra.repr z s • b.ExteriorAlgebra s :=
    (b.ExteriorAlgebra.sum_repr z).symm
  constructor
  · intro hc s₀ hs₀
    classical
    have hcoeff : ∀ s : Finset (Fin (m + 1)),
        ∃ u : Kˣ, b.ExteriorAlgebra.coord (s₀.erase 0)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.dualBasis 0)
            (b.ExteriorAlgebra s)) =
          if s = s₀ then (u : K) else 0 := fun s => by
      by_cases hs : (0 : Fin (m + 1)) ∈ s
      · obtain ⟨u, hu⟩ := contractLeft_dualBasis_zero_of_mem b hs
        refine ⟨u, ?_⟩
        rw [hu, LinearMap.map_smul, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self,
          Finsupp.single_apply, smul_eq_mul]
        by_cases hst : s = s₀
        · subst hst
          simp
        · have hne : s.erase 0 ≠ s₀.erase 0 := by
            intro heq
            apply hst
            ext x
            by_cases hx : x = 0
            · simp [hx, hs, hs₀]
            · have := Finset.ext_iff.mp heq x
              simpa [Finset.mem_erase, hx] using this
          simp [hst, hne]
      · refine ⟨1, ?_⟩
        have hne : s ≠ s₀ := fun h => hs (h ▸ hs₀)
        rw [contractLeft_dualBasis_zero_of_notMem b hs, LinearMap.map_zero, ite_eq_right hne]
    choose u hu using hcoeff
    have hsum := congrArg (b.ExteriorAlgebra.coord (s₀.erase 0)) hc
    conv_lhs at hsum => rw [hz, map_sum, map_sum]
    simp only [map_smul, hu, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, LinearMap.map_zero] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right (u s₀).ne_zero
  · intro hzeros
    conv_lhs => rw [hz, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : (0 : Fin (m + 1)) ∈ s
    · rw [hzeros s hs, zero_smul, map_zero]
    · rw [map_smul, contractLeft_dualBasis_zero_of_notMem b hs, smul_zero]

/-- **Grassmann No. 512 Basis Coordinate Reduction (`p. 380`)**:
when `b.repr w 0 ≠ 0`, `ι K w * Ω^n = 0` iff every basis coordinate of `ι K w * Ω^n` containing
index `0` vanishes. -/
theorem grassmann_no512_basis_coord_reduction {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} (b : Module.Basis (Fin (m + 1)) K V) {w : V} (hw0 : b.repr w 0 ≠ 0)
    (Ω : ExteriorAlgebra K V) (n : ℕ) :
    ExteriorAlgebra.ι K w * Ω ^ n = 0 ↔
      ∀ s : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∈ s →
        b.ExteriorAlgebra.repr (ExteriorAlgebra.ι K w * Ω ^ n) s = 0 := by
  have hd : b.dualBasis 0 w = b.repr w 0 := b.dualBasis_apply 0 w
  have hu : IsUnit (b.dualBasis 0 w) := by
    rw [hd]
    exact IsUnit.mk0 _ hw0
  exact (grassmann_no512_unit_reduction hu (Ω ^ n)).trans
    (contractLeft_dualBasis_zero_eq_zero_iff b (ExteriorAlgebra.ι K w * Ω ^ n))

end GrassmannNo512Syzygy

/-! ## 2. Editorial Note 114: Systems of `h` Pfaffian Equations (`pp. 375–376`) -/

section Note114PfaffianSystems

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem one_mem_spanInjBlades_zero {n : ℕ} (α : Fin n → M) :
    (1 : ExteriorAlgebra R M) ∈ spanInjBlades (R := R) α 0 := by
  refine Submodule.subset_span ⟨1, Fin.elim0, fun a => a.elim0, ?_⟩
  rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]

private theorem mul_pfaffJetOneForm_mem_spanInjBlades {n k : ℕ} (u : Fin n → R) (α : Fin n → M)
    {z : ExteriorAlgebra R M} (hz : z ∈ spanInjBlades α k) :
    z * pfaffJetOneForm u α ∈ spanInjBlades α (k + 1) := by
  induction hz using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨pref, g, _, rfl⟩ := hw
    dsimp [pfaffJetOneForm]
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hk : ExteriorAlgebra.ιMulti R k (α ∘ g) ∈ ⋀[R]^k M :=
      ExteriorAlgebra.ιMulti_range R k ⟨α ∘ g, rfl⟩
    have hcomm := ι_mul_exteriorPower_comm (α j) hk
    have hswap : ExteriorAlgebra.ιMulti R k (α ∘ g) * ExteriorAlgebra.ι R (α j) =
        ((-1 : R) ^ k) • (ExteriorAlgebra.ι R (α j) * ExteriorAlgebra.ιMulti R k (α ∘ g)) := by
      have hs := congrArg (fun t => ((-1 : R) ^ k) • t) hcomm.symm
      simpa [smul_smul, ← mul_pow, neg_one_mul] using hs
    have hcons : ExteriorAlgebra.ι R (α j) * ExteriorAlgebra.ιMulti R k (α ∘ g) =
        ExteriorAlgebra.ιMulti R (k + 1) (α ∘ Fin.cons j g) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      rfl
    have hprod : (pref * ExteriorAlgebra.ιMulti R k (α ∘ g)) *
        (u j • ExteriorAlgebra.ι R (α j)) =
        ((u j * (-1 : R) ^ k) • pref) * ExteriorAlgebra.ιMulti R (k + 1) (α ∘ Fin.cons j g) := by
      rw [mul_smul_comm, mul_assoc, hswap, mul_smul_comm, smul_smul, smul_mul_assoc, hcons]
    rw [hprod]
    by_cases hinj : Function.Injective (Fin.cons j g)
    · exact Submodule.subset_span ⟨_, Fin.cons j g, hinj, rfl⟩
    · have hdep : ¬Function.Injective (α ∘ Fin.cons j g) := fun h =>
        hinj (Function.Injective.of_comp h)
      rw [ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hdep, mul_zero]
      exact Submodule.zero_mem _
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r ih

private theorem mul_pfaffJetTwoForm_mem_spanInjBlades_step {n k : ℕ} (β α : Fin n → M)
    {z : ExteriorAlgebra R M} (hz : z ∈ spanInjBlades α k) :
    z * pfaffJetTwoForm β α ∈ spanInjBlades α (k + 1) := by
  induction hz using Submodule.span_induction with
  | mem _ hw =>
    obtain ⟨pref, g, _, rfl⟩ := hw
    dsimp [pfaffJetTwoForm]
    rw [Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h2_mem : ExteriorAlgebra.ι R (β j) * ExteriorAlgebra.ι R (α j) ∈ ⋀[R]^2 M := by
      rw [ExteriorAlgebra.exteriorPower, pow_two]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    have hcomm_2 := exteriorPower_two_mul_comm h2_mem (ExteriorAlgebra.ιMulti R k (α ∘ g))
    have hcons : ExteriorAlgebra.ι R (α j) * ExteriorAlgebra.ιMulti R k (α ∘ g) =
        ExteriorAlgebra.ιMulti R (k + 1) (α ∘ Fin.cons j g) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      rfl
    have hprod : (pref * ExteriorAlgebra.ιMulti R k (α ∘ g)) *
        (ExteriorAlgebra.ι R (β j) * ExteriorAlgebra.ι R (α j)) =
        (pref * ExteriorAlgebra.ι R (β j)) *
          ExteriorAlgebra.ιMulti R (k + 1) (α ∘ Fin.cons j g) := by
      calc
        (pref * ExteriorAlgebra.ιMulti R k (α ∘ g)) *
            (ExteriorAlgebra.ι R (β j) * ExteriorAlgebra.ι R (α j))
            = pref * (ExteriorAlgebra.ιMulti R k (α ∘ g) *
                (ExteriorAlgebra.ι R (β j) * ExteriorAlgebra.ι R (α j))) := by simp only [mul_assoc]
        _ = pref * ((ExteriorAlgebra.ι R (β j) * ExteriorAlgebra.ι R (α j)) *
                ExteriorAlgebra.ιMulti R k (α ∘ g)) := by rw [← hcomm_2]
        _ = (pref * ExteriorAlgebra.ι R (β j)) *
              (ExteriorAlgebra.ι R (α j) * ExteriorAlgebra.ιMulti R k (α ∘ g)) := by
            simp only [mul_assoc]
        _ = (pref * ExteriorAlgebra.ι R (β j)) *
              ExteriorAlgebra.ιMulti R (k + 1) (α ∘ Fin.cons j g) := by rw [hcons]
    rw [hprod]
    by_cases hinj : Function.Injective (Fin.cons j g)
    · exact Submodule.subset_span ⟨_, Fin.cons j g, hinj, rfl⟩
    · have hdep : ¬Function.Injective (α ∘ Fin.cons j g) := fun h =>
        hinj (Function.Injective.of_comp h)
      rw [ExteriorAlgebra.ιMulti_eq_zero_of_not_inj hdep, mul_zero]
      exact Submodule.zero_mem _
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r ih

private theorem mul_pfaffJetOneForm_pow_mem_spanInjBlades {n k m : ℕ} (u : Fin n → R)
    (α : Fin n → M) {z : ExteriorAlgebra R M} (hz : z ∈ spanInjBlades α k) :
    z * (pfaffJetOneForm u α) ^ m ∈ spanInjBlades α (k + m) := by
  induction m generalizing k z with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', ← mul_assoc, show k + (m + 1) = (k + 1) + m by omega]
    exact ih (mul_pfaffJetOneForm_mem_spanInjBlades u α hz)

private theorem mul_pfaffJetTwoForm_pow_mem_spanInjBlades {n k m : ℕ} (β α : Fin n → M)
    {z : ExteriorAlgebra R M} (hz : z ∈ spanInjBlades α k) :
    z * (pfaffJetTwoForm β α) ^ m ∈ spanInjBlades α (k + m) := by
  induction m generalizing k z with
  | zero => simpa using hz
  | succ m ih =>
    rw [pow_succ', ← mul_assoc, show k + (m + 1) = (k + 1) + m by omega]
    exact ih (mul_pfaffJetTwoForm_mem_spanInjBlades_step β α hz)

private theorem spanInjBlades_eq_bot_of_lt {n m : ℕ} (α : Fin n → M) (hnm : n < m) :
    spanInjBlades (R := R) α m = ⊥ := by
  rw [eq_bot_iff, spanInjBlades, Submodule.span_le]
  rintro _ ⟨_, g, hg, rfl⟩
  exfalso
  exact absurd hg (Fintype.not_injective_of_card_lt g (by simpa [Fintype.card_fin] using hnm))

private theorem prod_pfaff_system_mem_spanInjBlades {n : ℕ} (α : Fin n → M) :
    ∀ {h k : ℕ} (U : Fin h → Fin n → R) (β : Fin h → Fin n → M) (ε r : Fin h → ℕ)
      {z : ExteriorAlgebra R M}, z ∈ spanInjBlades α k →
      z * (List.ofFn fun κ : Fin h =>
          (pfaffJetOneForm (U κ) α) ^ (ε κ) * (pfaffJetTwoForm (β κ) α) ^ (r κ)).prod ∈
        spanInjBlades α (k + ∑ κ : Fin h, (ε κ + r κ))
  | 0, k, _, _, _, _, z, hz => by
    simp [hz]
  | h + 1, k, U, β, ε, r, z, hz => by
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc, Fin.sum_univ_succ]
    have hstep1 : z * ((pfaffJetOneForm (U 0) α) ^ (ε 0) * (pfaffJetTwoForm (β 0) α) ^ (r 0)) ∈
        spanInjBlades α (k + (ε 0 + r 0)) := by
      rw [← mul_assoc, ← add_assoc]
      exact mul_pfaffJetTwoForm_pow_mem_spanInjBlades (β 0) α
        (mul_pfaffJetOneForm_pow_mem_spanInjBlades (U 0) α hz)
    have htail := prod_pfaff_system_mem_spanInjBlades α (fun κ => U κ.succ)
      (fun κ => β κ.succ) (fun κ => ε κ.succ) (fun κ => r κ.succ) hstep1
    rwa [← add_assoc]

/-- **Editorial Note 114 (`pp. 375–376`, Eq. `(5)`) — Pfaffian Systems**:
for any `h` Pfaffian forms `ω_κ = pfaffJetOneForm (U κ) α` and `Ω_κ = pfaffJetTwoForm (β κ) α`
sharing differentials `α : Fin n → M` over ANY `[CommRing R]`, every ordered product with total
exponent `n < ∑ κ, (ε κ + r κ)` vanishes identically. -/
theorem note114_pfaff_system_vanishing {n h : ℕ} (α : Fin n → M) (U : Fin h → Fin n → R)
    (β : Fin h → Fin n → M) (ε r : Fin h → ℕ)
    (hsum : n < ∑ κ : Fin h, (ε κ + r κ)) :
    (List.ofFn fun κ : Fin h =>
        (pfaffJetOneForm (U κ) α) ^ (ε κ) * (pfaffJetTwoForm (β κ) α) ^ (r κ)).prod = 0 := by
  have hmem := prod_pfaff_system_mem_spanInjBlades α U β ε r (one_mem_spanInjBlades_zero (R := R) α)
  rw [one_mul, zero_add, spanInjBlades_eq_bot_of_lt α hsum] at hmem
  exact (Submodule.mem_bot R).mp hmem

end Note114PfaffianSystems

/-! ## 3. Grassmann No. 503 / Sophus Lie's Symplectic Isotropic Bound (`Note 110, p. 373`) -/

section LieNo503Symplectic

/-- **Grassmann No. 503 / Sophus Lie's Auxiliary Problem (`Note 110, p. 373`)**:
every isotropic subspace `W` of a finite-dimensional space `(V, B)` with nondegenerate bilinear
form `B` satisfies `W ≤ B.orthogonal W`, `2 * finrank K W ≤ finrank K V`, and (when `B.IsRefl`)
achieves half dimension iff `W` is maximally isotropic (Lagrangian: `W = B.orthogonal W`). -/
theorem lie_no503_isotropic_finrank_bound {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hiso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    W ≤ B.orthogonal W ∧
      2 * Module.finrank K W ≤ Module.finrank K V ∧
      (B.IsRefl → (2 * Module.finrank K W = Module.finrank K V ↔ W = B.orthogonal W)) := by
  have hle : W ≤ B.orthogonal W := fun x hx =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun y hy => hiso y hy x hx
  have hmono : Module.finrank K W ≤ Module.finrank K (B.orthogonal W) :=
    Submodule.finrank_mono hle
  have horth : Module.finrank K (B.orthogonal W) = Module.finrank K V - Module.finrank K W :=
    B.finrank_orthogonal hB W
  have hWle : Module.finrank K W ≤ Module.finrank K V := Submodule.finrank_le W
  have hbound : 2 * Module.finrank K W ≤ Module.finrank K V := by
    omega
  refine ⟨hle, hbound, fun _ => ?_⟩
  constructor
  · intro heq
    have hfin_eq : Module.finrank K W = Module.finrank K (B.orthogonal W) := by omega
    exact Submodule.eq_of_le_of_finrank_eq hle hfin_eq
  · intro heq
    have hfin_eq : Module.finrank K W = Module.finrank K (B.orthogonal W) := by rw [← heq]
    omega

/-- Canonical Darboux symplectic form `∑ i, (u_{2i} v_{2i+1} - u_{2i+1} v_{2i})` on `K^{2n}`. -/
def canonicalSymplecticForm (K : Type*) [Field K] (n : ℕ) :
    LinearMap.BilinForm K (Fin (2 * n) → K) :=
  LinearMap.mk₂ K
    (fun u v => ∑ i : Fin n,
      (u ⟨2 * i.val, by omega⟩ * v ⟨2 * i.val + 1, by omega⟩ -
       u ⟨2 * i.val + 1, by omega⟩ * v ⟨2 * i.val, by omega⟩))
    (fun u₁ u₂ v => by
      dsimp
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [add_mul]
      abel)
    (fun c u v => by
      dsimp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_sub]
      simp only [mul_assoc])
    (fun u v₁ v₂ => by
      dsimp
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mul_add]
      abel)
    (fun c u v => by
      dsimp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_sub, mul_left_comm _ c, mul_left_comm _ c])

theorem canonicalSymplecticForm_skew (K : Type*) [Field K] (n : ℕ)
    (u v : Fin (2 * n) → K) :
    canonicalSymplecticForm K n u v = -canonicalSymplecticForm K n v u := by
  dsimp [canonicalSymplecticForm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem canonicalSymplecticForm_nondegenerate (K : Type*) [Field K] (n : ℕ) :
    (canonicalSymplecticForm K n).Nondegenerate := by
  have hleft : (canonicalSymplecticForm K n).SeparatingLeft := by
    intro u hu
    ext k
    simp only [Pi.zero_apply]
    have hk_even : ∀ i : Fin n, u ⟨2 * i.val, by omega⟩ = 0 := fun i => by
      have hv := hu (fun m : Fin (2 * n) => if m.val = 2 * i.val + 1 then (1 : K) else 0)
      dsimp [canonicalSymplecticForm] at hv
      have hsingle : ∀ j : Fin n,
          (u ⟨2 * j.val, by omega⟩ * (if 2 * j.val + 1 = 2 * i.val + 1 then (1 : K) else 0) -
           u ⟨2 * j.val + 1, by omega⟩ * (if 2 * j.val = 2 * i.val + 1 then (1 : K) else 0)) =
            if j = i then u ⟨2 * i.val, by omega⟩ else 0 := fun j => by
        by_cases hj : j = i
        · subst hj
          simp
        · have hji : j.val ≠ i.val := Fin.val_ne_of_ne hj
          have h2 : 2 * j.val ≠ 2 * i.val + 1 := by omega
          simp [hj, hji, h2]
      simp_rw [hsingle, Finset.sum_ite_eq'] at hv
      simpa using hv
    have hk_odd : ∀ i : Fin n, u ⟨2 * i.val + 1, by omega⟩ = 0 := fun i => by
      have hv := hu (fun m : Fin (2 * n) => if m.val = 2 * i.val then (1 : K) else 0)
      dsimp [canonicalSymplecticForm] at hv
      have hsingle : ∀ j : Fin n,
          (u ⟨2 * j.val, by omega⟩ * (if 2 * j.val + 1 = 2 * i.val then (1 : K) else 0) -
           u ⟨2 * j.val + 1, by omega⟩ * (if 2 * j.val = 2 * i.val then (1 : K) else 0)) =
            if j = i then -u ⟨2 * i.val + 1, by omega⟩ else 0 := fun j => by
        by_cases hj : j = i
        · subst hj
          simp
        · have h1 : 2 * j.val + 1 ≠ 2 * i.val := by omega
          have hji : j.val ≠ i.val := Fin.val_ne_of_ne hj
          simp [hj, h1, hji]
      simp_rw [hsingle, Finset.sum_ite_eq'] at hv
      simp only [Finset.mem_univ, ite_true] at hv
      exact neg_eq_zero.mp hv
    rcases Nat.even_or_odd k.val with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hqi : q < n := by omega
      have hkq : k = ⟨2 * q, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hkq]
      exact hk_even ⟨q, hqi⟩
    · have hqi : q < n := by omega
      have hkq : k = ⟨2 * q + 1, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hkq]
      exact hk_odd ⟨q, hqi⟩
  refine ⟨hleft, fun v hv => hleft v fun u => ?_⟩
  rw [canonicalSymplecticForm_skew]
  exact neg_eq_zero.mpr (hv u)

/-- Applied to Grassmann's symplectic Pfaff phase space `K^{2n}`, any integrating isotropic
subspace `W` has `finrank K W ≤ n` and `n ≤ 2 * n - finrank K W`. -/
theorem lie_no503_canonical_symplectic_assembly (K : Type*) [Field K] (n : ℕ)
    (W : Submodule K (Fin (2 * n) → K))
    (hiso : ∀ x ∈ W, ∀ y ∈ W, canonicalSymplecticForm K n x y = 0) :
    Module.finrank K W ≤ n ∧
      n ≤ 2 * n - Module.finrank K W ∧
      (2 * Module.finrank K W = 2 * n ↔
        W = (canonicalSymplecticForm K n).orthogonal W) := by
  have hmain := lie_no503_isotropic_finrank_bound (canonicalSymplecticForm K n)
    (canonicalSymplecticForm_nondegenerate K n) W hiso
  have hfin : Module.finrank K (Fin (2 * n) → K) = 2 * n := by simp
  have hrefl : (canonicalSymplecticForm K n).IsRefl := fun u v huv => by
    rw [canonicalSymplecticForm_skew, huv, neg_zero]
  rw [hfin] at hmain
  refine ⟨by omega, by omega, hmain.2.2 hrefl⟩

end LieNo503Symplectic

/-! ## 4. Grassmann Nos. 519 & 522–527 Darboux Odd/Even Normal-Form Class Dichotomy (`pp. 384–389`) -/

section DarbouxNormalFormDichotomy

private theorem commute_sq_zero_add_pow {A : Type*} [Ring A] {a b : A}
    (hcomm : Commute a b) (ha : a * a = 0) (d : ℕ) :
    (a + b) ^ (d + 1) = b ^ (d + 1) + (d + 1) • (a * b ^ d) := by
  induction d with
  | zero =>
    simp [add_comm]
  | succ d ih =>
    rw [pow_succ (a + b) (d + 1), ih, add_mul, mul_add, mul_add, smul_mul_assoc,
      smul_mul_assoc]
    have h1 : b ^ (d + 1) * a = a * b ^ (d + 1) := (hcomm.pow_right (d + 1)).symm.eq
    have h2 : a * b ^ d * a = 0 := by
      calc
        a * b ^ d * a = a * (b ^ d * a) := by rw [mul_assoc]
        _ = a * (a * b ^ d) := by rw [(hcomm.pow_right d).eq]
        _ = (a * a) * b ^ d := by rw [← mul_assoc]
        _ = 0 := by rw [ha, zero_mul]
    rw [h1, h2, nsmul_zero, zero_add, ← pow_succ, mul_assoc, ← pow_succ, add_assoc]
    calc
      a * b ^ (d + 1) + (b ^ (d + 2) + (d + 1) • (a * b ^ (d + 1)))
          = b ^ (d + 2) + ((1 : ℕ) • (a * b ^ (d + 1)) + (d + 1) • (a * b ^ (d + 1))) := by
            rw [one_nsmul, add_left_comm]
      _ = b ^ (d + 2) + (d + 2) • (a * b ^ (d + 1)) := by
            rw [← add_nsmul, Nat.add_comm 1 (d + 1)]

/-- Canonical Darboux 2-form `∑ j : Fin n, ι (e j) * ι (f j)` (identical to `pfaffJetTwoForm e f`). -/
def darbouxTwoForm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (e f : Fin n → M) : ExteriorAlgebra R M :=
  ∑ j : Fin n, ExteriorAlgebra.ι R (e j) * ExteriorAlgebra.ι R (f j)

private theorem darbouxTwoForm_mem_exteriorPower {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (e f : Fin n → M) :
    darbouxTwoForm e f ∈ ⋀[R]^2 M := by
  dsimp [darbouxTwoForm]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [ExteriorAlgebra.exteriorPower, pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

private theorem two_blade_sq_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  have huv : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u =
      -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  calc
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)
        = ExteriorAlgebra.ι R u * (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) *
            ExteriorAlgebra.ι R v := by simp only [mul_assoc]
    _ = -((ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u) *
          ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v) := by
          rw [huv, mul_neg, neg_mul, ← mul_assoc (ExteriorAlgebra.ι R u) (ExteriorAlgebra.ι R u)]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul, neg_zero]

/-- Exact top power and next-power vanishing of Darboux's canonical 2-form over ANY `[CommRing R]`:
`(darbouxTwoForm e f) ^ n = n! • ∏ j, (ι (e j) * ι (f j))` and `(darbouxTwoForm e f) ^ (n + 1) = 0`. -/
theorem darbouxTwoForm_pow_spec {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    ∀ {n : ℕ} (e f : Fin n → M),
      (darbouxTwoForm (R := R) e f) ^ n =
          (n.factorial : R) •
            (List.ofFn fun j : Fin n => ExteriorAlgebra.ι R (e j) * ExteriorAlgebra.ι R (f j)).prod ∧
        (darbouxTwoForm (R := R) e f) ^ (n + 1) = 0
  | 0, _, _ => by
    simp [darbouxTwoForm]
  | n + 1, e, f => by
    let a := ExteriorAlgebra.ι R (e 0) * ExteriorAlgebra.ι R (f 0)
    let B := darbouxTwoForm (R := R) (e ∘ Fin.succ) (f ∘ Fin.succ)
    have hsplit : darbouxTwoForm (R := R) e f = a + B := by
      dsimp [darbouxTwoForm, a, B]
      rw [Fin.sum_univ_succ]
    have ha_mem : a ∈ ⋀[R]^2 M := by
      rw [ExteriorAlgebra.exteriorPower, pow_two]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    have hcomm : Commute a B := exteriorPower_two_mul_comm ha_mem B
    have ha2 : a * a = 0 := two_blade_sq_zero (e 0) (f 0)
    have ih := darbouxTwoForm_pow_spec (R := R) (e ∘ Fin.succ) (f ∘ Fin.succ)
    refine ⟨?_, ?_⟩
    · rw [hsplit, commute_sq_zero_add_pow hcomm ha2 n, ih.2, zero_add, ih.1,
        List.ofFn_succ, List.prod_cons, mul_smul_comm, ← Nat.cast_smul_eq_nsmul R (n + 1),
        smul_smul]
      congr 1
      push_cast [Nat.factorial_succ]
      ring
    · rw [hsplit, commute_sq_zero_add_pow hcomm ha2 (n + 1)]
      have hB2 : B ^ (n + 2) = 0 := by rw [pow_succ, ih.2, zero_mul]
      rw [hB2, ih.2, mul_zero, nsmul_zero, add_zero]

/-- Interleaved `2n`-vector tuple `[e₀, f₀, e₁, f₁, ..., e_{n-1}, f_{n-1}]`. -/
def interleaveVec {M : Type*} {n : ℕ} (e f : Fin n → M) : Fin (2 * n) → M :=
  fun k =>
    if k.val % 2 = 0 then e ⟨k.val / 2, by omega⟩ else f ⟨k.val / 2, by omega⟩

private theorem list_prod_twoBlades_eq_ιMulti {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] :
    ∀ {n : ℕ} (e f : Fin n → M),
      (List.ofFn fun j : Fin n => ExteriorAlgebra.ι R (e j) * ExteriorAlgebra.ι R (f j)).prod =
        ExteriorAlgebra.ιMulti R (2 * n) (interleaveVec e f)
  | 0, e, f => by simp [ExteriorAlgebra.ιMulti_zero_apply]
  | n + 1, e, f => by
    rw [List.ofFn_succ, List.prod_cons]
    have hrest : (List.ofFn fun i : Fin n =>
        ExteriorAlgebra.ι R (e i.succ) * ExteriorAlgebra.ι R (f i.succ)).prod =
        ExteriorAlgebra.ιMulti R (2 * n) (interleaveVec (e ∘ Fin.succ) (f ∘ Fin.succ)) :=
      list_prod_twoBlades_eq_ιMulti (e ∘ Fin.succ) (f ∘ Fin.succ)
    rw [hrest]
    change (ExteriorAlgebra.ι R (e 0) * ExteriorAlgebra.ι R (f 0)) *
        ExteriorAlgebra.ιMulti R (2 * n) (interleaveVec (e ∘ Fin.succ) (f ∘ Fin.succ)) =
      ExteriorAlgebra.ιMulti R ((2 * n + 1) + 1) (interleaveVec e f)
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc]
    have h0 : interleaveVec e f 0 = e 0 := by simp [interleaveVec]
    have h1 : Matrix.vecTail (interleaveVec e f) 0 = f 0 := by
      dsimp [Matrix.vecTail, interleaveVec]
      simp [Nat.mod_eq_of_lt (by omega : 1 < 2 * (n + 1))]
    have htail : Matrix.vecTail (Matrix.vecTail (interleaveVec e f)) =
        interleaveVec (e ∘ Fin.succ) (f ∘ Fin.succ) := by
      ext k
      simp only [Matrix.vecTail, interleaveVec, Function.comp_apply]
      have hmod : (k.val + 2) % 2 = k.val % 2 := by omega
      have hdiv : (k.val + 2) / 2 = k.val / 2 + 1 := by omega
      by_cases h : k.val % 2 = 0
      · have h2 : (k.val + 1 + 1) % 2 = 0 := by omega
        simp [h, h2]
        apply congrArg e
        exact Fin.ext hdiv
      · have h2 : (k.val + 1 + 1) % 2 ≠ 0 := by omega
        simp [h, h2]
        apply congrArg f
        exact Fin.ext hdiv
    rw [h0, h1, htail]

/-- **Grassmann Nos. 519 & 522–527 Darboux Odd/Even Normal-Form Class Dichotomy (`pp. 384–389`)**:
In `[CharZero K]` for any `n ≥ 1`:
1. **Odd/Contact `(2n + 1)`-normal form** on `K^{2n+1}`: `ω_c * Ω_c ^ n ≠ 0 ∧ Ω_c ^ (n + 1) = 0`.
2. **Even/Liouville `2n`-normal form** on `K^{2n}`: for EVERY nonzero covector coefficient
   tuple `y : Fin n → K`, `ω_e * Ω_e ^ (n - 1) ≠ 0`, `Ω_e ^ n ≠ 0`, and `ω_e * Ω_e ^ n = 0`
   (characteristic invariants separating odd class `(n, 2n + 1)` from even class `(n, 2n)`). -/
theorem grassmann_nos522_527_darboux_normal_form_dichotomy (K : Type*) [Field K] [CharZero K]
    (n : ℕ) (hn : 1 ≤ n) :
    (let b := Pi.basisFun K (Fin (2 * n + 1))
     let e : Fin n → (Fin (2 * n + 1) → K) := fun j => b ⟨2 * j.val, by omega⟩
     let f : Fin n → (Fin (2 * n + 1) → K) := fun j => b ⟨2 * j.val + 1, by omega⟩
     let ω_c := ExteriorAlgebra.ι K (b ⟨2 * n, by omega⟩)
     let Ω_c := pfaffJetTwoForm (R := K) e f
     ω_c * Ω_c ^ n ≠ 0 ∧ Ω_c ^ (n + 1) = 0) ∧
      (let b := Pi.basisFun K (Fin (2 * n))
       let e : Fin n → (Fin (2 * n) → K) := fun j => b ⟨2 * j.val, by omega⟩
       let f : Fin n → (Fin (2 * n) → K) := fun j => b ⟨2 * j.val + 1, by omega⟩
       let Ω_e := pfaffJetTwoForm (R := K) e f
       Ω_e ^ n ≠ 0 ∧
         ∀ y : Fin n → K, y ≠ 0 →
           pfaffJetOneForm y f * Ω_e ^ (n - 1) ≠ 0 ∧ pfaffJetOneForm y f * Ω_e ^ n = 0) := by
  have hfac : ((n.factorial : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  refine ⟨?_, ?_⟩
  · intro b e f ω_c Ω_c
    have hΩ : Ω_c = darbouxTwoForm (R := K) e f := rfl
    have hpow := darbouxTwoForm_pow_spec (R := K) e f
    rw [← hΩ] at hpow
    refine ⟨?_, hpow.2⟩
    rw [hpow.1, list_prod_twoBlades_eq_ιMulti, mul_smul_comm]
    have hcons : ExteriorAlgebra.ι K (b ⟨2 * n, by omega⟩) *
        ExteriorAlgebra.ιMulti K (2 * n) (interleaveVec e f) =
        ExteriorAlgebra.ιMulti K (2 * n + 1) (Fin.cons (b ⟨2 * n, by omega⟩) (interleaveVec e f)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      rfl
    rw [hcons]
    let σ : Fin (2 * n + 1) → Fin (2 * n + 1) :=
      Fin.cons ⟨2 * n, by omega⟩ (Fin.castAdd 1)
    have hfam : Fin.cons (b ⟨2 * n, by omega⟩) (interleaveVec e f) = b ∘ σ := by
      funext k
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨q, rfl⟩
      · rfl
      · simp only [Function.comp_apply, σ, Fin.cons_succ]
        dsimp [interleaveVec, e, f]
        split_ifs <;>
        · apply congrArg b
          exact Fin.ext (by dsimp; omega)
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · rfl
      · exfalso
        dsimp [σ] at hxy
        rw [Fin.cons_zero, Fin.cons_succ] at hxy
        have hv := congrArg Fin.val hxy
        simp only [Fin.val_castAdd] at hv
        omega
      · exfalso
        dsimp [σ] at hxy
        rw [Fin.cons_zero, Fin.cons_succ] at hxy
        have hv := congrArg Fin.val hxy
        simp only [Fin.val_castAdd] at hv
        omega
      · congr 1
        dsimp [σ] at hxy
        rw [Fin.cons_succ, Fin.cons_succ] at hxy
        have hv := congrArg Fin.val hxy
        simp only [Fin.val_castAdd] at hv
        exact Fin.ext hv
    rw [hfam]
    exact smul_ne_zero hfac
      (ιMulti_ne_zero_of_linearIndependent (b ∘ σ) (b.linearIndependent.comp σ hσ_inj))
  · intro b e f Ω_e
    have hΩ : Ω_e = darbouxTwoForm (R := K) e f := rfl
    have hpow := darbouxTwoForm_pow_spec (R := K) e f
    rw [← hΩ] at hpow
    have hΩ_ne : Ω_e ^ n ≠ 0 := by
      rw [hpow.1, list_prod_twoBlades_eq_ιMulti]
      have hfam : interleaveVec e f = b := by
        funext k
        dsimp [interleaveVec, e, f]
        split_ifs <;>
        · apply congrArg b
          exact Fin.ext (by dsimp; omega)
      rw [hfam]
      exact smul_ne_zero hfac
        (ιMulti_ne_zero_of_linearIndependent b b.linearIndependent)
    refine ⟨hΩ_ne, fun y hy => ⟨?_, ?_⟩⟩
    · intro hzero
      let v : Fin (2 * n) → K := ∑ j : Fin n, y j • f j
      have h1 : pfaffJetOneForm y f = ExteriorAlgebra.ι K v := by
        dsimp [pfaffJetOneForm, v]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.map_smul]
      have hv_ne : v ≠ 0 := by
        intro hv0
        apply hy
        funext j₀
        have hj₀ := congrFun hv0 ⟨2 * j₀.val + 1, by omega⟩
        dsimp [v] at hj₀
        have hcoord : (∑ j : Fin n, y j • f j) ⟨2 * j₀.val + 1, by omega⟩ = y j₀ := by
          rw [Finset.sum_apply]
          have hterm : ∀ j : Fin n, (y j • f j) ⟨2 * j₀.val + 1, by omega⟩ =
              if j = j₀ then y j₀ else 0 := fun j => by
            rw [Pi.smul_apply, smul_eq_mul]
            dsimp [f, b]
            rw [Pi.basisFun_apply, Pi.single_apply]
            by_cases hj : j = j₀
            · subst hj
              simp
            · have hne : (⟨2 * j₀.val + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * j.val + 1, by omega⟩ := by
                intro h
                apply hj
                ext
                have hv' := congrArg Fin.val h
                dsimp at hv'
                omega
              simp [hj, hne]
          simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [hcoord] at hj₀
        exact hj₀
      rw [h1] at hzero
      have hdiv := grassmann_no518_exterior_division hv_ne (darbouxTwoForm_mem_exteriorPower (R := K) e f)
        (n - 1) hzero
      rw [Nat.sub_add_cancel hn] at hdiv
      exact hΩ_ne hdiv
    · exact grassmann_no511_pfaff_exterior_vanishing y e f

end DarbouxNormalFormDichotomy

/-! ## 5. Wave II Causal Poset & Master Synthesis -/

section Wave2CausalPosetAndSynthesis

/-- 9-node acyclic causal poset covering Wave II (`GA₉`–`GA₁₇`) of `hmath019-endmatter.pdf`. -/
inductive GrassmannWave2Archetype : Type
  | GA9_PluckerSubspaceEquivalence
  | GA10_RegressiveSubspaceMeetDichotomy
  | GA11_ExteriorCramerRule
  | GA12_CircleSpaceMullerAndSyncyclicCountermodel
  | GA13_No512ContractionSyzygyReduction
  | GA14_Note114PfaffianSystems
  | GA15_No503LieSymplecticIsotropicBound
  | GA16_Nos522_527DarbouxClassDichotomy
  | GA17_MasterWave2Synthesis
  deriving DecidableEq, Repr

open GrassmannWave2Archetype

def gaWave2Le : GrassmannWave2Archetype → GrassmannWave2Archetype → Prop
  | a, b =>
    a = b ∨
    a = GA9_PluckerSubspaceEquivalence ∨
    b = GA17_MasterWave2Synthesis ∨
    (a = GA10_RegressiveSubspaceMeetDichotomy ∧
      (b = GA11_ExteriorCramerRule ∨ b = GA12_CircleSpaceMullerAndSyncyclicCountermodel)) ∨
    (a = GA13_No512ContractionSyzygyReduction ∧
      (b = GA14_Note114PfaffianSystems ∨ b = GA16_Nos522_527DarbouxClassDichotomy)) ∨
    (a = GA15_No503LieSymplecticIsotropicBound ∧ b = GA16_Nos522_527DarbouxClassDichotomy)

instance : DecidableRel gaWave2Le := fun a b => by
  dsimp [gaWave2Le]
  infer_instance

instance : PartialOrder GrassmannWave2Archetype where
  le := gaWave2Le
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

instance : DecidableLE GrassmannWave2Archetype := fun a b =>
  inferInstanceAs (Decidable (gaWave2Le a b))

instance : DecidableLT GrassmannWave2Archetype := fun a b => by
  change Decidable (gaWave2Le a b ∧ ¬ gaWave2Le b a)
  infer_instance

/-- Explicit non-linear branching witnesses in the 9-node Wave II causal poset. -/
theorem grassmann_wave2_poset_branching :
    ¬ (GA11_ExteriorCramerRule ≤ GA14_Note114PfaffianSystems) ∧
      ¬ (GA14_Note114PfaffianSystems ≤ GA11_ExteriorCramerRule) ∧
      ¬ (GA12_CircleSpaceMullerAndSyncyclicCountermodel ≤ GA15_No503LieSymplecticIsotropicBound) ∧
      ¬ (GA15_No503LieSymplecticIsotropicBound ≤ GA12_CircleSpaceMullerAndSyncyclicCountermodel) ∧
      GA9_PluckerSubspaceEquivalence < GA10_RegressiveSubspaceMeetDichotomy ∧
      GA10_RegressiveSubspaceMeetDichotomy < GA12_CircleSpaceMullerAndSyncyclicCountermodel ∧
      GA12_CircleSpaceMullerAndSyncyclicCountermodel < GA17_MasterWave2Synthesis ∧
      GA13_No512ContractionSyzygyReduction < GA16_Nos522_527DarbouxClassDichotomy ∧
      GA15_No503LieSymplecticIsotropicBound < GA16_Nos522_527DarbouxClassDichotomy ∧
      GA16_Nos522_527DarbouxClassDichotomy < GA17_MasterWave2Synthesis := by
  decide

/-- Master Wave II conjunction unifying all eight formal pillars (`GA₉`–`GA₁₆`) without wrappers. -/
theorem grassmann_endmatter_wave2_master_synthesis :
    (∀ (v w : Fin 2 → (Fin 4 → ℝ)), LinearIndependent ℝ v → LinearIndependent ℝ w →
      (Submodule.span ℝ (Set.range v) = Submodule.span ℝ (Set.range w) ↔
        ∃ c : ℝˣ, ExteriorAlgebra.ιMulti ℝ 2 v = (c : ℝ) • ExteriorAlgebra.ιMulti ℝ 2 w)) ∧
      (∀ (v w : Fin 2 → (Fin 3 → ℝ)), LinearIndependent ℝ v → LinearIndependent ℝ w →
        Submodule.span ℝ (Set.range v) ⊔ Submodule.span ℝ (Set.range w) = ⊤ →
          regressive (Pi.basisFun ℝ (Fin 3)) (ExteriorAlgebra.ιMulti ℝ 2 v) (ExteriorAlgebra.ιMulti ℝ 2 w) ≠ 0 ∧
            bladeSupport (regressive (Pi.basisFun ℝ (Fin 3))
              (ExteriorAlgebra.ιMulti ℝ 2 v) (ExteriorAlgebra.ιMulti ℝ 2 w)) =
              Submodule.span ℝ (Set.range v) ⊓ Submodule.span ℝ (Set.range w)) ∧
      (∀ (a : Fin 3 → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) (i : Fin 3),
        ExteriorAlgebra.ιMulti ℝ 3 (Function.update a i (∑ j : Fin 3, x j • a j)) =
          x i • ExteriorAlgebra.ιMulti ℝ 3 a) ∧
      (sigPos circleBilin.toQuadraticMap = 1 ∧ sigNeg circleBilin.toQuadraticMap = 3 ∧
        (∃ (T : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (u v : Fin 4 → ℝ),
          IsCircleTangent u v ∧ ¬ IsCircleTangent (T u) (T v))) ∧
      (∀ (w : Fin 3 → ℝ), (Pi.basisFun ℝ (Fin 3)).repr w 0 ≠ 0 →
        ∀ (Ω : ExteriorAlgebra ℝ (Fin 3 → ℝ)) (n : ℕ),
          ExteriorAlgebra.ι ℝ w * Ω ^ n = 0 ↔
            ∀ s : Finset (Fin 3), (0 : Fin 3) ∈ s →
              (Pi.basisFun ℝ (Fin 3)).ExteriorAlgebra.repr (ExteriorAlgebra.ι ℝ w * Ω ^ n) s = 0) ∧
      (∀ (α : Fin 3 → (Fin 4 → ℝ)) (U : Fin 2 → Fin 3 → ℝ) (β : Fin 2 → Fin 3 → (Fin 4 → ℝ))
          (ε r : Fin 2 → ℕ), 3 < ∑ κ : Fin 2, (ε κ + r κ) →
          (List.ofFn fun κ : Fin 2 =>
            (pfaffJetOneForm (U κ) α) ^ (ε κ) * (pfaffJetTwoForm (β κ) α) ^ (r κ)).prod = 0) ∧
      (∀ (W : Submodule ℝ (Fin 4 → ℝ)),
        (∀ x ∈ W, ∀ y ∈ W, canonicalSymplecticForm ℝ 2 x y = 0) →
          Module.finrank ℝ W ≤ 2) ∧
      (∀ (y : Fin 2 → ℝ), y ≠ 0 →
        let b4 := Pi.basisFun ℝ (Fin (2 * 2))
        let e : Fin 2 → (Fin (2 * 2) → ℝ) := fun j => b4 ⟨2 * j.val, by omega⟩
        let f : Fin 2 → (Fin (2 * 2) → ℝ) := fun j => b4 ⟨2 * j.val + 1, by omega⟩
        pfaffJetOneForm y f * pfaffJetTwoForm e f ≠ 0 ∧
          (pfaffJetTwoForm (R := ℝ) e f) ^ 2 ≠ 0 ∧
          pfaffJetOneForm y f * (pfaffJetTwoForm e f) ^ 2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    exact plucker_span_eq_iff_proportional v w hv hw
  · intro v w hv hw hsup
    exact regressive_blade_intersection_of_sup_eq_top (Pi.basisFun ℝ (Fin 3)) v w hv hw hsup
  · intro a x i
    exact exterior_cramer_ιMulti a x i
  · exact ⟨circleBilin_signature.1, circleBilin_signature.2, note97_syncyclic_vs_moebius_tangency.2.2⟩
  · intro w hw0 Ω n
    exact grassmann_no512_basis_coord_reduction (Pi.basisFun ℝ (Fin 3)) hw0 Ω n
  · intro α U β ε r hsum
    exact note114_pfaff_system_vanishing α U β ε r hsum
  · intro W hiso
    exact (lie_no503_canonical_symplectic_assembly ℝ 2 W hiso).1
  · intro y hy
    have hdic := (grassmann_nos522_527_darboux_normal_form_dichotomy ℝ 2 (by decide)).2
    have h2 := hdic.2 y hy
    refine ⟨?_, hdic.1, h2.2⟩
    simpa using h2.1

end Wave2CausalPosetAndSynthesis

end InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
