import InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback

/-!
# A Stabilizer Filtration for the native split-octonion carrier

This module defines a finite filtration of the native flag stabilizer over
`Oₛ(𝔽₂)`:

  `{1} = U₆ ⊴ U₅ ⊴ U₄ ⊴ U₃ ⊴ U₂ ⊴ U₁ ⊴ U₀ = B`

where each stage `U_k` is defined as the intersection of the native flag
stabilizer with the stabilizer of a growing finite set of basis vectors.

The terminal stage is proved to be `⊥` by native basis readback.  This file
does not assert a root-subgroup series, an Artin--Schreier tower, or an
identification with the full automorphism group.
-/

namespace InfoGeometry.Algebra.Zorn.GaloisPeelingFiltration

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

/-- The ascending sequence of basis subsets in `Oₛ(𝔽₂)` fixed by the Galois tower. -/
def flagBasisSequence (k : Fin 7) : Set SplitOctF2 :=
  match k with
  | 0 => ∅
  | 1 => {basis8 4}
  | 2 => {basis8 4, basis8 6}
  | 3 => {basis8 4, basis8 6, basis8 5}
  | 4 => {basis8 4, basis8 6, basis8 5, basis8 3}
  | 5 => {basis8 4, basis8 6, basis8 5, basis8 3, basis8 2}
  | 6 => Set.range basis8

/-- The Galois peeling tower `U_k` as the intersection of `B` and the Galois stabilizer. -/
def galoisTower (k : Fin 7) : Subgroup SplitOctF2Aut :=
  nativeFlagStabilizer ⊓ galoisStabilizer (flagBasisSequence k)

/-- Monotonicity of the basis sequence. -/
theorem flagBasisSequence_monotone {i j : Fin 7} (h : i ≤ j) :
    flagBasisSequence i ⊆ flagBasisSequence j := by
  intro x hx
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold flagBasisSequence at hx ⊢
  interval_cases i <;> interval_cases j <;> try contradiction
  · exact hx
  · rcases hx with rfl; simp
  · rcases hx with rfl; simp
  · rcases hx with rfl; simp
  · rcases hx with rfl; simp
  · rcases hx with rfl; exact ⟨4, rfl⟩
  · exact hx
  · rcases hx with (rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl)
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
  · exact hx
  · rcases hx with (rfl | rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl | rfl)
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨5, rfl⟩
  · exact hx
  · rcases hx with (rfl | rfl | rfl | rfl) <;> simp
  · rcases hx with (rfl | rfl | rfl | rfl)
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨3, rfl⟩
  · exact hx
  · rcases hx with (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
  · exact hx

/-- The Galois tower is an antitone filtration of subgroups: `U_j ≤ U_i` for `i ≤ j`. -/
theorem galoisTower_antitone {i j : Fin 7} (h : i ≤ j) :
    galoisTower j ≤ galoisTower i := by
  dsimp [galoisTower]
  apply inf_le_inf_left
  exact galoisStabilizer_antitone (flagBasisSequence_monotone h)

/-- Top of the Galois tower: `U_0 = B`. -/
theorem galoisTower_zero_eq_borel :
    galoisTower 0 = nativeFlagStabilizer := by
  ext g
  simp [galoisTower, galoisStabilizer, flagBasisSequence]

/-- The base point `basis8 4` is fixed by `U_0 = B`, hence `U_1 = B`. -/
theorem galoisTower_one_eq_borel :
    galoisTower 1 = nativeFlagStabilizer := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    refine ⟨hg, ?_⟩
    intro X hX
    rcases hX with rfl
    exact nativeFlagStabilizer_basis8_four hg

/-- Terminal stage `U_6` fixes the entire basis of `Oₛ(𝔽₂)`. -/
theorem galoisTower_six_fixes_all_basis
    {g : SplitOctF2Aut} (hg : g ∈ galoisTower 6) (j : Fin 8) :
    g.1 (basis8 j) = basis8 j := by
  have hstab := hg.2
  apply hstab
  exact ⟨j, rfl⟩

/-- An automorphism fixing the 4 generator vectors fixes all 8 basis vectors. -/
theorem automorphism_all_basis_fixed_of_generators
    (g : SplitOctF2Aut)
    (h2 : g.1 (basis8 2) = basis8 2)
    (h4 : g.1 (basis8 4) = basis8 4)
    (h5 : g.1 (basis8 5) = basis8 5)
    (h7 : g.1 (basis8 7) = basis8 7) :
    ∀ j : Fin 8, g.1 (basis8 j) = basis8 j :=
  automorphism_basis8_all_fixed_of_generators_fixed g h2 h4 h5 h7

theorem peel0_eq_self_of_basis_fixed (g : SplitOctF2Aut) (h7 : g.1 (basis8 7) = basis8 7) :
    peel0 g = g := by
  dsimp [peel0]
  have h0 : (g.1 (basis8 7)).x0 = false := by rw [h7]; rfl
  simp [h0]

theorem peel1_eq_self_of_basis_fixed (g : SplitOctF2Aut) (h2 : g.1 (basis8 2) = basis8 2) :
    peel1 g = g := by
  dsimp [peel1]
  have h1 : (g.1 (basis8 2)).x1 = false := by rw [h2]; rfl
  simp [h1]

theorem peel2_eq_self_of_basis_fixed (g : SplitOctF2Aut) (h7 : g.1 (basis8 7) = basis8 7) :
    peel2 g = g := by
  dsimp [peel2]
  have h1 : (g.1 (basis8 7)).x1 = false := by rw [h7]; rfl
  simp [h1]

theorem peel34_eq_self_of_basis_fixed (g : SplitOctF2Aut)
    (h2 : g.1 (basis8 2) = basis8 2) (h3 : g.1 (basis8 3) = basis8 3) :
    peel34 g = g := by
  dsimp [peel34]
  have h2y1 : (g.1 (basis8 2)).y1 = false := by rw [h2]; rfl
  have h3x2 : (g.1 (basis8 3)).x2 = false := by rw [h3]; rfl
  simp [h2y1, h3x2]

/-- An element in `galoisTower 6` has trivial unipotent action and is the identity. -/
theorem galoisTower_six_eq_bot_of_readback
    {g : SplitOctF2Aut}
    (hfix : ∀ j : Fin 8, g.1 (basis8 j) = basis8 j) :
    g = 1 := by
  have hu : g ∈ unipotentSubgroup := by
    apply mem_unipotentSubgroup_of_basis_action_eq
      (e := fun _ : Fin 6 => false)
    intro j
    rw [hfix j]
    rfl
  rcases hu with ⟨e, he⟩
  have he0 : e = fun _ => false := by
    have hrec := extractAllBits_pcWord e
    have hext : extractAllBits (G2TwoSylowSubgroup.pcWord e) = fun _ => false := by
      rw [he]
      have hp0 := peel0_eq_self_of_basis_fixed g (hfix 7)
      have hp1 := peel1_eq_self_of_basis_fixed g (hfix 2)
      have hp2 := peel2_eq_self_of_basis_fixed g (hfix 7)
      have hp34 := peel34_eq_self_of_basis_fixed g (hfix 2) (hfix 3)
      funext i
      fin_cases i
      · change (g.1 (basis8 7)).x0 = false
        rw [hfix 7]
        rfl
      · change ((peel0 g).1 (basis8 2)).x1 = false
        rw [hp0, hfix 2]
        rfl
      · change ((peel1 (peel0 g)).1 (basis8 7)).x1 = false
        rw [hp0, hp1, hfix 7]
        rfl
      · change (((peel2 (peel1 (peel0 g))).1 (basis8 3)).x2 ^^
            ((peel2 (peel1 (peel0 g))).1 (basis8 2)).y1) = false
        rw [hp0, hp1, hp2, hfix 3, hfix 2]
        rfl
      · change ((peel2 (peel1 (peel0 g))).1 (basis8 2)).y1 = false
        rw [hp0, hp1, hp2, hfix 2]
        rfl
      · change ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = false
        rw [hp0, hp1, hp2, hp34, hfix 2]
        rfl
    rw [hext] at hrec
    exact hrec.symm
  rw [← he, he0]
  rfl

/-- The Fixed Field / Fixed Algebra terminal theorem: `U₆ = {1}`. -/
theorem galoisTower_six_eq_bot :
    galoisTower 6 = ⊥ := by
  ext g
  constructor
  · intro hg
    have hall := galoisTower_six_fixes_all_basis hg
    rw [Subgroup.mem_bot]
    exact galoisTower_six_eq_bot_of_readback hall
  · intro hg
    rw [Subgroup.mem_bot] at hg
    subst hg
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro X _
    rfl

/-- Elementwise form of the terminal filtration statement. -/
theorem mem_galoisTower_six_iff {g : SplitOctF2Aut} :
    g ∈ galoisTower 6 ↔ g = 1 := by
  rw [galoisTower_six_eq_bot]
  simp

/-- For any stabilizer element `g ∈ B`, `fullPeel g` unconditionally fixes `basis8 4`. -/
theorem fullPeel_basis8_four_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 4) = basis8 4 :=
  G2NativeFlagStabilizerClosureReadback.fullPeel_basis8_four_readback hg

/-- For any stabilizer element `g ∈ B`, `fullPeel g` unconditionally fixes `basis8 5`. -/
theorem fullPeel_basis8_five_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 5) = basis8 5 :=
  G2NativeFlagStabilizerClosureReadback.fullPeel_basis8_five_readback hg

end InfoGeometry.Algebra.Zorn.GaloisPeelingFiltration
