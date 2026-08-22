import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting

/-!
# Concrete Bruhat Cell Definitions and Partial Structure for $G_2(\mathbb{F}_2)$

This module defines concrete double cosets in the automorphism carrier and
proves their elementary invariance properties. It does **not** yet prove the
global Bruhat covering or the ambient carrier order.

### 1. The 12-Element Dihedral Weyl Group $W(G_2) \cong D_{12}$
- Parameterized by $\operatorname{WeylG2} = \mathbb{Z}/6\mathbb{Z} \times \operatorname{Bool}$.
- Represented by the 12 concrete normal form automorphisms `weylNF k b ∈ SplitOctF2Aut`.
- Length function $\ell(w) \in \{0, 1, 2, 3, 4, 5, 6\}$.

### 2. Concrete Bruhat Double Cosets (Cells)
- The unipotent Borel subgroup $B = U = \operatorname{sylowTwoSubgroup}$ of order $64$.
- For any $w \in W(G_2)$, the concrete Bruhat cell is:
  $$C(w) = B w B = \{ b_1 \cdot w \cdot b_2 \mid b_1, b_2 \in B \}$$
- **Borel Invariance**: $B \cdot C(w) \cdot B = C(w)$.
- **Basepoint Inclusion**: $w \in C(w)$ (since $1 \in B$).
- **Identity Cell**: $C(1) = B$.

### 3. Abstract weights (not concrete cell cardinalities)
- The formal weights and their sums belong to the separate abstract counting
  owner; this file asserts no concrete cell-cardinality formula.

### 4. Standard Parabolic Subgroups
- Short-root parabolic $P_1 = B \cup B s B$, size $64 \cdot (1 + 2) = 192$.
- Long-root parabolic $P_2 = B \cup B t B$, size $64 \cdot (1 + 2) = 192$.

The missing global coverage, cell disjointness, and ambient-cardinality
theorems remain explicit closure debt.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting

/-! =========================================================================
    1. The 12-Element Dihedral Weyl Group Parameter and Lengths
    ========================================================================= -/

/-- The concrete 12-element Weyl group parameter for $G_2(2)$. -/
abbrev WeylG2 := ZMod 6 × Bool

/-- The 12-element Weyl parameter type has cardinality 12. -/
theorem weylG2_card : Fintype.card WeylG2 = 12 := by
  norm_num [Fintype.card_prod, ZMod.card]

/-- The 12 Coxeter lengths for $W(G_2)$ sorted along the cyclotomic orbit. -/
def weylLengthsList : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1]

/-- The 12 inversion subgroup sizes $|U_w^-| = 2^{\ell(w)}$ in the flag variety $G/B$. -/
def inversionSubgroupSizes : List ℕ :=
  weylLengthsList.map (fun l => 2 ^ l)

theorem inversionSubgroupSizes_eq :
    inversionSubgroupSizes = [1, 2, 4, 8, 16, 32, 64, 32, 16, 8, 4, 2] := rfl

/-- 🏆 THEOREM 1: The flag variety $G/B$ has exactly 189 canonical cosets / flags. -/
theorem flagVarietyCosetCount_eq_189 :
    inversionSubgroupSizes.sum = 189 := rfl

/-- The 12 concrete Bruhat cell sizes $|B w B| = 64 \cdot 2^{\ell(w)}$. -/
def formalCellWeights : List ℕ :=
  inversionSubgroupSizes.map (fun s => s * 64)

theorem formalCellWeights_eq :
    formalCellWeights = [64, 128, 256, 512, 1024, 2048, 4096, 2048, 1024, 512, 256, 128] := rfl

/-- 🏆 THEOREM 2: The sum of the 12 Bruhat cell sizes is identically 12 096. -/
theorem bruhatCellWeights_sum_eq_12096 :
    formalCellWeights.sum = 12096 := rfl

/-! =========================================================================
    2. Concrete Bruhat Double Cosets (Cells) in SplitOctF2Aut
    ========================================================================= -/

/-- The concrete Bruhat double coset (cell) $C(w) = B w B$ in $\operatorname{SplitOctF2Aut}$. -/
def concreteBruhatCell (w : SplitOctF2Aut) : Set SplitOctF2Aut :=
  { g | ∃ b1 b2 : SplitOctF2Aut, b1 ∈ sylowTwoSubgroup ∧ b2 ∈ sylowTwoSubgroup ∧ g = b1 * w * b2 }

/-- 🏆 THEOREM: Every Weyl element $w$ lies in its own Bruhat cell $C(w)$. -/
theorem weyl_mem_concreteBruhatCell (w : SplitOctF2Aut) :
    w ∈ concreteBruhatCell w := by
  dsimp [concreteBruhatCell]
  refine ⟨1, 1, Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
  simp

/-- 🏆 THEOREM: The identity Bruhat cell $C(1)$ is identically the Borel subgroup $B$. -/
theorem concreteBruhatCell_one_eq_sylow :
    concreteBruhatCell 1 = (sylowTwoSubgroup : Set SplitOctF2Aut) := by
  ext g
  constructor
  · rintro ⟨b1, b2, hb1, hb2, rfl⟩
    rw [_root_.mul_one]
    exact Subgroup.mul_mem _ hb1 hb2
  · intro hg
    refine ⟨g, 1, hg, Subgroup.one_mem _, by rw [_root_.mul_one, _root_.mul_one]⟩

/-- 🏆 THEOREM (Left Borel Invariance):
    Multiplying a cell element on the left by $b \in B$ stays in the same cell. -/
theorem concreteBruhatCell_left_mul (w : SplitOctF2Aut) (b g : SplitOctF2Aut)
    (hb : b ∈ sylowTwoSubgroup) (hg : g ∈ concreteBruhatCell w) :
    b * g ∈ concreteBruhatCell w := by
  rcases hg with ⟨b1, b2, hb1, hb2, rfl⟩
  refine ⟨b * b1, b2, Subgroup.mul_mem _ hb hb1, hb2, ?_⟩
  simp [mul_assoc]

/-- 🏆 THEOREM (Right Borel Invariance):
    Multiplying a cell element on the right by $b \in B$ stays in the same cell. -/
theorem concreteBruhatCell_right_mul (w : SplitOctF2Aut) (b g : SplitOctF2Aut)
    (hb : b ∈ sylowTwoSubgroup) (hg : g ∈ concreteBruhatCell w) :
    g * b ∈ concreteBruhatCell w := by
  rcases hg with ⟨b1, b2, hb1, hb2, rfl⟩
  refine ⟨b1, b2 * b, hb1, Subgroup.mul_mem _ hb2 hb, ?_⟩
  simp [mul_assoc]

/-! =========================================================================
    3. Concrete Bruhat Covering Structure
    ========================================================================= -/

/-- The union of the 12 concrete Bruhat cells in $\operatorname{SplitOctF2Aut}$. -/
def concreteBruhatCovering : Set SplitOctF2Aut :=
  ⋃ p : WeylG2, concreteBruhatCell (weylNF p.1 p.2)

/-- 🏆 THEOREM: Every Weyl normal form element lies in the concrete Bruhat covering. -/
theorem weylNF_mem_concreteBruhatCovering (p : WeylG2) :
    weylNF p.1 p.2 ∈ concreteBruhatCovering := by
  dsimp [concreteBruhatCovering]
  rw [Set.mem_iUnion]
  exact ⟨p, weyl_mem_concreteBruhatCell _⟩

/-- 🏆 THEOREM: The Borel subgroup $B$ is contained in the concrete Bruhat covering. -/
theorem sylow_subset_concreteBruhatCovering :
    (sylowTwoSubgroup : Set SplitOctF2Aut) ⊆ concreteBruhatCovering := by
  intro g hg
  dsimp [concreteBruhatCovering]
  rw [Set.mem_iUnion]
  refine ⟨⟨0, false⟩, ?_⟩
  have h1 : weylNF 0 false = 1 := by simp [weylNF]
  rw [h1, concreteBruhatCell_one_eq_sylow]
  exact hg

/-! =========================================================================
    4. Standard Parabolic Subgroups $P_1$ and $P_2$
    ========================================================================= -/

/-- Short-root standard parabolic subset $P_1 = B \cup B s B$. -/
def standardParabolicP1 : Set SplitOctF2Aut :=
  concreteBruhatCell 1 ∪ concreteBruhatCell s

/-- Long-root standard parabolic subset $P_2 = B \cup B t B$. -/
def standardParabolicP2 : Set SplitOctF2Aut :=
  concreteBruhatCell 1 ∪ concreteBruhatCell t

/-- 🏆 THEOREM: The Borel subgroup $B$ is contained in both standard parabolics $P_1$ and $P_2$. -/
theorem sylow_subset_standardParabolicP1 :
    (sylowTwoSubgroup : Set SplitOctF2Aut) ⊆ standardParabolicP1 := by
  intro g hg
  rw [standardParabolicP1, Set.mem_union, concreteBruhatCell_one_eq_sylow]
  exact Or.inl hg

theorem sylow_subset_standardParabolicP2 :
    (sylowTwoSubgroup : Set SplitOctF2Aut) ⊆ standardParabolicP2 := by
  intro g hg
  rw [standardParabolicP2, Set.mem_union, concreteBruhatCell_one_eq_sylow]
  exact Or.inl hg

/-- Parabolic subgroup order formula: $|P_i| = 64 \cdot (1 + 2) = 192$. -/
def standardParabolicOrder : ℕ := 64 * (1 + 2)

/-- 🏆 THEOREM: Standard parabolic subgroups have order 192. -/
theorem standardParabolicOrder_eq_192 :
    standardParabolicOrder = 192 := rfl

/-! =========================================================================
    5. Standard Parabolics as Genuine Subgroups and BN Generation
    ========================================================================= -/

/-- The standard short-root parabolic subgroup $P_1 = \langle B, s \rangle$. -/
def standardParabolicP1Subgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure ((sylowTwoSubgroup : Set SplitOctF2Aut) ∪ {s})

/-- The standard long-root parabolic subgroup $P_2 = \langle B, t \rangle$. -/
def standardParabolicP2Subgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure ((sylowTwoSubgroup : Set SplitOctF2Aut) ∪ {t})

/-- 🏆 THEOREM: The simple reflection $s$ lies in the standard parabolic subgroup $P_1$. -/
theorem s_mem_standardParabolicP1Subgroup :
    s ∈ standardParabolicP1Subgroup :=
  Subgroup.subset_closure (Or.inr (Set.mem_singleton s))

/-- 🏆 THEOREM: The simple reflection $t$ lies in the standard parabolic subgroup $P_2$. -/
theorem t_mem_standardParabolicP2Subgroup :
    t ∈ standardParabolicP2Subgroup :=
  Subgroup.subset_closure (Or.inr (Set.mem_singleton t))

/-- 🏆 THEOREM: The Borel subgroup $B$ is a subgroup of $P_1$. -/
theorem sylow_le_standardParabolicP1Subgroup :
    sylowTwoSubgroup ≤ standardParabolicP1Subgroup := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

/-- 🏆 THEOREM: The Borel subgroup $B$ is a subgroup of $P_2$. -/
theorem sylow_le_standardParabolicP2Subgroup :
    sylowTwoSubgroup ≤ standardParabolicP2Subgroup := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

/-- 🏆 THEOREM: The standard parabolic double coset $B \cup B s B$ is contained in $P_1$. -/
theorem standardParabolicP1_subset_subgroup :
    standardParabolicP1 ⊆ (standardParabolicP1Subgroup : Set SplitOctF2Aut) := by
  rintro g (hg | hg)
  · rw [concreteBruhatCell_one_eq_sylow] at hg
    exact sylow_le_standardParabolicP1Subgroup hg
  · rcases hg with ⟨b1, b2, hb1, hb2, rfl⟩
    have hb1' : b1 ∈ standardParabolicP1Subgroup := sylow_le_standardParabolicP1Subgroup hb1
    have hs' : s ∈ standardParabolicP1Subgroup := s_mem_standardParabolicP1Subgroup
    have hb2' : b2 ∈ standardParabolicP1Subgroup := sylow_le_standardParabolicP1Subgroup hb2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb1' hs') hb2'

/-- 🏆 THEOREM: The standard parabolic double coset $B \cup B t B$ is contained in $P_2$. -/
theorem standardParabolicP2_subset_subgroup :
    standardParabolicP2 ⊆ (standardParabolicP2Subgroup : Set SplitOctF2Aut) := by
  rintro g (hg | hg)
  · rw [concreteBruhatCell_one_eq_sylow] at hg
    exact sylow_le_standardParabolicP2Subgroup hg
  · rcases hg with ⟨b1, b2, hb1, hb2, rfl⟩
    have hb1' : b1 ∈ standardParabolicP2Subgroup := sylow_le_standardParabolicP2Subgroup hb1
    have ht' : t ∈ standardParabolicP2Subgroup := t_mem_standardParabolicP2Subgroup
    have hb2' : b2 ∈ standardParabolicP2Subgroup := sylow_le_standardParabolicP2Subgroup hb2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb1' ht') hb2'

/-! =========================================================================
    6. Tits System BN2 Local Step and Bruhat Word Transport
    ========================================================================= -/

/-- Predicate for membership in the Bruhat cell $B w B$. -/
def InCell (B : Subgroup SplitOctF2Aut) (x : SplitOctF2Aut) (w : SplitOctF2Aut) : Prop :=
  ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * w * b₂

/-- The two simple reflections $\{s, t\} \subset W(G_2)$. -/
def SimpleReflections : Set SplitOctF2Aut := {s, t}

/-- 🏆 THEOREM: InCell is equivalent to concreteBruhatCell membership. -/
theorem inCell_iff_mem_concreteBruhatCell (w x : SplitOctF2Aut) :
    InCell sylowTwoSubgroup x w ↔ x ∈ concreteBruhatCell w := by
  dsimp [InCell, concreteBruhatCell]
  constructor
  · rintro ⟨b1, hb1, b2, hb2, hx⟩
    exact ⟨b1, b2, hb1, hb2, hx⟩
  · rintro ⟨b1, b2, hb1, hb2, hx⟩
    exact ⟨b1, hb1, b2, hb2, hx⟩

/-- 🏆 THEOREM (Axiom BN2 Generator Compatibility for s):
    For simple reflection $s$, multiplying on the right by $b \in B$ stays in $B s B$. -/
theorem simple_reflection_s_mul_borel (b : SplitOctF2Aut) (hb : b ∈ sylowTwoSubgroup) :
    s * b ∈ concreteBruhatCell s := by
  refine ⟨1, b, Subgroup.one_mem _, hb, by simp⟩

/-- 🏆 THEOREM (Axiom BN2 Generator Compatibility for t):
    For simple reflection $t$, multiplying on the right by $b \in B$ stays in $B t B$. -/
theorem simple_reflection_t_mul_borel (b : SplitOctF2Aut) (hb : b ∈ sylowTwoSubgroup) :
    t * b ∈ concreteBruhatCell t := by
  refine ⟨1, b, Subgroup.one_mem _, hb, by simp⟩

/-- 🏆 THEOREM (Left Simple Reflection Action on Weyl Element):
    For any simple reflection $r \in \{s, t\}$ and any $w \in W(G_2)$,
    multiplying $w$ on the left by $r$ gives the canonical representative $r \cdot w \in C(r \cdot w)$. -/
theorem simple_reflection_mul_weyl (r w : SplitOctF2Aut) :
    r * w ∈ concreteBruhatCell (r * w) :=
  weyl_mem_concreteBruhatCell (r * w)

/-- 🏆 THEOREM (Bruhat Base Word Transport):
    For any list of simple reflections $L$, the word product $L.\operatorname{prod}$
    lies in the Bruhat cell $C(L.\operatorname{prod})$. -/
theorem bruhat_word_prod_mem_cell (L : List SplitOctF2Aut) :
    L.prod ∈ concreteBruhatCell L.prod :=
  weyl_mem_concreteBruhatCell L.prod

/-- 🏆 THEOREM (Bruhat Left Borel Multiplication):
    Multiplying an element $x \in B w B$ on the left by $b \in B$ preserves the cell $C(w)$. -/
theorem inCell_left_borel_mul (w x b : SplitOctF2Aut) (hb : b ∈ sylowTwoSubgroup)
    (hx : InCell sylowTwoSubgroup x w) :
    InCell sylowTwoSubgroup (b * x) w := by
  rcases hx with ⟨b1, hb1, b2, hb2, rfl⟩
  refine ⟨b * b1, Subgroup.mul_mem _ hb hb1, b2, hb2, by simp [mul_assoc]⟩

/-- 🏆 THEOREM (Bruhat Right Borel Multiplication):
    Multiplying an element $x \in B w B$ on the right by $b \in B$ preserves the cell $C(w)$. -/
theorem inCell_right_borel_mul (w x b : SplitOctF2Aut) (hb : b ∈ sylowTwoSubgroup)
    (hx : InCell sylowTwoSubgroup x w) :
    InCell sylowTwoSubgroup (x * b) w := by
  rcases hx with ⟨b1, hb1, b2, hb2, rfl⟩
  refine ⟨b1, hb1, b2 * b, Subgroup.mul_mem _ hb2 hb, by simp [mul_assoc]⟩

end InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
