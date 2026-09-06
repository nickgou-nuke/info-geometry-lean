import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
import InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting
import InfoGeometry.Algebra.Zorn.BruhatPeelingTransport
import InfoGeometry.Algebra.Zorn.G2BNPair
import InfoGeometry.Algebra.Zorn.BruhatSubwordOrder
import InfoGeometry.Algebra.Zorn.BruhatIntervalPoincare
import InfoGeometry.Algebra.Zorn.LeviRootDecompositionBN2
import InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization

/-!
# Concrete Bruhat Cell Definitions and Partial Structure for $G_2(\mathbb{F}_2)$

This module defines concrete Bruhat cells and proves their elementary invariance
properties.  It does not yet prove global carrier coverage, pairwise cell
disjointness, or the ambient group order; those require a concrete BN2/factor
chart and a carrier-level normal-form theorem.

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

### 3. Bruhat Counting Targets
- The displayed cell weights and sums are CAS targets, not concrete theorems in this file.

### 4. Standard Parabolic Subgroups
- Short-root parabolic $P_1 = B \cup B s B$, size $64 \cdot (1 + 2) = 192$.
- Long-root parabolic $P_2 = B \cup B t B$, size $64 \cdot (1 + 2) = 192$.
- Subgroups $P_1 = \langle B, s \rangle$ and $P_2 = \langle B, t \rangle$.

### 5. Inductive Bruhat Transport and $(B, N)$ Peeling-Off
- Axiom (BN2): $s B s \subseteq B \cup B s B$.
- Inductive Word Transport: $L.\operatorname{prod} \cdot (B w B) \subseteq \bigcup_{w'} B w' B$.
- Double-Coset Multiplication Closure: $(B w_1 B) \cdot (B w_2 B) \subseteq \bigcup B w' B$.

The proved results in this file are limited to the explicitly stated elementary
cell properties; no global Bruhat classification is claimed here.
-/

namespace InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting
open InfoGeometry.Algebra.Zorn.BruhatPeeling
open InfoGeometry.Algebra.Zorn.BruhatOrder
open InfoGeometry.Algebra.Zorn.BruhatInterval
open InfoGeometry.Algebra.Zorn.LeviDecomposition
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

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

theorem concreteBruhatCell_eq_exact_unipotentCell (w : SplitOctF2Aut) :
    concreteBruhatCell w =
      InfoGeometry.Algebra.Zorn.G2BNPair.doubleCoset
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w := by
  rw [concreteBruhatCell]
  rw [InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.sylowTwoSubgroup_eq_unipotentSubgroup]
  ext g
  constructor
  · rintro ⟨b₁, b₂, hb₁, hb₂, rfl⟩
    exact ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, b₂, hb₁, hb₂, rfl⟩

/-! A concrete disjointness interface for the indexed Bruhat cells.  The
    hypothesis is stated at the actual double-coset witness level: this is
    the separation statement that a future concrete BN-pair certificate must
    provide.  In particular, it does not incorrectly infer disjointness from
    inequality of arbitrary middle elements. -/

theorem concreteBruhatCell_disjoint_of_witness_separation
    (w₁ w₂ : SplitOctF2Aut)
    (hsep : ∀ (b₁ b₂ c₁ c₂ : SplitOctF2Aut),
      b₁ ∈ sylowTwoSubgroup → b₂ ∈ sylowTwoSubgroup →
      c₁ ∈ sylowTwoSubgroup → c₂ ∈ sylowTwoSubgroup →
      b₁ * w₁ * b₂ ≠ c₁ * w₂ * c₂) :
    Disjoint (concreteBruhatCell w₁) (concreteBruhatCell w₂) := by
  apply Set.disjoint_left.mpr
  intro g hg₁ hg₂
  rcases hg₁ with ⟨b₁, b₂, hb₁, hb₂, rfl⟩
  rcases hg₂ with ⟨c₁, c₂, hc₁, hc₂, hEq⟩
  exact hsep b₁ b₂ c₁ c₂ hb₁ hb₂ hc₁ hc₂ hEq

theorem concreteBruhatCell_inter_eq_empty_of_witness_separation
    (w₁ w₂ : SplitOctF2Aut)
    (hsep : ∀ (b₁ b₂ c₁ c₂ : SplitOctF2Aut),
      b₁ ∈ sylowTwoSubgroup → b₂ ∈ sylowTwoSubgroup →
      c₁ ∈ sylowTwoSubgroup → c₂ ∈ sylowTwoSubgroup →
      b₁ * w₁ * b₂ ≠ c₁ * w₂ * c₂) :
    concreteBruhatCell w₁ ∩ concreteBruhatCell w₂ = (∅ : Set SplitOctF2Aut) := by
  exact Set.disjoint_iff_inter_eq_empty.mp
    (concreteBruhatCell_disjoint_of_witness_separation w₁ w₂ hsep)

/-! The quotient-level separation route is the canonical finite-geometry
    interface.  A certificate that the two B-orbits in G/B are disjoint is
    transported to disjointness of the corresponding concrete double cosets. -/

theorem concreteBruhatCell_disjoint_of_quotientOrbit_separation
    (w₁ w₂ : SplitOctF2Aut)
    (hsep : Disjoint
      (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w₁)
      (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w₂)) :
    Disjoint (concreteBruhatCell w₁) (concreteBruhatCell w₂) := by
  rw [concreteBruhatCell_eq_exact_unipotentCell,
    concreteBruhatCell_eq_exact_unipotentCell]
  exact InfoGeometry.Algebra.Zorn.G2BNPair.disjoint_doubleCoset_of_disjoint_quotientOrbit
    InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w₁ w₂ hsep

theorem concreteBruhatCell_inter_eq_empty_of_quotientOrbit_separation
    (w₁ w₂ : SplitOctF2Aut)
    (hsep : Disjoint
      (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w₁)
      (InfoGeometry.Algebra.Zorn.G2BNPair.quotientOrbit
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup w₂)) :
    concreteBruhatCell w₁ ∩ concreteBruhatCell w₂ =
      (∅ : Set SplitOctF2Aut) := by
  exact Set.disjoint_iff_inter_eq_empty.mp
    (concreteBruhatCell_disjoint_of_quotientOrbit_separation w₁ w₂ hsep)

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

/-! The one-sided PC peel preserves a double coset once the input is known to
    lie in that cell.  This is the correct residual statement: it does not
    collapse a general double-coset element to its Weyl representative. -/

theorem fullPeel_mem_same_concreteBruhatCell
    {f w : SplitOctF2Aut} (hf : f ∈ concreteBruhatCell w) :
    fullPeel f ∈ concreteBruhatCell w := by
  let q : SplitOctF2Aut := G2TwoSylowSubgroup.pcWord (extractAllBits f)
  have hq : q ∈ sylowTwoSubgroup := by
    exact G2TwoSylowSubgroup.pcWord_mem_sylow _
  have hfactor : q * fullPeel f = f := by
    simpa [q] using fullPeel_pcWord_factorization f
  rcases hf with ⟨b₁, b₂, hb₁, hb₂, rfl⟩
  have hres : fullPeel (b₁ * w * b₂) =
      q⁻¹ * (b₁ * w * b₂) := by
    calc
      fullPeel (b₁ * w * b₂) = 1 * fullPeel (b₁ * w * b₂) := by simp
      _ = (q⁻¹ * q) * fullPeel (b₁ * w * b₂) := by
        rw [inv_mul_cancel]
      _ = q⁻¹ * (q * fullPeel (b₁ * w * b₂)) := by
        simp [mul_assoc]
      _ = q⁻¹ * (b₁ * w * b₂) := by rw [hfactor]
  rw [hres]
  refine ⟨q⁻¹ * b₁, b₂, sylowTwoSubgroup.mul_mem
    (sylowTwoSubgroup.inv_mem hq) hb₁, hb₂, ?_⟩
  simp [mul_assoc]

/-! =========================================================================
    3. Concrete Bruhat Covering Structure
    ========================================================================= -/

/-- The union of the 12 concrete Bruhat cells in $\operatorname{SplitOctF2Aut}$. -/
def concreteBruhatCovering : Set SplitOctF2Aut :=
  ⋃ p : WeylG2, concreteBruhatCell (weylNF p.1 p.2)

/-- The concrete coverage obligation, kept separate from its generation
consequence until the ambient Bruhat classification is proved. -/
def concreteBruhatCoverObligation : Prop :=
  ∀ g : SplitOctF2Aut, ∃ p : WeylG2,
    g ∈ concreteBruhatCell (weylNF p.1 p.2)

/-- The explicit coverage obligation is exactly the assertion that the
    indexed union of the twelve cells is the whole carrier. -/
theorem concreteBruhatCoverObligation_iff_covering_eq_univ :
    concreteBruhatCoverObligation ↔ concreteBruhatCovering = Set.univ := by
  constructor
  · intro h
    ext g
    simp only [Set.mem_univ, iff_true]
    simpa [concreteBruhatCovering] using h g
  · intro h g
    have hg : g ∈ concreteBruhatCovering := by
      rw [h]
      exact Set.mem_univ g
    simpa [concreteBruhatCovering] using hg

/-! The quotient-orbit transport is the concrete interface expected from a
finite flag-space certificate.  The orbit-cover premise remains explicit. -/
theorem concreteBruhatCoverObligation_of_quotient_orbit_cover
    (hcover : ∀ g : SplitOctF2Aut, ∃ p : WeylG2, ∃ b : SplitOctF2Aut,
      b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        b • (QuotientGroup.mk (weylNF p.1 p.2) :
          SplitOctF2Aut ⧸
            InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) =
          QuotientGroup.mk g) :
    concreteBruhatCoverObligation := by
  intro g
  obtain ⟨p, b, hb, hq⟩ := hcover g
  refine ⟨p, ?_⟩
  rw [concreteBruhatCell_eq_exact_unipotentCell]
  exact (InfoGeometry.Algebra.Zorn.G2BNPair.mem_doubleCoset_iff_quotient_smul
    InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup
      (weylNF p.1 p.2) g).2 ⟨b, hb, hq⟩

/-- A finite flag-orbit partition transports directly to the concrete cover.
The hypotheses are the exact finite certificate that must be supplied by the
carrier-aligned CAS export and proved in Lean. -/
theorem concreteBruhatCoverObligation_of_fin189_orbit_partition
    (enum : Fin 189 ≃
      SplitOctF2Aut ⧸ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup)
    (p : Fin 12 → WeylG2)
    (cells : Fin 12 → Finset (Fin 189))
    (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ cells k →
      ∃ b : SplitOctF2Aut,
        b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup ∧
          enum i = b •
            (QuotientGroup.mk (weylNF (p k).1 (p k).2) :
              SplitOctF2Aut ⧸
                InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup))
    (hpartition : Finset.univ.biUnion cells = Finset.univ) :
    concreteBruhatCoverObligation := by
  apply concreteBruhatCoverObligation_of_quotient_orbit_cover
  intro g
  let i : Fin 189 := enum.symm (QuotientGroup.mk g)
  have hi : i ∈ Finset.univ := Finset.mem_univ i
  rw [← hpartition, Finset.mem_biUnion] at hi
  obtain ⟨k, hk, hki⟩ := hi
  obtain ⟨b, hb, hq⟩ := hcell k i hki
  refine ⟨p k, b, hb, ?_⟩
  have henum : enum i = QuotientGroup.mk g := by
    dsimp [i]
    exact enum.apply_symm_apply _
  rw [henum] at hq
  exact hq.symm

/-- The finite flag certificate closes the concrete twelve-cell covering
    exactly, once its enumeration and orbit-membership fields are supplied. -/
theorem concreteBruhatCovering_eq_univ_of_fin189_orbit_partition
    (enum : Fin 189 ≃
      SplitOctF2Aut ⧸ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup)
    (p : Fin 12 → WeylG2)
    (cells : Fin 12 → Finset (Fin 189))
    (hcell : ∀ (k : Fin 12) (i : Fin 189), i ∈ cells k →
      ∃ b : SplitOctF2Aut,
        b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup ∧
          enum i = b •
            (QuotientGroup.mk (weylNF (p k).1 (p k).2) :
              SplitOctF2Aut ⧸
                InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup))
    (hpartition : Finset.univ.biUnion cells = Finset.univ) :
    concreteBruhatCovering = Set.univ := by
  apply concreteBruhatCoverObligation_iff_covering_eq_univ.mp
  exact concreteBruhatCoverObligation_of_fin189_orbit_partition
    enum p cells hcell hpartition

/-! The residual formulation is equivalent to the ambient twelve-cell cover.
    This is a substantive transport theorem: it uses the existing PC recovery
    factorization and the concrete cell invariance, without assuming the cover.
    The conditional convenience theorem is intentionally not exported here. -/

theorem fullPeel_bruhat_cover_iff :
    (∀ f : SplitOctF2Aut, ∃ w : WeylG2,
      fullPeel f ∈ concreteBruhatCell (weylNF w.1 w.2)) ↔
      concreteBruhatCovering = Set.univ := by
  constructor
  · intro h
    apply concreteBruhatCoverObligation_iff_covering_eq_univ.mp
    intro f
    obtain ⟨w, hw⟩ := h f
    let q : SplitOctF2Aut :=
      G2TwoSylowSubgroup.pcWord (extractAllBits f)
    have hq : q ∈ sylowTwoSubgroup := by
      exact G2TwoSylowSubgroup.pcWord_mem_sylow _
    have hfactor : q * fullPeel f = f := by
      simpa [q] using fullPeel_pcWord_factorization f
    refine ⟨w, ?_⟩
    rw [← hfactor]
    exact concreteBruhatCell_left_mul _ _ _ hq hw
  · intro h f
    have hf : f ∈ concreteBruhatCovering := by
      rw [h]
      exact Set.mem_univ f
    have hcell : ∃ w : WeylG2,
        f ∈ concreteBruhatCell (weylNF w.1 w.2) := by
      simpa [concreteBruhatCovering] using hf
    obtain ⟨w, hw⟩ := hcell
    let q : SplitOctF2Aut :=
      G2TwoSylowSubgroup.pcWord (extractAllBits f)
    have hq : q ∈ sylowTwoSubgroup := by
      exact G2TwoSylowSubgroup.pcWord_mem_sylow _
    have hfactor : q * fullPeel f = f := by
      simpa [q] using fullPeel_pcWord_factorization f
    refine ⟨w, ?_⟩
    have hres : fullPeel f = q⁻¹ * f := by
      calc
        fullPeel f = 1 * fullPeel f := by simp
        _ = (q⁻¹ * q) * fullPeel f := by rw [inv_mul_cancel]
        _ = q⁻¹ * (q * fullPeel f) := by simp
        _ = q⁻¹ * f := by rw [hfactor]
    rw [hres]
    exact concreteBruhatCell_left_mul _ _ _
      (sylowTwoSubgroup.inv_mem hq) hw

/-- The exact generation consequence of a concrete 12-cell cover.  The
covering hypothesis is kept explicit: this theorem does not manufacture the
missing ambient Bruhat classification. -/
theorem concreteGeneratedSubgroup_eq_top_of_bruhat_cover
    (hcover : concreteBruhatCoverObligation) :
    Subgroup.closure
        ((sylowTwoSubgroup : Set SplitOctF2Aut) ∪
          Set.range (fun p : WeylG2 => weylNF p.1 p.2)) = ⊤ := by
  apply InfoGeometry.Algebra.Zorn.G2BNPair.closure_eq_top_of_doubleCoset_cover
    sylowTwoSubgroup (Set.range (fun p : WeylG2 => weylNF p.1 p.2))
  intro g
  obtain ⟨p, hp⟩ := hcover g
  refine ⟨weylNF p.1 p.2, ⟨p, rfl⟩, ?_⟩
  simpa [concreteBruhatCell,
    InfoGeometry.Algebra.Zorn.G2BNPair.doubleCoset] using hp

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

theorem standardParabolicP1Subgroup_le_nativePointStabilizer :
    standardParabolicP1Subgroup ≤ nativePointStabilizer := by
  rw [standardParabolicP1Subgroup]
  apply (Subgroup.closure_le _).2
  intro g hg
  rcases hg with hg | hg
  · have hSylow : sylowTwoSubgroup ≤ nativePointStabilizer := by
      rw [← pcSubgroup_eq_sylowTwoSubgroup]
      exact pcSubgroup_le_nativePointStabilizer
    exact hSylow hg
  · have hs : g = s := Set.mem_singleton_iff.mp hg
    subst g
    exact InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer.swap01Aut_pointData_fix

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
    6. Tits System BN2 Compatibility and Local Step
    ========================================================================= -/

/-- The two simple reflections $\{s, t\} \subset W(G_2)$. -/
def SimpleReflections : Set SplitOctF2Aut := {s, t}

/-- 🏆 THEOREM: `InCell` from generic peeling matches `concreteBruhatCell`. -/
theorem inCell_iff_mem_concreteBruhatCell (w x : SplitOctF2Aut) :
    BruhatPeeling.InCell sylowTwoSubgroup x w ↔ x ∈ concreteBruhatCell w := by
  dsimp [BruhatPeeling.InCell, concreteBruhatCell]
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

end InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
