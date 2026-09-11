import Mathlib.Algebra.Group.Subgroup.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.Zorn.BruhatPeelingTransport

/-!
# Coordinate-Free Axiom (BN2) via Levi Root Decomposition

This module formalizes the structural, coordinate-free deduction of the Tits $(B, N)$
system generator axiom **(BN2)**:

$$s B s \subseteq B \cup B s B \quad (\forall s \in S)$$

via the **Levi root decomposition** of the Borel subgroup $B = U_s \ltimes U_s^\perp$:

1. **Simple Root Factor $U_s$**:
   The 1-dimensional root subgroup $U_s \cong \mathbb{F}_2$ satisfies the rank-1 $SL_2(\mathbb{F}_2)$
   relation $s U_s s \subseteq \{1\} \cup U_s s U_s \subseteq B \cup B s B$.
2. **Complementary Root Subgroup $U_s^\perp$**:
   The $(n-1)$-dimensional complementary root subgroup $U_s^\perp = U_{\Phi^+ \setminus \{\alpha_s\}}$
   is stabilized under conjugation by $s$: $s U_s^\perp s = U_s^\perp \subseteq B$.
3. **Symbolic Assembly**:
   Every $b \in B$ factors as $b = u \cdot v$ with $u \in U_s, v \in U_s^\perp$, giving:
   $$s b s = (s u s) \cdot (s v s) \in (B \cup B s B) \cdot B \subseteq B \cup B s B$$

All proofs are complete in native Lean 4 with zero sorrys and zero custom axioms.
-/

namespace InfoGeometry.Algebra.Zorn.LeviDecomposition

open InfoGeometry.Algebra.Zorn.BruhatPeeling

set_option linter.unusedVariables false

variable {G : Type*} [Group G]

/-! =========================================================================
    1. Levi Root Decomposition Data Structure
    ========================================================================= -/

/--
A Levi decomposition structure on $(B, S)$ decomposing $B$ with respect to each
simple generator $s \in S$ into a rank-1 simple root factor and a stable complement.
-/
structure LeviDecompositionData (B : Subgroup G) (S : Set G) where
  /-- The simple root subgroup $U_s \le B$. -/
  simpleRootFactor : G → Subgroup G
  /-- The complementary root subgroup $U_s^\perp \le B$. -/
  complementRootFactor : G → Subgroup G
  /-- $U_s$ is a subgroup of $B$. -/
  simple_le_borel : ∀ s ∈ S, simpleRootFactor s ≤ B
  /-- $U_s^\perp$ is a subgroup of $B$. -/
  complement_le_borel : ∀ s ∈ S, complementRootFactor s ≤ B
  /-- Every $b \in B$ factors as $u \cdot v$ with $u \in U_s, v \in U_s^\perp$. -/
  borel_factorization : ∀ s ∈ S, ∀ b ∈ B,
    ∃ (u : G) (hu : u ∈ simpleRootFactor s) (v : G) (hv : v ∈ complementRootFactor s),
      b = u * v
  /-- Rank-1 $SL_2$ relation on $U_s$: $s u s \in B \cup B s B$. -/
  simple_root_bn2 : ∀ s ∈ S, ∀ u ∈ simpleRootFactor s,
    (s * (u : G) * s) ∈ B ∨ ∃ b1 ∈ B, ∃ b2 ∈ B, (s * (u : G) * s) = b1 * s * b2
  /-- Complementary root invariance: $s U_s^\perp s \subseteq B$. -/
  complement_invariant : ∀ s ∈ S, ∀ v ∈ complementRootFactor s,
    (s * (v : G) * s) ∈ B

/-! =========================================================================
    2. Coordinate-Free Proof of Axiom (BN2)
    ========================================================================= -/

/--
🏆 THEOREM (Coordinate-Free Axiom BN2):
Under a Levi root decomposition, left and right conjugation by any simple reflection
$s \in S$ maps the Borel subgroup $B$ into $B \cup B s B$:
$$s B s \subseteq B \cup B s B$$
-/
theorem levi_root_bn2 (B : Subgroup G) (S : Set G) (data : LeviDecompositionData B S)
    (s : G) (hs : s ∈ S) (b : G) (hb : b ∈ B) (hs_sq : s * s = 1) :
    (s * b * s) ∈ (B : Set G) ∨ ∃ b1 ∈ B, ∃ b2 ∈ B, (s * b * s) = b1 * s * b2 := by
  obtain ⟨u, hu, v, hv, rfl⟩ := data.borel_factorization s hs b hb
  have hv_inv : s * v * s ∈ B := data.complement_invariant s hs v hv
  rcases data.simple_root_bn2 s hs u hu with hu_in_B | ⟨b1, hb1, b2, hb2, hu_cell⟩
  · left
    have h_prod : s * (u * v) * s = (s * u * s) * (s * v * s) := by
      calc
        s * (u * v) * s = s * u * (s * s) * v * s := by
          have h1 : s * u * (s * s) = s * u * 1 := by rw [hs_sq]
          rw [h1]
          group
        _ = (s * u * s) * (s * v * s) := by group
    rw [h_prod]
    exact Subgroup.mul_mem B hu_in_B hv_inv
  · right
    have h_prod : s * (u * v) * s = (s * u * s) * (s * v * s) := by
      calc
        s * (u * v) * s = s * u * (s * s) * v * s := by
          have h1 : s * u * (s * s) = s * u * 1 := by rw [hs_sq]
          rw [h1]
          group
        _ = (s * u * s) * (s * v * s) := by group
    rw [h_prod, hu_cell]
    refine ⟨b1, hb1, b2 * (s * v * s), B.mul_mem hb2 hv_inv, ?_⟩
    group

/--
Axiom BN2 in terms of simple reflection conjugation sets:
`s · B · s ⊆ B ∪ B · s · B`.
-/
def HasBN2Conjugation (B : Subgroup G) (S : Set G) : Prop :=
  ∀ s ∈ S, ∀ b ∈ B, (s * b * s) ∈ (B : Set G) ∨ ∃ b1 ∈ B, ∃ b2 ∈ B, (s * b * s) = b1 * s * b2

/--
🏆 THEOREM: Every Levi decomposition data certifies the global $(B, N)$ axiom `HasBN2Conjugation`.
-/
theorem hasBN2Conjugation_of_levi (B : Subgroup G) (S : Set G)
    (data : LeviDecompositionData B S) (hs_invol : ∀ s ∈ S, s * s = 1) :
    HasBN2Conjugation B S := by
  intro s hs b hb
  exact levi_root_bn2 B S data s hs b hb (hs_invol s hs)

/--
🏆 THEOREM (Simple Reflection Left-Coset Shift):
If $s b s = b_1 \in B$, then $s \cdot b = b_1 \cdot s$, so $s \cdot (b \cdot w) \in B \cdot (s \cdot w)$.
-/
theorem simple_shift_of_conj_in_borel (B : Subgroup G) (s b w : G)
    (hs_sq : s * s = 1) (b1 : G) (hb1 : b1 ∈ B) (h_conj : s * b * s = b1) :
    s * (b * w) = b1 * (s * w) := by
  calc
    s * (b * w) = (s * b * s) * s * w := by
      have : (s * b * s) * s * w = s * b * (s * s) * w := by group
      rw [this, hs_sq]
      group
    _ = b1 * (s * w) := by rw [h_conj]; group

end InfoGeometry.Algebra.Zorn.LeviDecomposition
