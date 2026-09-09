import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.l2Space
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Meta.Architecture

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.Canonical

open InfoGeometry.Topology

namespace CantorCuntzBasis

/-- Binary orbit words indexing the Cantor/Cuntz recursion. -/
abbrev BinaryWord := List Bool

/--
The theorem-backed Cantor/Cuntz basis packet.

This keeps the carrier minimal: an `O₂`-style Cuntz algebra carrier and a
distinguished seed vector from which the orbit is recursively generated.
-/
@[rep_depth operator]
structure CantorCuntzBasisPacket
    (Op : Type*) [Ring Op] [StarRing Op] where
  cuntz : CuntzO2Carrier Op
  seed : Op

namespace CantorCuntzBasisPacket

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (B : CantorCuntzBasisPacket Op)

/-- The recursively generated binary orbit. -/
@[rep_depth operator]
def orbit : BinaryWord → Op
  | [] => B.seed
  | false :: w => B.cuntz.S_left * orbit w
  | true :: w => B.cuntz.S_right * orbit w

/-- The orbit at the empty word is the seed. -/
@[rep_depth operator]
theorem orbit_root_eq_seed :
    orbit B [] = B.seed := by
  rfl

/-- The seed is exactly the root orbit. -/
@[rep_depth operator]
theorem orbit_seed_eq :
    B.seed = orbit B [] := by
  rfl

/-- Left branch action on a false child word. -/
@[rep_depth operator]
theorem orbit_cons_false_action (w : BinaryWord) :
    orbit B (false :: w) = B.cuntz.S_left * orbit B w := by
  rfl

/-- Right branch action on a true child word. -/
@[rep_depth operator]
theorem orbit_cons_true_action (w : BinaryWord) :
    orbit B (true :: w) = B.cuntz.S_right * orbit B w := by
  rfl

/--
Unified recursive orbit law.

This is the direct binary recursion behind the Cantor/Cuntz orbit.
-/
@[rep_depth operator]
theorem orbit_branch_recursion (b : Bool) (w : BinaryWord) :
    orbit B (b :: w) =
      (if b then B.cuntz.S_right else B.cuntz.S_left) * orbit B w := by
  cases b <;> simp [orbit]

/--
General induction principle for orbit words.

This is a plain list induction principle specialized to binary orbit words so
later orbit proofs can be structured without rewriting the recursion manually.
-/
@[rep_depth operator]
theorem orbit_word_induction
    {P : BinaryWord → Prop}
    (h_nil : P [])
    (h_false : ∀ w, P w → P (false :: w))
    (h_true : ∀ w, P w → P (true :: w)) :
    ∀ w, P w := by
  intro w
  induction w with
  | nil =>
      exact h_nil
  | cons b w ih =>
      cases b with
      | false =>
          simpa using h_false w ih
      | true =>
          simpa using h_true w ih

end CantorCuntzBasisPacket

namespace CuntzO2Carrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op)

/-- Left branch component of the seed decomposition. -/
@[rep_depth operator]
def seedBranchLeft (seed : Op) : Op :=
  C.leftRangeProjection * seed

/-- Right branch component of the seed decomposition. -/
@[rep_depth operator]
def seedBranchRight (seed : Op) : Op :=
  C.rightRangeProjection * seed

/-- The seed branch decomposition, exposed as the combined sum identity. -/
@[rep_depth operator]
theorem seed_branch_decomposition (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed + CuntzO2Carrier.seedBranchRight C seed = seed := by
  simpa [CuntzO2Carrier.seedBranchLeft, CuntzO2Carrier.seedBranchRight] using
    CuntzO2Carrier.rangeProjection_decomposition C seed

/-- Left branch readback of the seed decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_left (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed = C.leftRangeProjection * seed := by
  rfl

/-- Right branch readback of the seed decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_right (seed : Op) :
    CuntzO2Carrier.seedBranchRight C seed = C.rightRangeProjection * seed := by
  rfl

/-- Sum readback of the seed decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_sum (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed + CuntzO2Carrier.seedBranchRight C seed = seed := by
  simpa [CuntzO2Carrier.seedBranchLeft, CuntzO2Carrier.seedBranchRight] using
    CuntzO2Carrier.seed_branch_decomposition C seed

end CuntzO2Carrier

/-- Public seed branch decomposition theorem. -/
@[rep_depth operator]
theorem seed_branch_decomposition
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed + CuntzO2Carrier.seedBranchRight C seed = seed := by
  simpa using CuntzO2Carrier.seed_branch_decomposition C seed

/-- Public left readback of the seed branch decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_left
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed = C.leftRangeProjection * seed := by
  rfl

/-- Public right readback of the seed branch decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_right
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (seed : Op) :
    CuntzO2Carrier.seedBranchRight C seed = C.rightRangeProjection * seed := by
  rfl

/-- Public sum readback of the seed branch decomposition. -/
@[rep_depth operator]
theorem seed_branch_decomposition_sum
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (seed : Op) :
    CuntzO2Carrier.seedBranchLeft C seed + CuntzO2Carrier.seedBranchRight C seed = seed := by
  simpa [CuntzO2Carrier.seedBranchLeft, CuntzO2Carrier.seedBranchRight] using
    CuntzO2Carrier.seed_branch_decomposition C seed

end CantorCuntzBasis

section HilbertOrbit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/--
Orbit family attached to a Hilbert basis on binary words.

This is the theorem-backed infinite-dimensional basis layer: the orbit family
is a Hilbert basis, so orthogonality and completeness are genuine mathlib
consequences.
-/
@[rep_depth operator]
def orbitHilbert (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) : CantorCuntzBasis.BinaryWord → E :=
  b

@[simp, rep_depth operator]
theorem orbitHilbert_apply (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E)
    (w : CantorCuntzBasis.BinaryWord) :
    orbitHilbert b w = b w :=
  rfl

/-- The Hilbert-basis orbit is orthogonal on distinct words. -/
@[rep_depth operator]
theorem orbit_orthogonal_of_distinct_words
    (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) {w v : CantorCuntzBasis.BinaryWord}
    (h : w ≠ v) :
    ⟪orbitHilbert b w, orbitHilbert b v⟫_ℂ = 0 := by
  simpa [orbitHilbert] using (b.orthonormal.inner_eq_zero h)

/-- The Hilbert-basis orbit is orthonormal. -/
@[rep_depth operator]
theorem orbit_orthonormal (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) :
    Orthonormal ℂ (orbitHilbert b) := by
  exact b.orthonormal

/-- The Hilbert-basis orbit is complete in the Hilbert-space sense. -/
@[rep_depth operator]
theorem orbit_complete (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) :
    (Submodule.span ℂ (Set.range (orbitHilbert b))).topologicalClosure = ⊤ := by
  exact b.dense_span

/-- The Hilbert-basis orbit is cyclic. -/
@[rep_depth operator]
theorem orbit_cyclic (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (orbitHilbert b))).topologicalClosure := by
  rw [orbit_complete b]

/-- The orbit family itself is the Hilbert basis. -/
@[rep_depth operator]
def orbit_isHilbertBasis (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) :
    HilbertBasis CantorCuntzBasis.BinaryWord ℂ E :=
  b

/-- The basis readout is the inner-product coefficient formula. -/
@[rep_depth operator]
theorem orbit_basis_repr_apply
    (b : HilbertBasis CantorCuntzBasis.BinaryWord ℂ E) (x : E) (w : CantorCuntzBasis.BinaryWord) :
    (orbit_isHilbertBasis b).repr x w = ⟪orbitHilbert b w, x⟫_ℂ := by
  simpa [orbit_isHilbertBasis, orbitHilbert] using
    (b.repr_apply_apply x w)

end HilbertOrbit

end InfoGeometry.Canonical
