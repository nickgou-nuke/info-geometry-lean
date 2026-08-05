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

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op) (seed : Op)

/-- The recursively generated binary orbit. -/
@[rep_depth operator]
def orbit : BinaryWord → Op
  | [] => seed
  | false :: w => CuntzO2Carrier.S_left C * orbit w
  | true :: w => CuntzO2Carrier.S_right C * orbit w

theorem left_branch_isometry :
    star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C = 1 := by
  simpa [CuntzO2Carrier.S_left] using CuntzO2Carrier.left_isometry C

theorem right_branch_isometry :
    star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C = 1 := by
  simpa [CuntzO2Carrier.S_right] using CuntzO2Carrier.right_isometry C

theorem left_right_branch_orthogonal :
    star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_right C = 0 := by
  exact (CuntzO2Carrier.orthogonal_ranges C).1

theorem right_left_branch_orthogonal :
    star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_left C = 0 := by
  exact (CuntzO2Carrier.orthogonal_ranges C).2

/-- The orbit at the empty word is the seed. -/
@[rep_depth operator]
theorem orbit_root_eq_seed :
    orbit C seed [] = seed := by
  rfl

/-- The seed is exactly the root orbit. -/
@[rep_depth operator]
theorem orbit_seed_eq :
    seed = orbit C seed [] := by
  rfl

/-- Left branch action on a false child word. -/
@[rep_depth operator]
theorem orbit_cons_false_action (w : BinaryWord) :
    orbit C seed (false :: w) = CuntzO2Carrier.S_left C * orbit C seed w := by
  rfl

/-- Right branch action on a true child word. -/
@[rep_depth operator]
theorem orbit_cons_true_action (w : BinaryWord) :
    orbit C seed (true :: w) = CuntzO2Carrier.S_right C * orbit C seed w := by
  rfl

/--
Unified recursive orbit law.

This is the direct binary recursion behind the Cantor/Cuntz orbit.
-/
@[rep_depth operator]
theorem orbit_branch_recursion (b : Bool) (w : BinaryWord) :
    orbit C seed (b :: w) =
      (if b then CuntzO2Carrier.S_right C else CuntzO2Carrier.S_left C) * orbit C seed w := by
  cases b <;> simp [orbit]

theorem orbit_append_recursion (u w : BinaryWord) :
    orbit C seed (u ++ w) =
      List.foldr
        (fun b x => (if b then CuntzO2Carrier.S_right C else CuntzO2Carrier.S_left C) * x)
        (orbit C seed w) u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [List.cons_append, orbit_branch_recursion]
      simp only [List.foldr]
      rw [ih]

theorem left_action_preserves_star_mul (x : Op) :
    star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C * (star x * x) =
      star x * x := by
  rw [left_branch_isometry C]
  simp

theorem right_action_preserves_star_mul (x : Op) :
    star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C * (star x * x) =
      star x * x := by
  rw [right_branch_isometry C]
  simp

theorem orbit_words_orthogonal
    (u v : BinaryWord)
    (hlen : u.length = v.length)
    (hne : u ≠ v) :
    star (orbit C seed u) * orbit C seed v = 0 := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => exact (hne rfl).elim
      | cons c v => simp at hlen
  | cons b u ih =>
      cases v with
      | nil => simp at hlen
      | cons c v =>
          have htail : u.length = v.length := by simpa using hlen
          cases b with
          | false =>
              cases c with
              | false =>
                  simp only [orbit, star_mul]
                  calc
                    star (orbit C seed u) * star (CuntzO2Carrier.S_left C) *
                          (CuntzO2Carrier.S_left C * orbit C seed v) =
                        star (orbit C seed u) *
                          (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C) *
                            orbit C seed v := by noncomm_ring
                    _ = star (orbit C seed u) * orbit C seed v := by
                      rw [left_branch_isometry C]
                      simp
                    _ = 0 := ih v htail (by
                      intro huv
                      apply hne
                      simp [huv])
              | true =>
                  simp only [orbit, star_mul]
                  calc
                    star (orbit C seed u) * star (CuntzO2Carrier.S_left C) *
                          (CuntzO2Carrier.S_right C * orbit C seed v) =
                        star (orbit C seed u) *
                          (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_right C) *
                            orbit C seed v := by noncomm_ring
                    _ = 0 := by
                      rw [left_right_branch_orthogonal C]
                      simp
          | true =>
              cases c with
              | false =>
                  simp only [orbit, star_mul]
                  calc
                    star (orbit C seed u) * star (CuntzO2Carrier.S_right C) *
                          (CuntzO2Carrier.S_left C * orbit C seed v) =
                        star (orbit C seed u) *
                          (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_left C) *
                            orbit C seed v := by noncomm_ring
                    _ = 0 := by
                      rw [right_left_branch_orthogonal C]
                      simp
              | true =>
                  simp only [orbit, star_mul]
                  calc
                    star (orbit C seed u) * star (CuntzO2Carrier.S_right C) *
                          (CuntzO2Carrier.S_right C * orbit C seed v) =
                        star (orbit C seed u) *
                          (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C) *
                            orbit C seed v := by noncomm_ring
                    _ = star (orbit C seed u) * orbit C seed v := by
                      rw [right_branch_isometry C]
                      simp
                    _ = 0 := ih v htail (by
                      intro huv
                      apply hne
                      simp [huv])

theorem orbit_word_isometric (w : BinaryWord) :
    star (orbit C seed w) * orbit C seed w = star seed * seed := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b with
      | false =>
          simp only [orbit, star_mul]
          calc
            star (orbit C seed w) * star (CuntzO2Carrier.S_left C) *
                  (CuntzO2Carrier.S_left C * orbit C seed w) =
                star (orbit C seed w) *
                  (star (CuntzO2Carrier.S_left C) * CuntzO2Carrier.S_left C) *
                    orbit C seed w := by noncomm_ring
            _ = star (orbit C seed w) * orbit C seed w := by
              rw [left_branch_isometry C]
              simp
            _ = star seed * seed := ih
      | true =>
          simp only [orbit, star_mul]
          calc
            star (orbit C seed w) * star (CuntzO2Carrier.S_right C) *
                  (CuntzO2Carrier.S_right C * orbit C seed w) =
                star (orbit C seed w) *
                  (star (CuntzO2Carrier.S_right C) * CuntzO2Carrier.S_right C) *
                    orbit C seed w := by noncomm_ring
            _ = star (orbit C seed w) * orbit C seed w := by
              rw [right_branch_isometry C]
              simp
            _ = star seed * seed := ih

theorem orbit_words_inner_eq_ite
    (u v : BinaryWord)
    (hlen : u.length = v.length) :
    star (orbit C seed u) * orbit C seed v =
      if u = v then star seed * seed else 0 := by
  by_cases h : u = v
  · subst v
    simp [orbit_word_isometric]
  · rw [orbit_words_orthogonal C seed u v hlen h]
    simp [h]

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



variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : CuntzO2Carrier Op) (seed : Op)

theorem orbit_words_equal_norm
    (u v : BinaryWord) (h : u.length = v.length) :
    star (orbit C seed u) * orbit C seed u =
      star (orbit C seed v) * orbit C seed v := by
  rw [orbit_word_isometric C seed u, orbit_word_isometric C seed v]

theorem orbit_append_preserves_norm
    (u v : BinaryWord) :
    star (orbit C seed (u ++ v)) * orbit C seed (u ++ v) =
      star (orbit C seed u) * orbit C seed u := by
  rw [orbit_word_isometric C seed (u ++ v), orbit_word_isometric C seed u]



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
