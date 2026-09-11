import Mathlib.Topology.Constructions
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Clopen
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Complex
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CuntzCantorBoundaryShift
import InfoGeometry.Canonical.UHFBoundaryExactSequence

/-!
# Product topology for the finite-cylinder Cantor boundary

The algebraic UHF boundary owner deliberately leaves topology open.  This
file supplies only the native product-topological layer: compactness of the
binary boundary, continuity of finite prefixes and cylinders, and continuity
of the two branch maps and the tail map.  It does not assert a C*-completion,
measure, KMS state, or spectral theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.UHFBoundaryExactSequence

theorem continuous_boundaryPrefix (n : ℕ) :
    Continuous (boundaryPrefix n) := by
  apply continuous_pi
  intro i
  simpa [boundaryPrefix] using (continuous_apply i.1)

theorem continuous_cylinder (n : ℕ) (f : DiagAlg n) :
    Continuous (cylinder n f) := by
  exact continuous_of_discreteTopology.comp
    (continuous_boundaryPrefix n)

theorem continuous_tail :
    Continuous (tail : CantorBoundary → CantorBoundary) := by
  apply continuous_pi
  intro n
  simpa [tail] using (continuous_apply (n + 1))

theorem continuous_prependBit (b : Bool) :
    Continuous (prependBit b : CantorBoundary → CantorBoundary) := by
  apply continuous_pi
  intro n
  cases n with
  | zero =>
      simpa [prependBit] using (continuous_const :
        Continuous (fun _ : CantorBoundary => b))
  | succ k =>
      simpa [prependBit] using (continuous_apply k)

theorem continuous_cylinder_branch_pullback
    (n : ℕ) (b : Bool) (f : DiagAlg (n + 1)) :
    Continuous
      (fun x : CantorBoundary =>
        cylinder (n + 1) f (prependBit b x)) := by
  exact (continuous_cylinder (n + 1) f).comp
    (continuous_prependBit b)

theorem cylinder_colimit_mem_continuous
    {g : CantorBoundary → ℂ} (hg : g ∈ CylinderColimit) :
    Continuous g := by
  rcases hg with ⟨p, rfl⟩
  exact continuous_cylinder p.1 p.2

theorem cantorBoundary_compact :
    IsCompact (Set.univ : Set CantorBoundary) :=
  isCompact_univ

theorem prependBit_image_compact (b : Bool) :
    IsCompact (Set.range (prependBit b)) :=
  isCompact_range (continuous_prependBit b)

theorem prependBit_isClosedEmbedding (b : Bool) :
    Topology.IsClosedEmbedding
      (prependBit b : CantorBoundary → CantorBoundary) :=
  (continuous_prependBit b).isClosedEmbedding
    (prependBit_injective b)

theorem prependBit_image_closed (b : Bool) :
    IsClosed (Set.range (prependBit b)) :=
  (prependBit_isClosedEmbedding b).isClosed_range

theorem prependBit_image_compl (b : Bool) :
    (Set.range (prependBit b))ᶜ = Set.range (prependBit (!b)) := by
  cases b
  · ext x
    constructor
    · intro hx
      rcases prependBit_range_cover x with h | h
      · exact False.elim (hx h)
      · exact h
    · intro hx hsame
      exact Set.disjoint_left.mp prependBit_false_true_disjoint hsame hx
  · ext x
    constructor
    · intro hx
      rcases prependBit_range_cover x with h | h
      · exact h
      · exact False.elim (hx h)
    · intro hx hsame
      exact Set.disjoint_left.mp prependBit_false_true_disjoint hx hsame

theorem prependBit_image_clopen (b : Bool) :
    IsClopen (Set.range (prependBit b)) := by
  refine ⟨prependBit_image_closed b, ?_⟩
  have h : Set.range (prependBit b) =
      (Set.range (prependBit (!b)))ᶜ := by
    rw [prependBit_image_compl (!b)]
    simp
  rw [h]
  simpa using (prependBit_image_closed (!b)).isOpen_compl

/-- Each binary branch is homeomorphic to its closed image. -/
noncomputable def prependBitHomeomorph (b : Bool) :
    CantorBoundary ≃ₜ Set.range (prependBit b) :=
  (prependBit_isClosedEmbedding b).isEmbedding.toHomeomorph

@[simp] theorem prependBitHomeomorph_apply
    (b : Bool) (x : CantorBoundary) :
    ((prependBitHomeomorph b x : Set.range (prependBit b)) : CantorBoundary) =
      prependBit b x :=
  rfl

@[simp] theorem prependBitHomeomorph_symm_apply
    (b : Bool) (x : CantorBoundary) :
    (prependBitHomeomorph b).symm
        ⟨prependBit b x, ⟨x, rfl⟩⟩ = x := by
  exact Topology.IsEmbedding.toHomeomorph_symm_apply
    (prependBit_isClosedEmbedding b).isEmbedding x

theorem tail_image_compact :
    IsCompact (Set.range (tail : CantorBoundary → CantorBoundary)) :=
  isCompact_range continuous_tail

/-! The Cuntz branch operators preserve the finite-cylinder carrier. -/

/-- Remove the leading bit from a finite word. -/
def dropHeadWord (n : ℕ) (w : BitWord (n + 1)) : BitWord n :=
  fun i => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

/-- Extend a finite cylinder by placing it on one binary branch. -/
def branchCylinder (n : ℕ) (b : Bool) (f : DiagAlg n) : DiagAlg (n + 1) :=
  fun w => if w ⟨0, Nat.succ_pos n⟩ = b then f (dropHeadWord n w) else 0

theorem dropHeadWord_boundaryPrefix (n : ℕ) (x : CantorBoundary) :
    dropHeadWord n (boundaryPrefix (n + 1) x) = boundaryPrefix n (tail x) := by
  ext i
  rfl

theorem cylinder_branchCylinder (n : ℕ) (b : Bool) (f : DiagAlg n)
    (x : CantorBoundary) :
    cylinder (n + 1) (branchCylinder n b f) x =
      if x 0 = b then cylinder n f (tail x) else 0 := by
  dsimp [cylinder, branchCylinder, dropHeadWord, boundaryPrefix, tail]
  by_cases h : x 0 = b
  · simp [h, dropHeadWord_boundaryPrefix]
  · simp [h]

theorem S_L_op_cylinder (n : ℕ) (f : DiagAlg n) :
    S_L_op (cylinder n f) = cylinder (n + 1) (branchCylinder n false f) := by
  funext x
  dsimp [S_L_op]
  rw [cylinder_branchCylinder]

theorem S_R_op_cylinder (n : ℕ) (f : DiagAlg n) :
    S_R_op (cylinder n f) = cylinder (n + 1) (branchCylinder n true f) := by
  funext x
  dsimp [S_R_op]
  rw [cylinder_branchCylinder]

theorem S_L_op_mem_cylinder_colimit (n : ℕ) (f : DiagAlg n) :
    S_L_op (cylinder n f) ∈ CylinderColimit := by
  exact ⟨⟨n + 1, branchCylinder n false f⟩, (S_L_op_cylinder n f).symm⟩

theorem S_R_op_mem_cylinder_colimit (n : ℕ) (f : DiagAlg n) :
    S_R_op (cylinder n f) ∈ CylinderColimit := by
  exact ⟨⟨n + 1, branchCylinder n true f⟩, (S_R_op_cylinder n f).symm⟩

theorem S_L_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : S_L_op g ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  exact S_L_op_mem_cylinder_colimit n f

theorem S_R_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : S_R_op g ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  exact S_R_op_mem_cylinder_colimit n f

/-! Pullback by a fixed branch remains at the same finite cylinder stage. -/

/-- Replace the first bit of a finite word by a fixed branch bit. -/
def prependHeadWord : (n : ℕ) → Bool → BitWord n → BitWord n
  | 0, _, _ => fun i => Fin.elim0 i
  | _ + 1, b, w => fun i => i.cases b (fun j => w j.castSucc)

/-- Finite-stage pullback of a cylinder along a branch inclusion. -/
def prependHeadDiag (n : ℕ) (b : Bool) (f : DiagAlg n) : DiagAlg n :=
  fun w => f (prependHeadWord n b w)

theorem boundaryPrefix_prependBit (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix n (prependBit b x) =
      prependHeadWord n b (boundaryPrefix n x) := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl

theorem star_S_L_op_cylinder (n : ℕ) (f : DiagAlg n) :
    star_S_L_op (cylinder n f) = cylinder n (prependHeadDiag n false f) := by
  funext x
  dsimp [star_S_L_op, cylinder, prependHeadDiag]
  rw [boundaryPrefix_prependBit]

theorem star_S_R_op_cylinder (n : ℕ) (f : DiagAlg n) :
    star_S_R_op (cylinder n f) = cylinder n (prependHeadDiag n true f) := by
  funext x
  dsimp [star_S_R_op, cylinder, prependHeadDiag]
  rw [boundaryPrefix_prependBit]

theorem star_S_L_op_mem_cylinder_colimit (n : ℕ) (f : DiagAlg n) :
    star_S_L_op (cylinder n f) ∈ CylinderColimit := by
  exact ⟨⟨n, prependHeadDiag n false f⟩, (star_S_L_op_cylinder n f).symm⟩

theorem star_S_R_op_mem_cylinder_colimit (n : ℕ) (f : DiagAlg n) :
    star_S_R_op (cylinder n f) ∈ CylinderColimit := by
  exact ⟨⟨n, prependHeadDiag n true f⟩, (star_S_R_op_cylinder n f).symm⟩

theorem star_S_L_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : star_S_L_op g ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  exact star_S_L_op_mem_cylinder_colimit n f

theorem star_S_R_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : star_S_R_op g ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  exact star_S_R_op_mem_cylinder_colimit n f

theorem UHF_boundary_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : UHF_boundary_op g ∈ CylinderColimit := by
  exact S_L_op_preserves_cylinder_colimit
    (star_S_R_op_preserves_cylinder_colimit hg)

theorem star_UHF_boundary_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : star_UHF_boundary_op g ∈ CylinderColimit := by
  exact S_R_op_preserves_cylinder_colimit
    (star_S_L_op_preserves_cylinder_colimit hg)

theorem UHF_Laplacian_op_preserves_cylinder_colimit {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : UHF_Laplacian_op g ∈ CylinderColimit := by
  rw [UHF_Laplacian_op_eq_id]
  exact hg

/-! Prefix cylinders are the compact clopen pieces of the boundary topology. -/

/-- The basic clopen cylinder determined by a finite binary word. -/
def cylinderSet (n : ℕ) (w : BitWord n) : Set CantorBoundary :=
  boundaryPrefix n ⁻¹' ({w} : Set (BitWord n))

theorem cylinderSet_isClopen (n : ℕ) (w : BitWord n) :
    IsClopen (cylinderSet n w) := by
  exact (isClopen_discrete ({w} : Set (BitWord n))).preimage
    (continuous_boundaryPrefix n)

theorem cylinderSet_isCompact (n : ℕ) (w : BitWord n) :
    IsCompact (cylinderSet n w) := by
  exact (cylinderSet_isClopen n w).isClosed.isCompact

theorem cylinderSet_disjoint {n : ℕ} {w v : BitWord n} (h : w ≠ v) :
    Disjoint (cylinderSet n w) (cylinderSet n v) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change boundaryPrefix n x = w at hx
  change boundaryPrefix n x = v at hy
  exact h (hx.symm.trans hy)

theorem cylinderSet_separates {x y : CantorBoundary} (hxy : x ≠ y) :
    ∃ n : ℕ, ∃ w : BitWord n,
      x ∈ cylinderSet n w ∧ y ∉ cylinderSet n w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨i + 1, boundaryPrefix (i + 1) x, ?_, ?_⟩
  · change boundaryPrefix (i + 1) x = boundaryPrefix (i + 1) x
    rfl
  · intro hy
    change boundaryPrefix (i + 1) y = boundaryPrefix (i + 1) x at hy
    have hi' := congrFun hy ⟨i, Nat.lt_succ_self i⟩
    exact hi (by simpa [boundaryPrefix] using hi'.symm)

/-- Add a fixed leading bit to a finite word. -/
def prependWord (n : ℕ) (b : Bool) (w : BitWord n) : BitWord (n + 1) :=
  fun i => i.cases b (fun j => w j)

theorem boundaryPrefix_succ_prependBit (n : ℕ) (b : Bool) (x : CantorBoundary) :
    boundaryPrefix (n + 1) (prependBit b x) =
      prependWord n b (boundaryPrefix n x) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rfl

theorem cylinderSet_prependBit_image (n : ℕ) (b : Bool) (w : BitWord n) :
    prependBit b '' cylinderSet n w =
      cylinderSet (n + 1) (prependWord n b w) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change boundaryPrefix (n + 1) (prependBit b x) = prependWord n b w
    rw [boundaryPrefix_succ_prependBit]
    change boundaryPrefix n x = w at hx
    rw [hx]
  · intro hy
    change boundaryPrefix (n + 1) y = prependWord n b w at hy
    have hhead : y 0 = b := by
      have hzero := congrFun hy ⟨0, Nat.succ_pos n⟩
      exact hzero
    refine ⟨tail y, ?_, ?_⟩
    · change boundaryPrefix n (tail y) = w
      rw [← prependBit_tail_of_head hhead] at hy
      rw [boundaryPrefix_succ_prependBit] at hy
      funext j
      have htail := congrFun hy ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩
      simpa [prependWord, boundaryPrefix, tail] using htail
    · exact prependBit_tail_of_head hhead

/-- Finite-prefix cylinders form a topological basis for the product boundary.

This uses only Mathlib's product-topology basis theorem; no metric or
analytic completion is used in this statement. -/
theorem isTopologicalBasis_cylinderSet :
    TopologicalSpace.IsTopologicalBasis
      {s : Set CantorBoundary |
        ∃ (n : ℕ) (w : BitWord n), s = cylinderSet n w} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro s ⟨n, w, rfl⟩
    exact (cylinderSet_isClopen n w).isOpen
  · intro x u hx hu
    obtain ⟨v, ⟨V, F, -, rfl⟩, hxv, hvu⟩ :
        ∃ v ∈ { S : Set CantorBoundary | ∃ (V : ∀ i : ℕ, Set Bool)
          (F : Finset ℕ),
          (∀ i : ℕ, i ∈ F → V i ∈ { s : Set Bool | IsOpen s }) ∧
            S = (F : Set ℕ).pi V },
        x ∈ v ∧ v ⊆ u :=
      (isTopologicalBasis_pi
        (fun _ => TopologicalSpace.isTopologicalBasis_opens)).exists_subset_of_mem_open
        hx hu
    obtain ⟨n, hn⟩ := Finset.bddAbove F
    let k := n + 1
    let w := boundaryPrefix k x
    refine ⟨cylinderSet k w, ⟨k, w, rfl⟩, ?_, ?_⟩
    · change boundaryPrefix k x = w
      rfl
    · intro y hy
      apply hvu
      intro i hiF
      have hi : i < k := (hn hiF).trans_lt (Nat.lt_succ_self n)
      have heq : y i = x i := by
        have hprefix := hy
        change boundaryPrefix k y = w at hprefix
        have hcoord := congrFun hprefix ⟨i, hi⟩
        simpa [w, boundaryPrefix] using hcoord
      rw [heq]
      have hxv' : x i ∈ V i := by
        have hxv'' : x ∈ (F : Set ℕ).pi V := hxv
        exact hxv'' i hiF
      exact hxv'

/-! The finite-cylinder carrier is closed under its algebra operations. -/

/-- Restrict an `m`-letter word to its first `n` letters. -/
def prefixTo (n m : ℕ) (h : n ≤ m) (w : BitWord m) : BitWord n :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

/-- Transport a finite diagonal observable to any later stage. -/
def diagEmbedTo (n m : ℕ) (h : n ≤ m) (f : DiagAlg n) : DiagAlg m :=
  fun w => f (prefixTo n m h w)

theorem boundaryPrefix_prefixTo (n m : ℕ) (h : n ≤ m) (x : CantorBoundary) :
    prefixTo n m h (boundaryPrefix m x) = boundaryPrefix n x := by
  ext i
  rfl

theorem cylinder_diagEmbedTo (n m : ℕ) (h : n ≤ m) (f : DiagAlg n) :
    cylinder m (diagEmbedTo n m h f) = cylinder n f := by
  funext x
  dsimp [cylinder, diagEmbedTo]
  rw [boundaryPrefix_prefixTo]

theorem cylinder_colimit_add {g h : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) (hh : h ∈ CylinderColimit) :
    g + h ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  rcases hh with ⟨⟨m, g⟩, rfl⟩
  let k := max n m
  let f' := diagEmbedTo n k (Nat.le_max_left n m) f
  let g' := diagEmbedTo m k (Nat.le_max_right n m) g
  refine ⟨⟨k, f' + g'⟩, ?_⟩
  change cylinder k (f' + g') = cylinder n f + cylinder m g
  rw [cylinder_add, cylinder_diagEmbedTo, cylinder_diagEmbedTo]

theorem cylinder_colimit_mul {g h : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) (hh : h ∈ CylinderColimit) :
    g * h ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  rcases hh with ⟨⟨m, g⟩, rfl⟩
  let k := max n m
  let f' := diagEmbedTo n k (Nat.le_max_left n m) f
  let g' := diagEmbedTo m k (Nat.le_max_right n m) g
  refine ⟨⟨k, f' * g'⟩, ?_⟩
  change cylinder k (f' * g') = cylinder n f * cylinder m g
  rw [cylinder_mul, cylinder_diagEmbedTo, cylinder_diagEmbedTo]

theorem cylinder_colimit_zero : (0 : CantorBoundary → ℂ) ∈ CylinderColimit := by
  exact ⟨⟨0, 0⟩, by ext x; rfl⟩

theorem cylinder_colimit_one : (1 : CantorBoundary → ℂ) ∈ CylinderColimit := by
  exact ⟨⟨0, 1⟩, by ext x; rfl⟩

theorem cylinder_colimit_algebraMap (c : ℂ) :
    algebraMap ℂ (CantorBoundary → ℂ) c ∈ CylinderColimit := by
  exact ⟨⟨0, constantStageObservable 0 c⟩, by ext x; change c = c; rfl⟩

/-- The finite-cylinder carrier as a native subalgebra of boundary functions. -/
def cylinderColimitSubalgebra : Subalgebra ℂ (CantorBoundary → ℂ) :=
  { carrier := CylinderColimit
    zero_mem' := cylinder_colimit_zero
    add_mem' := cylinder_colimit_add
    mul_mem' := cylinder_colimit_mul
    one_mem' := cylinder_colimit_one
    algebraMap_mem' := cylinder_colimit_algebraMap
  }

/-- View every finite-cylinder observable as a continuous function. -/
noncomputable def cylinderContinuousMap (g : cylinderColimitSubalgebra) :
    C(CantorBoundary, ℂ) :=
  { toFun := g.1
    continuous_toFun := cylinder_colimit_mem_continuous g.property }

@[simp] theorem cylinderContinuousMap_apply
    (g : cylinderColimitSubalgebra) (x : CantorBoundary) :
    cylinderContinuousMap g x = g.1 x := rfl

/-- The algebraic cylinder colimit embeds into the topological function algebra. -/
noncomputable def cylinderColimitToContinuousMap :
    cylinderColimitSubalgebra →ₐ[ℂ] C(CantorBoundary, ℂ) where
  toFun := cylinderContinuousMap
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl
  map_zero' := by
    ext x
    rfl
  map_add' g h := by
    ext x
    rfl
  commutes' c := by
    ext x
    rfl

theorem cylinderColimitToContinuousMap_injective :
    Function.Injective cylinderColimitToContinuousMap := by
  intro g h gh
  apply Subtype.ext
  funext x
  exact congrArg (fun k : C(CantorBoundary, ℂ) => k x) gh

/-! Star closure and topological density of the finite-cylinder image. -/

theorem cylinder_colimit_star {g : CantorBoundary → ℂ}
    (hg : g ∈ CylinderColimit) : star g ∈ CylinderColimit := by
  rcases hg with ⟨⟨n, f⟩, rfl⟩
  refine ⟨⟨n, fun w => star (f w)⟩, ?_⟩
  ext x
  rfl

def cylinderColimitStarSubalgebra :
    StarSubalgebra ℂ (CantorBoundary → ℂ) :=
  { toSubalgebra := cylinderColimitSubalgebra
    star_mem' := cylinder_colimit_star }

noncomputable def cylinderColimitToContinuousMapStarAlgHom :
    cylinderColimitStarSubalgebra →⋆ₐ[ℂ] C(CantorBoundary, ℂ) where
  toFun := fun g => cylinderContinuousMap ⟨g.1, g.property⟩
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl
  map_zero' := by
    ext x
    rfl
  map_add' g h := by
    ext x
    rfl
  commutes' c := by
    ext x
    rfl
  map_star' g := by
    ext x
    rfl

noncomputable def cylinderContinuousStarSubalgebra :
    StarSubalgebra ℂ C(CantorBoundary, ℂ) :=
  cylinderColimitToContinuousMapStarAlgHom.range

theorem cylinderContinuousStarSubalgebra_separatesPoints :
    cylinderContinuousStarSubalgebra.toSubalgebra.SeparatesPoints := by
  intro x y hxy
  obtain ⟨n, w, hx, hy⟩ := cylinderSet_separates hxy
  let f : DiagAlg n := fun v => if v = w then 1 else 0
  let g : cylinderColimitStarSubalgebra :=
    ⟨cylinder n f, cylinder_mem_colimit n f⟩
  let q := cylinderColimitToContinuousMapStarAlgHom g
  refine ⟨fun z => q z, ?_, ?_⟩
  · exact ⟨q, ⟨g, rfl⟩, rfl⟩
  · change f (boundaryPrefix n x) ≠ f (boundaryPrefix n y)
    change boundaryPrefix n x = w at hx
    change boundaryPrefix n y ≠ w at hy
    simp [f, hx, hy]

theorem cylinderContinuousStarSubalgebra_dense :
    cylinderContinuousStarSubalgebra.topologicalClosure = ⊤ := by
  exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    cylinderContinuousStarSubalgebra cylinderContinuousStarSubalgebra_separatesPoints

/-- The bundled finite-cylinder star homomorphism has dense range in the
    continuous functions on the product boundary.  This is the direct
    `DenseRange` form of the Stone--Weierstrass closure statement above. -/
theorem cylinderColimitToContinuousMapStarAlgHom_denseRange :
    DenseRange (cylinderColimitToContinuousMapStarAlgHom :
      cylinderColimitStarSubalgebra → C(CantorBoundary, ℂ)) := by
  rw [denseRange_iff_closure_range]
  have h := cylinderContinuousStarSubalgebra_dense
  have h' := congrArg (fun s : StarSubalgebra ℂ C(CantorBoundary, ℂ) =>
      (s : Set C(CantorBoundary, ℂ))) h
  change closure (↑cylinderContinuousStarSubalgebra) =
      (Set.univ : Set C(CantorBoundary, ℂ)) at h'
  simpa [cylinderContinuousStarSubalgebra] using h'

end InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
