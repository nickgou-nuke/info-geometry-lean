import Mathlib
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FractalCantorCliffordFockBridge

Theorem-safe bridge for the core chain:

* infinite binary Cantor boundary;
* finite binary cylinder refinement;
* Cuntz `O₂` branching and CAR readout;
* infinite Clifford/Fock witness packet;
* spectral-dimension / Hausdorff-calibration readout.

This file does not construct a new ultrametric on the Cantor boundary, nor
does it build the full infinite tensor product `Cl(1,1)^∞` analytically.  It
reuses the repo-owned boundary, Cuntz, Clifford, and Fock owner surfaces and
packages their theorem-safe consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.FractalCantorCliffordFockBridge

open InfoGeometry.Topology
open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-! ## 1. Boundary and cylinder carriers -/

/-- Infinite binary word space used as the symbolic Cantor boundary. -/
@[rep_depth operator]
abbrev InfiniteBinaryWordSpace := CantorBoundary

/-- Finite binary path codes used as Cantor cylinders. -/
@[rep_depth operator]
abbrev FiniteBinaryWord := TypeIIIModularCantorSystem.BinaryWord

/-- A canonical infinite binary boundary carrier. -/
@[rep_depth operator]
abbrev CantorBoundarySpace := InfiniteBinaryWordSpace

/-- The first boundary symbol readout. -/
@[rep_depth operator]
def boundaryHead (ξ : InfiniteBinaryWordSpace) : Bool :=
  ξ 0

/-- Prepend one binary symbol to an infinite boundary code. -/
@[rep_depth operator]
def boundaryCons (a : Bool) (ξ : InfiniteBinaryWordSpace) : InfiniteBinaryWordSpace :=
  fun n =>
    match n with
    | 0 => a
    | Nat.succ m => ξ m

/-- Remove the first binary symbol from an infinite boundary code. -/
@[rep_depth operator]
def boundaryTail (ξ : InfiniteBinaryWordSpace) : InfiniteBinaryWordSpace :=
  fun n => ξ (n + 1)

@[simp, rep_depth operator]
theorem boundaryHead_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) :
    boundaryHead (boundaryCons a ξ) = a := by
  rfl

@[simp, rep_depth operator]
theorem boundaryTail_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) :
    boundaryTail (boundaryCons a ξ) = ξ := by
  funext n
  rfl

/--
The infinite Cantor boundary decomposes recursively into its head symbol and
its tail.

This is the symbolic `n → ∞` carrier used by the Cantor/Fock lane.
-/
@[rep_depth operator]
theorem boundary_recursive_decomposition (ξ : InfiniteBinaryWordSpace) :
    ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := by
  funext n
  cases n <;> rfl

/-- Iterated tail extraction on the infinite binary boundary. -/
@[rep_depth operator]
def boundaryIterateTail : ℕ → InfiniteBinaryWordSpace → InfiniteBinaryWordSpace
  | 0, ξ => ξ
  | Nat.succ n, ξ => boundaryIterateTail n (boundaryTail ξ)

/-- Finite prefix extraction on the infinite binary boundary. -/
@[rep_depth operator]
def boundaryPrefix : ℕ → InfiniteBinaryWordSpace → List Bool
  | 0, _ => []
  | Nat.succ n, ξ => boundaryHead ξ :: boundaryPrefix n (boundaryTail ξ)

/-- Rebuild an infinite binary word from a finite prefix and a tail. -/
@[rep_depth operator]
def boundaryConsList : List Bool → InfiniteBinaryWordSpace → InfiniteBinaryWordSpace
  | [], ξ => ξ
  | b :: bs, ξ => boundaryCons b (boundaryConsList bs ξ)

@[simp, rep_depth operator]
theorem boundaryIterateTail_zero (ξ : InfiniteBinaryWordSpace) :
    boundaryIterateTail 0 ξ = ξ := by
  rfl

@[simp, rep_depth operator]
theorem boundaryIterateTail_succ (n : ℕ) (ξ : InfiniteBinaryWordSpace) :
    boundaryIterateTail (Nat.succ n) ξ = boundaryIterateTail n (boundaryTail ξ) := by
  rfl

@[simp, rep_depth operator]
theorem boundaryPrefix_zero (ξ : InfiniteBinaryWordSpace) :
    boundaryPrefix 0 ξ = [] := by
  rfl

@[simp, rep_depth operator]
theorem boundaryPrefix_succ (n : ℕ) (ξ : InfiniteBinaryWordSpace) :
    boundaryPrefix (Nat.succ n) ξ = boundaryHead ξ :: boundaryPrefix n (boundaryTail ξ) := by
  rfl

/-- Finite boundary prefixes have the expected length. -/
@[simp, rep_depth operator]
theorem boundaryPrefix_length (n : ℕ) (ξ : InfiniteBinaryWordSpace) :
    (boundaryPrefix n ξ).length = n := by
  induction n generalizing ξ with
  | zero => rfl
  | succ n ih =>
      simp [boundaryPrefix, ih]

/-- Prefixing a head symbol shifts the boundary prefix by one step. -/
@[simp, rep_depth operator]
theorem boundaryPrefix_succ_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) (n : ℕ) :
    boundaryPrefix (Nat.succ n) (boundaryCons a ξ) = a :: boundaryPrefix n ξ := by
  simp [boundaryPrefix, boundaryCons]

/-- Tail extraction after prefixing recovers the original boundary tail. -/
@[simp, rep_depth operator]
theorem boundaryIterateTail_succ_boundaryCons
    (a : Bool) (ξ : InfiniteBinaryWordSpace) (n : ℕ) :
    boundaryIterateTail (Nat.succ n) (boundaryCons a ξ) = boundaryIterateTail n ξ := by
  simp [boundaryIterateTail, boundaryCons]

@[simp, rep_depth operator]
theorem boundaryConsList_nil (ξ : InfiniteBinaryWordSpace) :
    boundaryConsList [] ξ = ξ := by
  rfl

@[simp, rep_depth operator]
theorem boundaryConsList_cons (b : Bool) (bs : List Bool) (ξ : InfiniteBinaryWordSpace) :
    boundaryConsList (b :: bs) ξ = boundaryCons b (boundaryConsList bs ξ) := by
  rfl

/-- Iterated boundary reconstruction from a finite prefix and the remaining tail. -/
@[rep_depth operator]
theorem boundary_iterated_decomposition :
    ∀ n (ξ : InfiniteBinaryWordSpace),
      ξ = boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ)
  | 0, ξ => by
      rfl
  | Nat.succ n, ξ => by
      calc
        ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := boundary_recursive_decomposition ξ
        _ = boundaryCons (boundaryHead ξ)
              (boundaryConsList (boundaryPrefix n (boundaryTail ξ))
                (boundaryIterateTail n (boundaryTail ξ))) := by
              congr
              exact boundary_iterated_decomposition n (boundaryTail ξ)
        _ = boundaryConsList (boundaryPrefix (Nat.succ n) ξ)
              (boundaryIterateTail (Nat.succ n) ξ) := by
              rfl

/--
The Cantor/Cuntz root branching and the infinite boundary recursion hold
together at the symbolic root.

This packages the finite Cuntz split with the `n → ∞` Cantor carrier without
claiming a new analytic infinite tensor product.
-/
@[rep_depth operator]
theorem cantorCuntz_root_branching
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op)
    (seed : Op)
    (ξ : InfiniteBinaryWordSpace) :
    (C.leftRangeProjection * seed +
      C.rightRangeProjection * seed = seed) ∧
      (ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ)) := by
  constructor
  · exact InfoGeometry.Canonical.CantorCuntzBasis.seed_branch_decomposition (C := C) (seed := seed)
  · exact boundary_recursive_decomposition ξ

/-- Finite boundary reconstruction is the theorem-backed crossing point into the limit carrier. -/
@[rep_depth operator]
theorem boundary_finite_reconstruction
    (n : ℕ) (ξ : InfiniteBinaryWordSpace) :
    ξ = boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) :=
  boundary_iterated_decomposition n ξ

/-- Boundary crossing witness with explicit prefix/tail fields. -/
@[rep_depth operator]
structure BoundaryCrossingWitness (n : ℕ) (ξ : InfiniteBinaryWordSpace) where
  pre : List Bool
  suf : InfiniteBinaryWordSpace
  reconstruction : ξ = boundaryConsList pre suf
  pre_eq : pre = boundaryPrefix n ξ
  suf_eq : suf = boundaryIterateTail n ξ

/-- Boundary crossing as a theorem-backed witness packet. -/
@[rep_depth operator]
theorem boundary_crossing_sorry
    (n : ℕ) (ξ : InfiniteBinaryWordSpace) :
    Nonempty (BoundaryCrossingWitness n ξ) := by
  refine ⟨⟨boundaryPrefix n ξ, boundaryIterateTail n ξ, ?_, rfl, rfl⟩⟩
  exact boundary_finite_reconstruction n ξ

/-- Re-export of the binary child map. -/
@[rep_depth operator]
def binaryChild (w : FiniteBinaryWord) (b : Bool) : FiniteBinaryWord :=
  BinaryWord.child w b

/-- Re-export of the binary closed cylinder. -/
@[rep_depth operator]
def binaryClosedCylinder (w : FiniteBinaryWord) : Set FiniteBinaryWord :=
  BinaryWord.closedCylinder w

@[simp, rep_depth operator]
theorem binaryWord_child_length (w : FiniteBinaryWord) (b : Bool) :
    (binaryChild w b).length = w.length + 1 := by
  simp [binaryChild, TypeIIIModularCantorSystem.BinaryWord.child]

@[simp, rep_depth operator]
theorem binaryWord_mem_closedCylinder_self (w : FiniteBinaryWord) :
    w ∈ binaryClosedCylinder w := by
  simpa [binaryClosedCylinder] using (TypeIIIModularCantorSystem.BinaryWord.mem_closedCylinder_self w)

@[rep_depth operator]
theorem binaryWord_closedCylinder_split (w : FiniteBinaryWord) :
    binaryClosedCylinder w =
      ({w} : Set FiniteBinaryWord)
        ∪ binaryClosedCylinder (binaryChild w false)
        ∪ binaryClosedCylinder (binaryChild w true) := by
  simpa [binaryClosedCylinder, binaryChild] using
    (TypeIIIModularCantorSystem.BinaryWord.closedCylinder_split w)

/-! ## 2. Hausdorff / spectral calibration readout -/

/--
The symbolic Hausdorff readout is carried by the Cuntz/Cantor spectral triple.

This is the repo-safe replacement for a literal metric instance on the infinite
binary boundary.
-/
@[rep_depth operator]
def cantorHausdorffReadout
    {Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (T : CuntzCantorSpectralTriple Op H) : ℝ :=
  T.spectralDimension

@[rep_depth operator]
theorem cantorHausdorffReadout_eq_middleThirdsCantor
    {Op H : Type*} [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H]
    (T : CuntzCantorSpectralTriple Op H) :
    cantorHausdorffReadout T = Real.log 2 / Real.log 3 := by
  simp [cantorHausdorffReadout, T.spectralDimension_eq_middleThirdsCantor]

/-! ## 3. Cuntz / CAR / Clifford readouts -/

/-- Re-export of the Cuntz range-projection partition of unity. -/
@[rep_depth operator]
theorem cuntz_rangeProjection_sum_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) :
    C.leftRangeProjection + C.rightRangeProjection = 1 :=
  C.rangeProjection_sum_one

/-- Re-export of the derived CAR nilpotency law. -/
@[rep_depth operator]
theorem carFromCuntz_sq_eq_zero
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    carFromCuntz C * carFromCuntz C = 0 :=
  InfoGeometry.Canonical.carFromCuntz_sq_eq_zero C

/-- Re-export of the derived CAR anticommutator law. -/
@[rep_depth operator]
theorem carFromCuntz_anticommutator_star_eq_one
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CantorCuntzO2Carrier Op) :
    cantorAnticommutator (carFromCuntz C) (star (carFromCuntz C)) = 1 :=
  InfoGeometry.Canonical.carFromCuntz_anticommutator_star_eq_one C

/-- Re-export of the infinite Clifford square law from the paper witness. -/
@[rep_depth operator]
theorem infiniteClifford_generator_sq
    {Op : Type*} [Ring Op]
    (C : RealDoubledCantorCliffordRepresentation Op) (i : ℕ) :
    C.gamma i * C.gamma i = 1 :=
  C.gamma_sq i

/-- Re-export of the infinite Clifford anticommutation law from the paper witness. -/
@[rep_depth operator]
theorem infiniteClifford_generator_anticomm
    {Op : Type*} [Ring Op]
    (C : RealDoubledCantorCliffordRepresentation Op) {i j : ℕ} (hij : i ≠ j) :
    C.gamma i * C.gamma j +
      C.gamma j * C.gamma i = 0 := by
  rw [C.gamma_anticomm (i := i) (j := j) hij]
  simp

/-- Re-export of the Hestenes/Krein structure-operator anticommutation law. -/
@[rep_depth operator]
theorem hestenes_structure_operator_anticommute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E)) =
      -((InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E))) :=
  InfoGeometry.Topology.FractalCantorFockWitness.hestenes_structure_operator_anticommute

/-- Re-export of the infinite `Cl(1,1)` generator readout as the structure operator. -/
@[rep_depth operator]
theorem cl11Rep_ι_zero_one_eq_structure_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Krein.cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = InfoGeometry.Krein.complex_i (E := E) :=
  InfoGeometry.Topology.FractalCantorFockWitness.cl11Rep_ι_zero_one_eq_structure_operator

/-! ## 4. Theorem surfaces -/

end FractalCantorCliffordFockBridge
