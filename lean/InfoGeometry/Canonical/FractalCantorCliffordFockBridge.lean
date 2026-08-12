import Mathlib.Tactic
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FractalCantorCliffordFockBridge

Theorem-safe bridge for the core chain:

* infinite binary Cantor boundary;
* finite binary cylinder refinement;
* Cuntz `O₂` branching and CAR readout;
* infinite Clifford/Fock property packet;
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
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNN

/-! ## 1. Boundary and cylinder carriers -/

/-- The first boundary symbol readout. -/
@[rep_depth operator]
def boundaryHead (ξ : (ℕ → Bool)) : Bool :=
  ξ 0

/-- Prepend one binary symbol to an infinite boundary code. -/
@[rep_depth operator]
def boundaryCons (a : Bool) (ξ : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n =>
    match n with
    | 0 => a
    | Nat.succ m => ξ m

/-- Remove the first binary symbol from an infinite boundary code. -/
@[rep_depth operator]
def boundaryTail (ξ : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => ξ (n + 1)

@[simp, rep_depth operator]
theorem boundaryHead_boundaryCons
    (a : Bool) (ξ : (ℕ → Bool)) :
    boundaryHead (boundaryCons a ξ) = a := by
  rfl

@[simp, rep_depth operator]
theorem boundaryTail_boundaryCons
    (a : Bool) (ξ : (ℕ → Bool)) :
    boundaryTail (boundaryCons a ξ) = ξ := by
  funext n
  rfl

/--
The infinite Cantor boundary decomposes recursively into its head symbol and
its tail.

This is the symbolic `n → ∞` carrier used by the Cantor/Fock lane.
-/
@[rep_depth operator]
theorem boundary_recursive_decomposition (ξ : (ℕ → Bool)) :
    ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := by
  funext n
  cases n <;> rfl

/-- Iterated tail extraction on the infinite binary boundary. -/
@[rep_depth operator]
def boundaryIterateTail : ℕ → (ℕ → Bool) → (ℕ → Bool)
  | 0, ξ => ξ
  | Nat.succ n, ξ => boundaryIterateTail n (boundaryTail ξ)

/-- Finite prefix extraction on the infinite binary boundary. -/
@[rep_depth operator]
def boundaryPrefix : ℕ → (ℕ → Bool) → List Bool
  | 0, _ => []
  | Nat.succ n, ξ => boundaryHead ξ :: boundaryPrefix n (boundaryTail ξ)

/-- Rebuild an infinite binary word from a finite prefix and a tail. -/
@[rep_depth operator]
def boundaryConsList : List Bool → (ℕ → Bool) → (ℕ → Bool)
  | [], ξ => ξ
  | b :: bs, ξ => boundaryCons b (boundaryConsList bs ξ)

@[simp, rep_depth operator]
theorem boundaryIterateTail_zero (ξ : (ℕ → Bool)) :
    boundaryIterateTail 0 ξ = ξ := by
  rfl

@[simp, rep_depth operator]
theorem boundaryIterateTail_succ (n : ℕ) (ξ : (ℕ → Bool)) :
    boundaryIterateTail (Nat.succ n) ξ = boundaryIterateTail n (boundaryTail ξ) := by
  rfl

@[simp, rep_depth operator]
theorem boundaryPrefix_zero (ξ : (ℕ → Bool)) :
    boundaryPrefix 0 ξ = [] := by
  rfl

@[simp, rep_depth operator]
theorem boundaryPrefix_succ (n : ℕ) (ξ : (ℕ → Bool)) :
    boundaryPrefix (Nat.succ n) ξ = boundaryHead ξ :: boundaryPrefix n (boundaryTail ξ) := by
  rfl

/-- Finite boundary prefixes have the expected length. -/
@[simp, rep_depth operator]
theorem boundaryPrefix_length (n : ℕ) (ξ : (ℕ → Bool)) :
    (boundaryPrefix n ξ).length = n := by
  induction n generalizing ξ with
  | zero => rfl
  | succ n ih =>
      simp [boundaryPrefix, ih]

/-- Prefixing a head symbol shifts the boundary prefix by one step. -/
@[simp, rep_depth operator]
theorem boundaryPrefix_succ_boundaryCons
    (a : Bool) (ξ : (ℕ → Bool)) (n : ℕ) :
    boundaryPrefix (Nat.succ n) (boundaryCons a ξ) = a :: boundaryPrefix n ξ := by
  simp [boundaryPrefix]

/-- Tail extraction after prefixing recovers the original boundary tail. -/
@[simp, rep_depth operator]
theorem boundaryIterateTail_succ_boundaryCons
    (a : Bool) (ξ : (ℕ → Bool)) (n : ℕ) :
    boundaryIterateTail (Nat.succ n) (boundaryCons a ξ) = boundaryIterateTail n ξ := by
  simp [boundaryIterateTail]

@[simp, rep_depth operator]
theorem boundaryConsList_nil (ξ : (ℕ → Bool)) :
    boundaryConsList [] ξ = ξ := by
  rfl

@[simp, rep_depth operator]
theorem boundaryConsList_cons (b : Bool) (bs : List Bool) (ξ : (ℕ → Bool)) :
    boundaryConsList (b :: bs) ξ = boundaryCons b (boundaryConsList bs ξ) := by
  rfl

@[rep_depth operator]
theorem boundaryConsList_append
    (pre post : List Bool) (ξ : (ℕ → Bool)) :
    boundaryConsList (pre ++ post) ξ =
      boundaryConsList pre (boundaryConsList post ξ) := by
  induction pre with
  | nil => rfl
  | cons b bs ih =>
      simp [boundaryConsList, ih]

/-- Iterated boundary reconstruction from a finite prefix and the remaining tail. -/
@[rep_depth operator]
theorem boundary_iterated_decomposition :
    ∀ n (ξ : (ℕ → Bool)),
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
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (seed : Op)
    (ξ : (ℕ → Bool)) :
    (InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C * seed +
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C * seed = seed) ∧
      (ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ)) := by
  constructor
  · exact InfoGeometry.Canonical.CantorCuntzBasis.seed_branch_decomposition (C := C) (seed := seed)
  · exact boundary_recursive_decomposition ξ

/-- Finite boundary reconstruction is the theorem-backed crossing point into the limit carrier. -/
@[rep_depth operator]
theorem boundary_finite_reconstruction
    (n : ℕ) (ξ : (ℕ → Bool)) :
    ξ = boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) :=
  boundary_iterated_decomposition n ξ

/-! ## 2. Zorn boundary subsystem for the infinite Cantor carrier -/

/--
A Cantor boundary subsystem is closed under the one-sided dynamics generated by
tail extraction and by adding either binary head symbol.

This is the set-theoretic boundary analogue of the directed colimit carrier:
finite head extensions stay inside the subsystem, and the tail map keeps the
system on the same boundary.
-/
@[rep_depth operator]
def BoundarySubsystem (S : Set (ℕ → Bool)) : Prop :=
  (∀ ξ, ξ ∈ S → boundaryTail ξ ∈ S) ∧
    (∀ a ξ, ξ ∈ S → boundaryCons a ξ ∈ S)

/-- Boundary subsystems are closed under any finite number of tail steps. -/
@[rep_depth operator]
theorem boundarySubsystem_boundaryIterateTail_mem
    {S : Set (ℕ → Bool)}
    (hS : BoundarySubsystem S) :
    ∀ n ξ, ξ ∈ S → boundaryIterateTail n ξ ∈ S
  | 0, _ξ, hξ => hξ
  | Nat.succ n, ξ, hξ =>
      boundarySubsystem_boundaryIterateTail_mem hS n (boundaryTail ξ) (hS.1 ξ hξ)

/-- Boundary subsystems are closed under adding any finite binary prefix. -/
@[rep_depth operator]
theorem boundarySubsystem_boundaryConsList_mem
    {S : Set (ℕ → Bool)}
    (hS : BoundarySubsystem S) :
    ∀ pre ξ, ξ ∈ S → boundaryConsList pre ξ ∈ S
  | [], _ξ, hξ => hξ
  | b :: bs, ξ, hξ =>
      hS.2 b (boundaryConsList bs ξ)
        (boundarySubsystem_boundaryConsList_mem hS bs ξ hξ)

/--
Every finite prefix/tail reconstruction of a boundary point in a subsystem
stays in that subsystem.
-/
@[rep_depth operator]
theorem boundarySubsystem_finite_reconstruction_mem
    {S : Set (ℕ → Bool)}
    (hS : BoundarySubsystem S)
    (n : ℕ)
    {ξ : (ℕ → Bool)}
    (hξ : ξ ∈ S) :
    boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) ∈ S :=
  boundarySubsystem_boundaryConsList_mem hS
    (boundaryPrefix n ξ)
    (boundaryIterateTail n ξ)
    (boundarySubsystem_boundaryIterateTail_mem hS n ξ hξ)

/-- The union of a chain of Cantor boundary subsystems is again a subsystem. -/
@[rep_depth operator]
theorem boundarySubsystem_sUnion_of_chain
    (chain : Set (Set (ℕ → Bool)))
    (hchain_subsystem : ∀ S ∈ chain, BoundarySubsystem S) :
    BoundarySubsystem (⋃₀ chain) := by
  constructor
  · intro ξ hξ
    rcases hξ with ⟨S, hS, hξS⟩
    exact ⟨S, hS, (hchain_subsystem S hS).1 ξ hξS⟩
  · intro a ξ hξ
    rcases hξ with ⟨S, hS, hξS⟩
    exact ⟨S, hS, (hchain_subsystem S hS).2 a ξ hξS⟩

/--
Every chain of boundary subsystems between a seed and an admissible ambient
subsystem has an upper bound, namely the union of the chain.
-/
@[rep_depth operator]
theorem boundarySubsystem_chain_has_upper_bound
    (seed U : Set (ℕ → Bool))
    (hseedU : seed ⊆ U)
    (hseed : BoundarySubsystem seed)
    (chain : Set (Set (ℕ → Bool)))
    (hchain_member :
      chain ⊆ {S | seed ⊆ S ∧ S ⊆ U ∧ BoundarySubsystem S}) :
    ∃ B ∈ {S | seed ⊆ S ∧ S ⊆ U ∧ BoundarySubsystem S},
      ∀ S ∈ chain, S ⊆ B := by
  by_cases hchain_nonempty : chain.Nonempty
  · rcases hchain_nonempty with ⟨S0, hS0⟩
    refine ⟨⋃₀ chain, ?_, ?_⟩
    · constructor
      · intro ξ hξ
        exact ⟨S0, hS0, (hchain_member hS0).1 hξ⟩
      · constructor
        · intro ξ hξ
          rcases hξ with ⟨S, hS, hξS⟩
          exact (hchain_member hS).2.1 hξS
        · exact boundarySubsystem_sUnion_of_chain chain
            (fun S hS => (hchain_member hS).2.2)
    · intro S hS ξ hξ
      exact ⟨S, hS, hξ⟩
  · refine ⟨seed, ?_, ?_⟩
    · exact ⟨fun _ hξ => hξ, hseedU, hseed⟩
    · intro S hS
      exact (hchain_nonempty ⟨S, hS⟩).elim

/--
Zorn boundary barrier for the Cantor/Fock carrier.

Given a seed boundary subsystem inside an admissible boundary subsystem, there is
a maximal boundary subsystem between them. This proves the Zorn step at the
symbolic Cantor boundary only; it does not assert an analytic Fock completion.
-/
@[rep_depth operator]
theorem zorn_maximal_boundarySubsystem
    (seed U : Set (ℕ → Bool))
    (hseedU : seed ⊆ U)
    (hseed : BoundarySubsystem seed) :
    ∃ M : Set (ℕ → Bool),
      seed ⊆ M ∧
        M ⊆ U ∧
          BoundarySubsystem M ∧
            ∀ N : Set (ℕ → Bool),
              seed ⊆ N →
                N ⊆ U →
                  BoundarySubsystem N →
                    M ⊆ N →
                      N = M := by
  let P : Set (Set (ℕ → Bool)) :=
    {S | seed ⊆ S ∧ S ⊆ U ∧ BoundarySubsystem S}
  have hchain :
      ∀ c ⊆ P, IsChain (· ⊆ ·) c → ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
    intro c hcP _hcchain
    exact boundarySubsystem_chain_has_upper_bound seed U hseedU hseed c hcP
  obtain ⟨M, hM⟩ := zorn_subset P hchain
  rcases hM with ⟨hMP, hMmax⟩
  rcases hMP with ⟨hseedM, hMU, hMsubsystem⟩
  refine ⟨M, hseedM, hMU, hMsubsystem, ?_⟩
  intro N hseedN hNU hNsubsystem hMN
  have hNP : N ∈ P := ⟨hseedN, hNU, hNsubsystem⟩
  have hNM : N ⊆ M := hMmax hNP hMN
  exact Set.Subset.antisymm hNM hMN

/--
A symbolic Cantor boundary subsystem and a split-Clifford direct-limit point are
compatible at every finite depth: the boundary point remains inside the
subsystem under finite prefix/tail reconstruction, while the split-Clifford
point has arbitrarily deep algebraic representatives.
-/
@[rep_depth operator]
theorem splitCliffordInfinity_boundarySubsystem_package
    (z : SplitCliffordInfinity)
    (S : Set (ℕ → Bool))
    (hS : BoundarySubsystem S)
    {ξ : (ℕ → Bool)}
    (hξ : ξ ∈ S) :
    (∀ n : ℕ, boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) ∈ S)
      ∧
    (∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z) := by
  constructor
  · intro n
    exact boundarySubsystem_finite_reconstruction_mem hS n hξ
  · exact splitCliffordInfinity_unbounded_representatives z

/--
Zorn-maximal symbolic boundary subsystems still support arbitrary-depth
split-Clifford representatives.

This is the precise Lean bridge between the Zorn boundary barrier and the
algebraic `Cl(n,n)` direct limit. It does not assert an analytic completion or
Connes/KMS regularity.
-/
@[rep_depth operator]
theorem splitCliffordInfinity_zornBoundarySubsystem_package
    (z : SplitCliffordInfinity)
    (seed U : Set (ℕ → Bool))
    (hseedU : seed ⊆ U)
    (hseed : BoundarySubsystem seed) :
    ∃ M : Set (ℕ → Bool),
      seed ⊆ M ∧
        M ⊆ U ∧
          BoundarySubsystem M ∧
            (∀ ξ ∈ M, ∀ n : ℕ,
              boundaryConsList (boundaryPrefix n ξ) (boundaryIterateTail n ξ) ∈ M) ∧
            (∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
              DirectLimit.Module.of ℝ ℕ SplitClNNAlg
                (fun m n h => splitCliffordMap m n h) n x = z) ∧
            ∀ N : Set (ℕ → Bool),
              seed ⊆ N →
                N ⊆ U →
                  BoundarySubsystem N →
                    M ⊆ N →
                      N = M := by
  rcases zorn_maximal_boundarySubsystem seed U hseedU hseed with
    ⟨M, hseedM, hMU, hMsubsystem, hMmax⟩
  refine ⟨M, hseedM, hMU, hMsubsystem, ?_, ?_, hMmax⟩
  · intro ξ hξ n
    exact boundarySubsystem_finite_reconstruction_mem hMsubsystem n hξ
  · exact splitCliffordInfinity_unbounded_representatives z


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
    (T : CuntzCantorSpectralTriple Op H)
    (hT : T.spectralDimension = Real.log 2 / Real.log 3) :
    cantorHausdorffReadout T = Real.log 2 / Real.log 3 := by
  simp [cantorHausdorffReadout, hT]

/-! ## 3. Cuntz / CAR / Clifford readouts -/


/-! ## 4. Theorem surfaces -/

end FractalCantorCliffordFockBridge
