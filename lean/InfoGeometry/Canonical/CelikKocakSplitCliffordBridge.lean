import InfoGeometry.Canonical.CelikKocakPaperFormalism
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
import InfoGeometry.Canonical.CantorCuntzCliffordBridge
import InfoGeometry.Topology.FractalCantorFockWitness
import InfoGeometry.Canonical.CelikKocakKreinSupergradedLift
import InfoGeometry.Canonical.CuntzMapKreinBridge
import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.CelikKocakSplitCliffordBridge

Theorem-backed bridge from the Çelik--Koçak Cantor tilt/switch lane to the
existing real split `Cl(n,n)` tower and the symbolic Cantor boundary recursion.

This file does not introduce a new infinite tensor-product model.  It packages
the already-owned theorem surfaces:

- the doubled real `Cl(1,1)` head atom,
- the recursive `Cl(n,n)` split step,
- the infinite binary boundary recursion.
-/

namespace InfoGeometry.Canonical.CelikKocakSplitCliffordBridge

open InfoGeometry.Canonical.CelikKocakPaperFormalism
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
open InfoGeometry.Quantum.RealMajoranaCategory
open InfoGeometry.Canonical.CelikKocakKreinSupergradedLift
open InfoGeometry.Canonical.CuntzMapKreinBridge
open InfoGeometry.Quantum
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Topology.FractalCantorFockWitness
open InfoGeometry.Krein
open KreinGradedModule

section RealSplit

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Head symbol of the Cantor boundary. -/
def boundaryHead (ξ : (ℕ → Bool)) : Bool :=
  ξ 0

/-- Prepend one bit to a Cantor boundary word. -/
def boundaryCons (a : Bool) (ξ : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n =>
    match n with
    | 0 => a
    | Nat.succ m => ξ m

/-- Tail of a Cantor boundary word. -/
def boundaryTail (ξ : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => ξ (n + 1)

theorem boundary_recursive_decomposition (ξ : (ℕ → Bool)) :
    ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := by
  funext n
  cases n <;> rfl

/-- The paper's left generator is the real split `J`-generator. -/
@[rep_depth krein]
theorem paperSplitClifford_tilt_eq_realJ :
    (doubledSpaceCl11Action (E := E)).J
      = InfoGeometry.Krein.modular_j (E := E) :=
  rfl

/-- The paper's right generator is the derived real phase axis `K = J ∘ ε`. -/
@[rep_depth krein]
theorem paperSplitClifford_switch_eq_realK :
    (doubledSpaceCl11Action (E := E)).K
      = InfoGeometry.Krein.complex_i (E := E) :=
  rfl

/-- The recursive split-tower step is the owned `Cl(n,n)` tensor transition. -/
@[rep_depth krein]
theorem splitClifford_recursive_transition_eq_owner (n : ℕ) :
    splitCliffordTensorRecursiveTransition (n := n)
      = splitCliffordTensorStepEquiv (n := n) :=
  rfl

/-- The head null pair is the real split CAR seed. -/
@[rep_depth krein]
theorem splitClifford_headNullPair_eq_seed (n : ℕ) :
    InfoGeometry.Clifford.ClNN.gammaHeadNullMinus n *
        InfoGeometry.Clifford.ClNN.gammaHeadNullPlus n
      + InfoGeometry.Clifford.ClNN.gammaHeadNullPlus n *
        InfoGeometry.Clifford.ClNN.gammaHeadNullMinus n = 1 :=
  InfoGeometry.Clifford.ClNN.gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n

/-- The head null pair stays isotropic in the recursive split tower. -/
@[rep_depth krein]
theorem splitClifford_headNullPair_isotropic (n : ℕ) :
    Quad (n + 1) (InfoGeometry.Clifford.ClNN.headNullMinus n) = 0 ∧
      Quad (n + 1) (InfoGeometry.Clifford.ClNN.headNullPlus n) = 0 := by
  exact ⟨InfoGeometry.Clifford.ClNN.headNullMinus_isotropic n,
    InfoGeometry.Clifford.ClNN.headNullPlus_isotropic n⟩

/-- The infinite Cantor boundary decomposes recursively into head and tail. -/
@[rep_depth operator]
theorem cantorBoundary_recursive_decomposition (ξ : (ℕ → Bool)) :
    ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) :=
  boundary_recursive_decomposition ξ

/--
The paper's finite split Clifford base, the recursive `Cl(n,n)` step, and the
infinite Cantor boundary recursion can be packaged together theorem-only.
-/
@[rep_depth operator]
theorem paperSplitClifford_limit_package
    (n : ℕ) (ξ : (ℕ → Bool)) :
    ((doubledSpaceCl11Action (E := E)).J = InfoGeometry.Krein.modular_j (E := E))
      ∧
    ((doubledSpaceCl11Action (E := E)).K = InfoGeometry.Krein.complex_i (E := E))
      ∧
    (splitCliffordTensorRecursiveTransition (n := n)
      = splitCliffordTensorStepEquiv (n := n))
      ∧
    (ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ)) := by
  constructor
  · exact paperSplitClifford_tilt_eq_realJ (E := E)
  · constructor
    · exact paperSplitClifford_switch_eq_realK (E := E)
    · constructor
      · exact splitClifford_recursive_transition_eq_owner (n := n)
      · exact cantorBoundary_recursive_decomposition ξ

/--
The split tower expands indefinitely and the Cantor boundary decomposes
recursively at the same time.
-/
@[rep_depth operator]
theorem paperSplitClifford_infiniteBoundary_package
    (z : SplitCliffordInfinity) (ξ : (ℕ → Bool)) :
    (∃ n x,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z ∧
      ∀ k : ℕ,
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (n + k)
          (splitCliffordMap n (n + k) (Nat.le_add_right n k) x) = z)
      ∧
      ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ) := by
  constructor
  · exact splitCliffordInfinity_boundary_expands z
  · exact boundary_recursive_decomposition ξ

end RealSplit

section InfiniteBoundary

variable {Op E : Type*} [Ring Op]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Every split direct-limit point has representatives at arbitrarily deep
levels.  The Fock carrier is independent data and is therefore not bundled
into this direct-limit theorem. -/
@[rep_depth operator]
theorem splitCliffordInfinity_boundary_complement
    (z : SplitCliffordInfinity) :
    ∀ N : ℕ, ∃ n ≥ N, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z := by
  intro N
  exact splitCliffordInfinity_unbounded_representatives z N

/--
The split infinite boundary and the concrete CAR property can be packaged
together without introducing any new infinite tensor product theorem.

The Cantor/Fock socket lives over a complex carrier `E`, while the concrete CAR
property lives over a real doubled carrier `F`; the theorem keeps those ambient
types separate.
-/
@[rep_depth operator]
theorem splitCliffordInfinity_fock_completion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    CARWitness (cl11CanonicalPolarizedMajorana (E := F)).core
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).annihil
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).create := by
  exact car_realization_of_clifford_concrete (E := F)

/-- The Cuntz binary legs still decompose the seed across the split boundary. -/
@[rep_depth operator]
theorem splitCliffordInfinity_leg_partition
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) (seed : Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * seed +
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * seed = seed := by
  calc
    ((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * seed + ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * seed
        = (((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) + ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))) * seed := by
            rw [add_mul]
    _ = 1 * seed := by
          rw [show ((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) + ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 1 from InfoGeometry.Topology.CuntzO2Carrier.rangeProjection_sum_one C]
    _ = seed := by
          simp

/-- The Cuntz binary legs remain orthogonal across the split boundary. -/
@[rep_depth operator]
theorem splitCliffordInfinity_leg_orthogonal
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) :
    (InfoGeometry.Topology.CuntzO2Carrier.S_left C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) *
      (InfoGeometry.Topology.CuntzO2Carrier.S_right C *
        star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 0 := by
  calc
    ((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C))
        = (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) := by
            simp [mul_assoc]
    _ = 0 := by
          rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).1]
          simp

/--
The split infinite boundary, the Cuntz root branch decomposition, and the
concrete CAR property can be packaged together in one theorem-backed packet.

This keeps the boundary expansion explicit using only the names already owned
in this file: the split direct-limit completion, the local binary boundary
recursion, and the Cuntz leg partition.
-/
@[rep_depth operator]
theorem splitCliffordInfinity_root_branch_completion
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (seed : Op)
    (ξ : (ℕ → Bool))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    (((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * seed + ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * seed = seed) ∧
      (((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = 0) ∧
      (ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ)) ∧
      CARWitness (cl11CanonicalPolarizedMajorana (E := F)).core
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).annihil
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).create := by
  constructor
  · exact splitCliffordInfinity_leg_partition (C := C) (seed := seed)
  · constructor
    · exact splitCliffordInfinity_leg_orthogonal (C := C)
    · constructor
      · exact boundary_recursive_decomposition ξ
      · exact car_realization_of_clifford_concrete (E := F)

/--
The theorem-backed Çelik--Koçak/Cuntz/CAR/Fock crossing packet.

This is the safe formal content behind the split-Fock/Cuntz-tree narrative:

* the split Clifford direct-limit point has arbitrarily deep representatives;
* the Cuntz carrier gives the CAR generator `S_left * S_right*`;
* a half-branch real readout is fixed by one Cuntz-map clock tick;
* the Cuntz range projections decompose the root seed;
* the Cantor boundary decomposes into head and tail;
* the concrete real doubled `Cl(1,1)` ladder satisfies CAR.

It deliberately does not assert a full `O₂ ≃ Cl(1,1)^{⊗∞}` isomorphism,
K-theory vanishing, complete positivity, or uniqueness of the KMS state.
-/
@[rep_depth operator]
theorem celikKocak_cuntzCAR_splitFock_fixedReadout_packet
    (z : SplitCliffordInfinity)
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)
    (φ : Op →+ ℝ)
    (X seed : Op)
    (ξ : (ℕ → Bool))
    (hleft : φ ((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) = (1 / 2 : ℝ) * φ X)
    (hright : φ ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * X * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) = (1 / 2 : ℝ) * φ X)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    (∃ n x,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z ∧
      ∀ k : ℕ,
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun m n h => splitCliffordMap m n h) (n + k)
          (splitCliffordMap n (n + k) (Nat.le_add_right n k) x) = z)
      ∧
      (_root_.InfoGeometry.Canonical.carFromCuntz C *
          _root_.InfoGeometry.Canonical.carFromCuntz C = 0)
      ∧
      (_root_.InfoGeometry.Canonical.cantorAnticommutator
          (_root_.InfoGeometry.Canonical.carFromCuntz C)
          (star (_root_.InfoGeometry.Canonical.carFromCuntz C)) = 1)
      ∧
      (φ (cuntzCarrierMap C X) = φ X)
      ∧
      (((InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C)) * seed +
          ((InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) * seed = seed)
      ∧
      (ξ = boundaryCons (boundaryHead ξ) (boundaryTail ξ))
      ∧
      CARWitness (cl11CanonicalPolarizedMajorana (E := F)).core
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).annihil
        (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := F))
          (cl11SplitCliffordDatum F) (cl11_concrete_ladder_realization (E := F))).create := by
  constructor
  · exact splitCliffordInfinity_boundary_expands z
  · constructor
    · exact _root_.InfoGeometry.Canonical.carFromCuntz_sq_eq_zero C
    · constructor
      · exact _root_.InfoGeometry.Canonical.carFromCuntz_anticommutator_star_eq_one C
      · constructor
        · exact cuntzCarrierMap_real_additive_readout_fixed_of_half_branch_scaling
            (C := C) (φ := φ) (X := X) hleft hright
        · constructor
          · exact splitCliffordInfinity_leg_partition (C := C) (seed := seed)
          · constructor
            · exact boundary_recursive_decomposition ξ
            · exact car_realization_of_clifford_concrete (E := F)

/--
The split boundary completion is compatible with the odd-sector supergraded
tilt/switch and Clifford readbacks already owned in the repository.

This is the theorem-backed bosonization-adjacent layer: it packages the finite
split boundary completion with the supercommutator/anticommutator identity on
odd generators, without introducing any new current algebra or Virasoro claim.
-/
@[rep_depth operator]
theorem splitCliffordInfinity_supergraded_completion
    (_z : SplitCliffordInfinity)
    (_D : CelikKocakInfiniteHilbertCarrier E)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] [KreinGradedModule H]
    (tiltSwitch : TiltSwitchSystem (H →L[ℝ] H))
    (clifford : RealDoubledCantorCliffordRepresentation (H →L[ℝ] H))
    (tiltOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.T p))
    (switchOdd : ∀ p : ℕ, IsOdd (H := H) (tiltSwitch.S p))
    (gammaOdd : ∀ i : ℕ, IsOdd (H := H) (clifford.gamma i))
    (p q i j : ℕ) :
    (superComm (H := H) (tiltSwitch.T p) (tiltSwitch.T q) =
        anticomm (tiltSwitch.T p) (tiltSwitch.T q)) ∧
      (superComm (H := H) (tiltSwitch.S p) (tiltSwitch.S q) =
        anticomm (tiltSwitch.S p) (tiltSwitch.S q)) ∧
      (superComm (H := H) (clifford.gamma i) (clifford.gamma j) =
        anticomm (clifford.gamma i) (clifford.gamma j)) := by
  constructor
  · exact tilt_superComm_eq_anticomm (H := H) (tiltSwitch := tiltSwitch) tiltOdd p q
  · constructor
    · exact switch_superComm_eq_anticomm (H := H) (tiltSwitch := tiltSwitch) switchOdd p q
    · exact gamma_superComm_eq_anticomm (H := H) (clifford := clifford) gammaOdd i j

end InfiniteBoundary

end InfoGeometry.Canonical.CelikKocakSplitCliffordBridge
