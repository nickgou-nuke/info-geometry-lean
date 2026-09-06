import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.l2Space
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Clifford.Lift
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace
open InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Topology.FractalCantorFock

Real Cantor-boundary Clifford/Fock analytic carrier.

Owner lane:

`Erlangen/binary boundary -> Cantor addresses -> tilt/switch operators ->
real doubled Hestenes/Krein Clifford representation -> Fock/CAR carrier`.

The tilt/switch operators are not identified with repository light-cone arrows
or Tomita mirror data by definition.  Those identifications are explicit
calibration data.

The metric graph embedding paper belongs to the finite metric graph-compression
lane, not to this Clifford/Fock carrier lane.
 -/

noncomputable section

open scoped InnerProductSpace

set_option linter.dupNamespace false

namespace InfoGeometry.Topology.FractalCantorFock

/-
Tilt/switch operator system.

`T p` is the tilt operator and `S p` is the switch operator.  The owner relation
is local anticommutation at the same address slot and commutation at distinct
slots.
-/
@[rep_depth operator]
structure TiltSwitchSystem
    (Op : Type*) [Ring Op] where
  T : ℕ → Op
  S : ℕ → Op

  T_sq :
    ∀ p, T p * T p = 1

  S_sq :
    ∀ p, S p * S p = 1

  T_comm :
    ∀ p q, T p * T q = T q * T p

  S_comm :
    ∀ p q, S p * S q = S q * S p

  T_S_comm_ne :
    ∀ p q, p ≠ q → T p * S q = S q * T p

  T_S_anticomm :
    ∀ p, T p * S p = - (S p * T p)

namespace TiltSwitchSystem

variable {Op : Type*} [Ring Op]
variable (TS : TiltSwitchSystem Op)

/-- Tilt squares to one at each Cantor address slot. -/
@[rep_depth operator]
theorem tilt_sq (p : ℕ) :
    TS.T p * TS.T p = 1 :=
  TS.T_sq p

/-- Switch squares to one at each Cantor address slot. -/
@[rep_depth operator]
theorem switch_sq (p : ℕ) :
    TS.S p * TS.S p = 1 :=
  TS.S_sq p

/-- Tilt and switch anticommute at the same slot. -/
@[rep_depth operator]
theorem tilt_switch_anticomm (p : ℕ) :
    TS.T p * TS.S p + TS.S p * TS.T p = 0 := by
  rw [TS.T_S_anticomm p]
  simp

/-- Tilt and switch commute at distinct slots. -/
@[rep_depth operator]
theorem tilt_switch_comm_of_ne {p q : ℕ} (hpq : p ≠ q) :
    TS.T p * TS.S q = TS.S q * TS.T p :=
  TS.T_S_comm_ne p q hpq

end TiltSwitchSystem

/--
Real doubled Hestenes/Krein Clifford representation generated from the
Cantor tilt/switch system.

`gamma i` is the image of the `i`-th Clifford generator.
-/
@[rep_depth operator]
structure RealDoubledCantorCliffordRepresentation
    (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op

  gamma : ℕ → Op

  gamma_sq :
    ∀ i, gamma i * gamma i = 1

  gamma_anticomm :
    ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

namespace RealDoubledCantorCliffordRepresentation

variable {Op : Type*} [Ring Op]
variable (C : RealDoubledCantorCliffordRepresentation Op)

end RealDoubledCantorCliffordRepresentation

namespace CantorBoundary

variable {j : ℕ}

/-- Flip the bit at a chosen boundary slot. -/
def flipAt (j : ℕ) (x : ℕ → Bool) : ℕ → Bool :=
  fun k => if k = j then ! (x k) else x k

@[simp] theorem flipAt_apply_eq (j : ℕ) (x : ℕ → Bool) :
    flipAt j x j = ! (x j) := by
  simp [flipAt]

@[simp] theorem flipAt_apply_ne {j k : ℕ} (h : k ≠ j) (x : ℕ → Bool) :
    flipAt j x k = x k := by
  simp [flipAt, h]

theorem flipAt_involutive (j : ℕ) (x : ℕ → Bool) :
    flipAt j (flipAt j x) = x := by
  funext k
  by_cases hk : k = j <;> simp [flipAt, hk, Bool.not_not]

theorem flipAt_comm {i j : ℕ} (hij : i ≠ j) (x : ℕ → Bool) :
    flipAt i (flipAt j x) = flipAt j (flipAt i x) := by
  funext k
  by_cases hki : k = i
  · by_cases hji : i = j
    · exact False.elim (hij hji)
    · simp [flipAt, hki, hji]
  · by_cases hkj : k = j
    · have hji : j ≠ i := by
        intro h
        apply hki
        rw [hkj, h]
      simp [flipAt, hkj, hji]
    · simp [flipAt, hki, hkj]

end CantorBoundary

namespace CantorBoundaryFunctionSpace

open CantorBoundary

variable {j : ℕ}

/-- Tilt operator on infinite boundary functions. -/
def tilt (j : ℕ) : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) where
  toFun f := fun x => if x j then -f x else f x
  map_add' := by
    intro f g
    ext x
    by_cases hx : x j <;> simp [hx, add_comm]
  map_smul' := by
    intro c f
    ext x
    by_cases hx : x j <;> simp [hx]

/-- Switch operator on infinite boundary functions. -/
def switch (j : ℕ) : ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ) where
  toFun f := fun x => f (CantorBoundary.flipAt j x)
  map_add' := by
    intro f g
    ext x
    rfl
  map_smul' := by
    intro c f
    ext x
    rfl

@[simp] theorem tilt_apply (j : ℕ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) :
    tilt j f x = if x j then -f x else f x :=
  rfl

@[simp] theorem switch_apply (j : ℕ) (f : (ℕ → Bool) → ℝ) (x : ℕ → Bool) :
    switch j f x = f (CantorBoundary.flipAt j x) :=
  rfl

/-- Tilt squares to the identity. -/
theorem tilt_sq (j : ℕ) :
    (tilt j) * (tilt j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, hx]

/-- Switch squares to the identity. -/
theorem switch_sq (j : ℕ) :
    (switch j) * (switch j) = 1 := by
  apply LinearMap.ext
  intro f
  ext x
  simpa using congrArg f (CantorBoundary.flipAt_involutive j x)

/-- Tilt operators commute at distinct slots. -/
theorem tilt_comm {i j : ℕ} :
    (tilt i) * (tilt j) = (tilt j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;> by_cases hxj : x j <;> simp [tilt, hxi, hxj]

/-- Switch operators commute at distinct slots. -/
theorem switch_comm {i j : ℕ} (hij : i ≠ j) :
    (switch i) * (switch j) = (switch j) * (switch i) := by
  apply LinearMap.ext
  intro f
  ext x
  simp [switch, CantorBoundary.flipAt_comm hij]

/-- Tilt and switch commute at different slots. -/
theorem tilt_switch_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    (tilt i) * (switch j) = (switch j) * (tilt i) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hxi : x i <;>
    simp [tilt, switch, CantorBoundary.flipAt_apply_ne hij, hxi]

theorem switch_tilt_comm_of_ne {i j : ℕ} (hij : i ≠ j) :
    (switch i) * (tilt j) = (tilt j) * (switch i) := by
  exact (tilt_switch_comm_of_ne (i := j) (j := i) hij.symm).symm

/-- Tilt and switch anticommute at the same slot. -/
theorem tilt_switch_anticomm (j : ℕ) :
    (tilt j) * (switch j) = - ((switch j) * (tilt j)) := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;> simp [tilt, switch, CantorBoundary.flipAt, hx]

theorem tilt_switch_anticommutator_eq_zero (j : ℕ) :
    (tilt j) * (switch j) + (switch j) * (tilt j) = 0 := by
  rw [tilt_switch_anticomm]
  simp

theorem switch_tilt_anticomm (j : ℕ) :
    (switch j) * (tilt j) = - ((tilt j) * (switch j)) := by
  rw [tilt_switch_anticomm]
  simp

theorem tilt_switch_product_sq (j : ℕ) :
    ((tilt j) * (switch j)) * ((tilt j) * (switch j)) = -1 := by
  apply LinearMap.ext
  intro f
  ext x
  by_cases hx : x j <;>
    simp [tilt, switch, CantorBoundary.flipAt, hx,
      CantorBoundary.flipAt_involutive]

theorem switch_conj_tilt_same (j : ℕ) :
    (switch j) * (tilt j) * (switch j) = -(tilt j) := by
  calc
    (switch j) * (tilt j) * (switch j) =
        -((tilt j) * (switch j)) * (switch j) := by
          rw [switch_tilt_anticomm]
    _ = -(((tilt j) * (switch j)) * (switch j)) := by
          exact neg_mul ((tilt j) * (switch j)) (switch j)
    _ = -((tilt j) * ((switch j) * (switch j))) := by
          rw [mul_assoc]
    _ = -(tilt j) := by
          rw [switch_sq]
          simp

theorem switch_conj_tilt_ne {i j : ℕ} (hij : i ≠ j) :
    (switch i) * (tilt j) * (switch i) = tilt j := by
  calc
    (switch i) * (tilt j) * (switch i) =
        (tilt j) * (switch i) * (switch i) := by
          rw [switch_tilt_comm_of_ne hij]
    _ = (tilt j) * ((switch i) * (switch i)) := by
          rw [← mul_assoc]
    _ = tilt j := by
          rw [switch_sq]
          simp

theorem tilt_conj_switch_same (j : ℕ) :
    (tilt j) * (switch j) * (tilt j) = -(switch j) := by
  calc
    (tilt j) * (switch j) * (tilt j) =
        -((switch j) * (tilt j)) * (tilt j) := by
          rw [tilt_switch_anticomm]
    _ = -(((switch j) * (tilt j)) * (tilt j)) := by
          exact neg_mul ((switch j) * (tilt j)) (tilt j)
    _ = -((switch j) * ((tilt j) * (tilt j))) := by
          rw [mul_assoc]
    _ = -(switch j) := by
          rw [tilt_sq]
          simp

theorem tilt_conj_switch_ne {i j : ℕ} (hij : i ≠ j) :
    (tilt i) * (switch j) * (tilt i) = switch j := by
  calc
    (tilt i) * (switch j) * (tilt i) =
        (switch j) * (tilt i) * (tilt i) := by
          rw [tilt_switch_comm_of_ne hij]
    _ = (switch j) * ((tilt i) * (tilt i)) := by
          rw [← mul_assoc]
    _ = switch j := by
          rw [tilt_sq]
          simp

/-- The canonical infinite Cantor tilt/switch system. -/
def canonicalTiltSwitchSystem :
    TiltSwitchSystem (((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)) where
  T := tilt
  S := switch
  T_sq := tilt_sq
  S_sq := switch_sq
  T_comm := by
    intro i j
    exact tilt_comm (i := i) (j := j)
  S_comm := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · exact switch_comm hij
  T_S_comm_ne := by
    intro i j hij
    exact tilt_switch_comm_of_ne hij
  T_S_anticomm := by
    intro j
    exact tilt_switch_anticomm j

/-! ## Canonical local `Cl(1,1)` product -/

theorem canonical_tilt_switch_product_sq (j : ℕ) :
    ((tilt j) * (switch j)) * ((tilt j) * (switch j)) = -1 := by
  exact tilt_switch_product_sq j

theorem canonical_tilt_switch_product_right_inverse (j : ℕ) :
    (tilt j) * (switch j) * (-((tilt j) * (switch j))) = 1 := by
  calc
    (tilt j) * (switch j) * (-((tilt j) * (switch j))) =
        -(((tilt j) * (switch j)) * ((tilt j) * (switch j))) := by
          exact mul_neg ((tilt j) * (switch j)) ((tilt j) * (switch j))
    _ = 1 := by
      rw [canonical_tilt_switch_product_sq]
      simp

theorem canonical_tilt_switch_product_left_inverse (j : ℕ) :
    (-((tilt j) * (switch j))) * ((tilt j) * (switch j)) = 1 := by
  calc
    (-((tilt j) * (switch j))) * ((tilt j) * (switch j)) =
        -(((tilt j) * (switch j)) * ((tilt j) * (switch j))) := by
          exact neg_mul ((tilt j) * (switch j)) ((tilt j) * (switch j))
    _ = 1 := by
      rw [canonical_tilt_switch_product_sq]
      simp

end CantorBoundaryFunctionSpace

/--
Infinite-dimensional Cantor/Cuntz orbit carrier.

This is the analytic substrate for the later orbit/basis theorems: a Cuntz
carrier, a distinguished seed vector, and explicit left/right branch actions
with a recursively defined orbit.
-/
@[rep_depth operator]
structure CelikKocakInfiniteFockCarrier
    (Op : Type*) [Ring Op] [StarRing Op]
    [NormedAddCommGroup Op] [NormedSpace ℂ Op] [CompleteSpace Op] where
  cuntz : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op
  seedVector : Op
  leftBranch : Op →L[ℂ] Op
  rightBranch : Op →L[ℂ] Op
  orbit : List Bool → Op
  orbit_root_eq_seed :
    orbit [] = seedVector
  orbit_cons_false_action :
    ∀ w, orbit (false :: w) = leftBranch (orbit w)
  orbit_cons_true_action :
    ∀ w, orbit (true :: w) = rightBranch (orbit w)

namespace CelikKocakInfiniteFockCarrier

variable {Op : Type*} [Ring Op] [StarRing Op]
variable [NormedAddCommGroup Op] [NormedSpace ℂ Op] [CompleteSpace Op]
variable (C : CelikKocakInfiniteFockCarrier Op)

/-- The orbit at the empty word is the seed vector. -/
@[rep_depth operator]
theorem orbit_root (C : CelikKocakInfiniteFockCarrier Op) :
    C.orbit [] = C.seedVector :=
  C.orbit_root_eq_seed

/-- Left-branch recursion for a false child word. -/
@[rep_depth operator]
theorem orbit_cons_false (C : CelikKocakInfiniteFockCarrier Op) (w : List Bool) :
    C.orbit (false :: w) = C.leftBranch (C.orbit w) :=
  C.orbit_cons_false_action w

/-- Right-branch recursion for a true child word. -/
@[rep_depth operator]
theorem orbit_cons_true (C : CelikKocakInfiniteFockCarrier Op) (w : List Bool) :
    C.orbit (true :: w) = C.rightBranch (C.orbit w) :=
  C.orbit_cons_true_action w

/-- Unified orbit action law. -/
@[rep_depth operator]
theorem orbit_action (C : CelikKocakInfiniteFockCarrier Op) (b : Bool) (w : List Bool) :
    C.orbit (b :: w) =
      (if b then C.rightBranch else C.leftBranch) (C.orbit w) := by
  cases b <;> simp [C.orbit_cons_false, C.orbit_cons_true]

@[rep_depth operator]
theorem orbit_eq_foldr (C : CelikKocakInfiniteFockCarrier Op) (w : List Bool) :
    C.orbit w =
      List.foldr
        (fun b x => if b then C.rightBranch x else C.leftBranch x)
        C.seedVector w := by
  induction w with
  | nil => simp [C.orbit_root]
  | cons b w ih =>
      rw [C.orbit_action b w, ih]
      cases b <;> rfl

@[rep_depth operator]
theorem orbit_append (C : CelikKocakInfiniteFockCarrier Op)
    (w v : List Bool) :
    C.orbit (w ++ v) =
      List.foldr
        (fun b x => if b then C.rightBranch x else C.leftBranch x)
        (C.orbit v) w := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [List.cons_append, C.orbit_action b (w ++ v), ih]
      cases b <;> rfl

/-- Root seed readback. -/
@[rep_depth operator]
theorem seed_vector_eq_orbit_root (C : CelikKocakInfiniteFockCarrier Op) :
    C.seedVector = C.orbit [] := by
  symm
  exact C.orbit_root

end CelikKocakInfiniteFockCarrier

/--
Infinite-dimensional Hilbert carrier for the Cantor orbit basis.

This is the theorem-backed analytic layer: a Hilbert basis indexed by binary
words, with orthogonality and completeness inherited from mathlib.
-/
@[rep_depth operator]
structure CelikKocakInfiniteHilbertCarrier
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  orbitBasis : HilbertBasis (List Bool) ℂ E

namespace CelikKocakInfiniteHilbertCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Construct the Hilbert carrier from a Hilbert basis property. -/
@[rep_depth operator]
def ofHilbertBasis (b : HilbertBasis (List Bool) ℂ E) :
    CelikKocakInfiniteHilbertCarrier E :=
  ⟨b⟩

@[simp, rep_depth operator]
theorem ofHilbertBasis_orbitBasis (b : HilbertBasis (List Bool) ℂ E) :
    (ofHilbertBasis (E := E) b).orbitBasis = b :=
  rfl

variable (H : CelikKocakInfiniteHilbertCarrier E)

/-- The Hilbert carrier is orthonormal. -/
@[rep_depth operator]
theorem orbit_orthonormal :
    Orthonormal ℂ H.orbitBasis := by
  exact H.orbitBasis.orthonormal

/-- The Hilbert carrier is complete. -/
@[rep_depth operator]
theorem orbit_complete :
    (Submodule.span ℂ (Set.range H.orbitBasis)).topologicalClosure = ⊤ := by
  exact H.orbitBasis.dense_span

/-- Distinct orbit words are orthogonal. -/
@[rep_depth operator]
theorem orbit_orthogonal_of_distinct_words {w v : List Bool} (h : w ≠ v) :
    ⟪H.orbitBasis w, H.orbitBasis v⟫_ℂ = 0 := by
  exact H.orbitBasis.orthonormal.inner_eq_zero h

/-- The basis coefficient readback is the inner-product formula. -/
@[rep_depth operator]
theorem orbit_basis_repr_apply (x : E) (w : List Bool) :
    H.orbitBasis.repr x w = ⟪H.orbitBasis w, x⟫_ℂ := by
  exact H.orbitBasis.repr_apply_apply x w

end CelikKocakInfiniteHilbertCarrier

namespace CelikKocakInfiniteFockCarrierData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (D : CelikKocakInfiniteHilbertCarrier E)

/-- The analytic Cantor orbit basis is orthonormal. -/
@[rep_depth operator]
theorem orbit_orthonormal :
    Orthonormal ℂ D.orbitBasis :=
  CelikKocakInfiniteHilbertCarrier.orbit_orthonormal D

/-- The analytic Cantor orbit basis is complete. -/
@[rep_depth operator]
theorem orbit_complete :
    (Submodule.span ℂ (Set.range D.orbitBasis)).topologicalClosure = ⊤ :=
  CelikKocakInfiniteHilbertCarrier.orbit_complete D

/-- The analytic Cantor orbit basis is cyclic. -/
@[rep_depth operator]
theorem orbit_cyclic :
    ⊤ ≤ (Submodule.span ℂ (Set.range D.orbitBasis)).topologicalClosure := by
  exact le_of_eq (D.orbit_complete.symm)

/-- Distinct words are orthogonal in the carrier data. -/
@[rep_depth operator]
theorem orbit_orthogonal_of_distinct_words {w v : List Bool} (h : w ≠ v) :
    ⟪D.orbitBasis w, D.orbitBasis v⟫_ℂ = 0 :=
  CelikKocakInfiniteHilbertCarrier.orbit_orthogonal_of_distinct_words D h

/-- Basis coefficient readback on the carrier data. -/
@[rep_depth operator]
theorem orbit_basis_repr_apply (x : E) (w : List Bool) :
    D.orbitBasis.repr x w = ⟪D.orbitBasis w, x⟫_ℂ :=
  CelikKocakInfiniteHilbertCarrier.orbit_basis_repr_apply D x w

end CelikKocakInfiniteFockCarrierData

/--
The Hestenes/Krein structure operator is the infinite-lane odd generator,
not the scalar complex unit.
-/
@[rep_depth operator]
theorem hestenes_structure_operator_anticommute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    (InfoGeometry.Krein.modular_j (E := E)).comp (InfoGeometry.Krein.complex_i (E := E)) =
      -((InfoGeometry.Krein.complex_i (E := E)).comp (InfoGeometry.Krein.modular_j (E := E))) :=
  InfoGeometry.Clifford.Lift.modular_j_complex_i_anticommute (E := E)

/-- The infinite `Cl(1,1)` generator at `(0,1)` is the structure operator. -/
@[rep_depth operator]
theorem cl11Rep_ι_zero_one_eq_structure_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Krein.cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1))
      = InfoGeometry.Krein.complex_i (E := E) :=
  InfoGeometry.Clifford.Lift.cl11Rep_ι_zero_one (E := E)

/--
Finite-dimensional Cantor-Pauli property over a real/doubled matrix carrier.

The representation on endpoint functions agrees with the real Pauli tensor lane
through an explicit property.
-/
theorem finite_cantor_pauli_generator_sq
    {n : ℕ} {Mat : Type*} [Ring Mat]
    (psiGamma : Fin (2 * n) → Mat)
    (gamma_sq : ∀ i, psiGamma i * psiGamma i = 1)
    (i : Fin (2 * n)) :
    psiGamma i * psiGamma i = 1 :=
  gamma_sq i

theorem finite_cantor_pauli_generator_anticomm
    {n : ℕ} {Mat : Type*} [Ring Mat]
    (psiGamma : Fin (2 * n) → Mat)
    (gamma_anticomm :
      ∀ i j, i ≠ j → psiGamma i * psiGamma j = -(psiGamma j * psiGamma i))
    {i j : Fin (2 * n)} (hij : i ≠ j) :
    psiGamma i * psiGamma j + psiGamma j * psiGamma i = 0 := by
  rw [gamma_anticomm i j hij]
  simp

/--
Real CAR pair.

This is the interface consumed by light-cone/Fock layers.
-/
@[rep_depth operator]
structure RealCARPair
    (Op : Type*) [Ring Op] where
  annihilation : Op
  creation : Op

  nilpotent_annihilation :
    annihilation * annihilation = 0

  nilpotent_creation :
    creation * creation = 0

  car :
    annihilation * creation + creation * annihilation = 1

namespace RealCARPair

variable {Op : Type*} [Ring Op]
variable (C : RealCARPair Op)

/-- Annihilation is nilpotent. -/
@[rep_depth operator]
theorem annihilation_sq_zero :
    C.annihilation * C.annihilation = 0 :=
  C.nilpotent_annihilation

/-- Creation is nilpotent. -/
@[rep_depth operator]
theorem creation_sq_zero :
    C.creation * C.creation = 0 :=
  C.nilpotent_creation

/-- Canonical CAR anticommutator law. -/
@[rep_depth operator]
theorem anticommutator_eq_one :
    C.annihilation * C.creation + C.creation * C.annihilation = 1 :=
  C.car

theorem annihilation_creation_idempotent :
    (C.annihilation * C.creation) *
      (C.annihilation * C.creation) =
      C.annihilation * C.creation := by
  have hca : C.creation * C.annihilation =
      1 - C.annihilation * C.creation := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using C.car
  calc
    (C.annihilation * C.creation) *
        (C.annihilation * C.creation) =
        C.annihilation * (C.creation * C.annihilation) * C.creation := by
          simp [mul_assoc]
    _ = C.annihilation * (1 - C.annihilation * C.creation) * C.creation := by
          rw [hca]
    _ = C.annihilation * C.creation := by
          simp [mul_assoc, sub_mul, mul_sub, C.nilpotent_creation]

theorem creation_annihilation_idempotent :
    (C.creation * C.annihilation) *
      (C.creation * C.annihilation) =
      C.creation * C.annihilation := by
  have hac : C.annihilation * C.creation =
      1 - C.creation * C.annihilation := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using C.car
  calc
    (C.creation * C.annihilation) *
        (C.creation * C.annihilation) =
        C.creation * (C.annihilation * C.creation) * C.annihilation := by
          simp [mul_assoc]
    _ = C.creation * (1 - C.creation * C.annihilation) * C.annihilation := by
          rw [hac]
    _ = C.creation * C.annihilation := by
          simp [mul_assoc, sub_mul, mul_sub, C.nilpotent_annihilation]

theorem annihilation_creation_orthogonal :
    (C.annihilation * C.creation) *
      (C.creation * C.annihilation) = 0 := by
  calc
    (C.annihilation * C.creation) *
        (C.creation * C.annihilation) =
        C.annihilation * (C.creation * C.creation) * C.annihilation := by
          simp [mul_assoc]
    _ = 0 := by simp [C.nilpotent_creation]

theorem creation_annihilation_orthogonal :
    (C.creation * C.annihilation) *
      (C.annihilation * C.creation) = 0 := by
  calc
    (C.creation * C.annihilation) *
        (C.annihilation * C.creation) =
        C.creation * (C.annihilation * C.annihilation) * C.creation := by
          simp [mul_assoc]
    _ = 0 := by simp [C.nilpotent_annihilation]

theorem creation_annihilation_eq_one_sub_annihilation_creation :
    C.creation * C.annihilation =
      1 - C.annihilation * C.creation := by
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using C.car

theorem annihilation_creation_eq_one_sub_creation_annihilation :
    C.annihilation * C.creation =
      1 - C.creation * C.annihilation := by
  apply eq_sub_iff_add_eq.mpr
  simpa [add_comm] using C.car

end RealCARPair

namespace CantorBoundaryFunctionSpace

abbrev Operator := ((ℕ → Bool) → ℝ) →ₗ[ℝ] ((ℕ → Bool) → ℝ)

noncomputable def canonicalAnnihilation (j : ℕ) : Operator :=
  (1 / 2 : ℝ) • (tilt j + (tilt j) * (switch j))

noncomputable def canonicalCreation (j : ℕ) : Operator :=
  (1 / 2 : ℝ) • (tilt j - (tilt j) * (switch j))

private theorem tilt_mul_tilt_switch (j : ℕ) :
    (tilt j) * ((tilt j) * (switch j)) = switch j := by
  rw [← mul_assoc, tilt_sq]
  simp

private theorem tilt_switch_mul_tilt (j : ℕ) :
    ((tilt j) * (switch j)) * (tilt j) = -(switch j) := by
  calc
    ((tilt j) * (switch j)) * (tilt j) =
        (tilt j) * ((switch j) * (tilt j)) := by rw [mul_assoc]
    _ = (tilt j) * (-((tilt j) * (switch j))) := by
      rw [switch_tilt_anticomm]
    _ = -((tilt j) * ((tilt j) * (switch j))) := by
      exact @mul_neg Operator _ _ (tilt j) ((tilt j) * (switch j))
    _ = -(switch j) := by rw [tilt_mul_tilt_switch]

theorem canonicalAnnihilation_sq (j : ℕ) :
    canonicalAnnihilation j * canonicalAnnihilation j = 0 := by
  simp only [canonicalAnnihilation, smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, tilt_sq, tilt_switch_product_sq,
    tilt_mul_tilt_switch, tilt_switch_mul_tilt]
  module

theorem canonicalCreation_sq (j : ℕ) :
    canonicalCreation j * canonicalCreation j = 0 := by
  simp only [canonicalCreation, smul_mul_assoc, mul_smul_comm,
    mul_sub, sub_mul, tilt_sq, tilt_switch_product_sq,
    tilt_mul_tilt_switch, tilt_switch_mul_tilt]
  module

theorem canonicalCAR_anticommutator (j : ℕ) :
    canonicalAnnihilation j * canonicalCreation j +
      canonicalCreation j * canonicalAnnihilation j = 1 := by
  simp only [canonicalAnnihilation, canonicalCreation, smul_mul_assoc,
    mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul,
    tilt_sq, tilt_switch_product_sq, tilt_mul_tilt_switch,
    tilt_switch_mul_tilt]
  module

noncomputable def canonicalCARPair (j : ℕ) : RealCARPair Operator where
  annihilation := canonicalAnnihilation j
  creation := canonicalCreation j
  nilpotent_annihilation := canonicalAnnihilation_sq j
  nilpotent_creation := canonicalCreation_sq j
  car := canonicalCAR_anticommutator j

end CantorBoundaryFunctionSpace

/--
Clifford-to-CAR calibration.

This explicitly records that a selected Clifford pair from the Cantor
representation supplies the CAR pair required by the light-cone/Fock interface.
-/
@[rep_depth operator]
structure CliffordToCARCalibration
    (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  clifford : RealDoubledCantorCliffordRepresentation Op
  gammaAIndex : ℕ
  gammaBIndex : ℕ
  gamma_indices_ne : gammaAIndex ≠ gammaBIndex

namespace CliffordToCARCalibration

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable (W : CliffordToCARCalibration Op)

/-- The first selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
def gammaA : Op :=
  W.clifford.gamma W.gammaAIndex

/-- The second selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
def gammaB : Op :=
  W.clifford.gamma W.gammaBIndex

/-- The first selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
theorem gammaA_generator :
    W.gammaA = W.clifford.gamma W.gammaAIndex :=
  rfl

/-- The second selected CAR seed is a Clifford generator image. -/
@[rep_depth operator]
theorem gammaB_generator :
    W.gammaB = W.clifford.gamma W.gammaBIndex :=
  rfl

private theorem gammaA_sq :
    W.gammaA * W.gammaA = 1 :=
  W.clifford.gamma_sq W.gammaAIndex

private theorem gammaB_sq :
    W.gammaB * W.gammaB = 1 :=
  W.clifford.gamma_sq W.gammaBIndex

private theorem gammaA_gammaB_anticomm :
    W.gammaA * W.gammaB = -(W.gammaB * W.gammaA) :=
  W.clifford.gamma_anticomm W.gammaAIndex W.gammaBIndex W.gamma_indices_ne

private theorem gammaB_gammaA_anticomm :
    W.gammaB * W.gammaA = -(W.gammaA * W.gammaB) := by
  calc
    W.gammaB * W.gammaA = -(- (W.gammaB * W.gammaA)) := by simp
    _ = -(W.gammaA * W.gammaB) := by rw [gammaA_gammaB_anticomm]

/-- The product of the two selected Clifford generators is the real phase axis. -/
@[rep_depth operator]
def phase : Op :=
  W.gammaA * W.gammaB

private theorem phase_sq :
    W.phase * W.phase = -1 := by
  calc
    W.phase * W.phase =
        W.gammaA * (W.gammaB * W.gammaA) * W.gammaB := by
          simp only [phase, mul_assoc]
    _ = W.gammaA * (-(W.gammaA * W.gammaB)) * W.gammaB := by
          rw [gammaB_gammaA_anticomm]
    _ = -((W.gammaA * W.gammaA) * (W.gammaB * W.gammaB)) := by
          noncomm_ring
    _ = -1 := by
          rw [gammaA_sq, gammaB_sq]
          simp

private theorem gammaA_phase_anticomm :
    W.gammaA * W.phase = -(W.phase * W.gammaA) := by
  have hleft : W.gammaA * W.phase = W.gammaB := by
    simp only [phase]
    rw [← mul_assoc, gammaA_sq]
    simp
  have hright : W.phase * W.gammaA = -W.gammaB := by
    calc
      W.phase * W.gammaA =
          W.gammaA * (W.gammaB * W.gammaA) := by
            simp only [phase, mul_assoc]
      _ = W.gammaA * (-(W.gammaA * W.gammaB)) := by
            rw [gammaB_gammaA_anticomm]
      _ = -((W.gammaA * W.gammaA) * W.gammaB) := by
            noncomm_ring
      _ = -W.gammaB := by
            rw [gammaA_sq]
            simp
  rw [hleft, hright]
  simp

/-- The CAR annihilation operator obtained from the real Clifford pair. -/
@[rep_depth operator]
noncomputable def annihilation : Op :=
  (1 / 2 : ℝ) • (W.gammaA + W.phase)

/-- The CAR creation operator obtained from the real Clifford pair. -/
@[rep_depth operator]
noncomputable def creation : Op :=
  (1 / 2 : ℝ) • (W.gammaA - W.phase)

@[rep_depth operator]
theorem annihilation_sq :
    W.annihilation * W.annihilation = 0 := by
  simp only [annihilation, smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
    gammaA_sq, phase_sq, gammaA_phase_anticomm]
  module

@[rep_depth operator]
theorem creation_sq :
    W.creation * W.creation = 0 := by
  simp only [creation, smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul,
    gammaA_sq, phase_sq, gammaA_phase_anticomm]
  module

@[rep_depth operator]
theorem car_anticommutator :
    W.annihilation * W.creation + W.creation * W.annihilation = 1 := by
  simp only [annihilation, creation, smul_mul_assoc, mul_smul_comm,
    mul_add, add_mul, mul_sub, sub_mul, gammaA_sq, phase_sq,
    gammaA_phase_anticomm]
  module

/-- The CAR pair is derived from the calibrated Clifford generators. -/
noncomputable def carPair : RealCARPair Op where
  annihilation := W.annihilation
  creation := W.creation
  nilpotent_annihilation := W.annihilation_sq
  nilpotent_creation := W.creation_sq
  car := W.car_anticommutator

end CliffordToCARCalibration

/--
Calibration between repository Drazin/chiral arrows and the Cantor tilt/switch
property.

This prevents identifying tilt/switch operators with `u_+`, `u_-`, or mirror
operators without an explicit representation map.
-/
@[rep_depth operator]
inductive TiltSwitchSide where
  | tilt
  | switch
  deriving DecidableEq, Repr

namespace TiltSwitchSide

/-- The side selects the tilt operator. -/
@[simp]
theorem eq_tilt_iff {s : TiltSwitchSide} : s = TiltSwitchSide.tilt ∨ s = TiltSwitchSide.switch :=
  by cases s <;> simp

end TiltSwitchSide

@[rep_depth operator]
structure DrazinArrowTiltSwitchCalibration
    (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op

  uPlusIndex : ℕ
  uMinusIndex : ℕ
  mirrorIndex : ℕ
  uMinusSide : TiltSwitchSide

namespace DrazinArrowTiltSwitchCalibration

variable {Op : Type*} [Ring Op]
variable (C : DrazinArrowTiltSwitchCalibration Op)

/-- Positive light-cone arrow readout. -/
@[rep_depth operator]
def uPlus : Op :=
  C.tiltSwitch.T C.uPlusIndex

/-- Negative light-cone arrow readout. -/
@[rep_depth operator]
def uMinus : Op :=
  match C.uMinusSide with
  | TiltSwitchSide.tilt => C.tiltSwitch.T C.uMinusIndex
  | TiltSwitchSide.switch => C.tiltSwitch.S C.uMinusIndex

/-- Mirror readout. -/
@[rep_depth operator]
def mirror : Op :=
  C.tiltSwitch.S C.mirrorIndex

end DrazinArrowTiltSwitchCalibration

@[rep_depth operator]
structure FractalCantorFockData
    (Op E : Type*) [Ring Op]
    [Algebra ℝ Op]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  celikKocak : CelikKocakInfiniteHilbertCarrier E
  cliffordToCAR : CliffordToCARCalibration Op
  drazinCalibration : DrazinArrowTiltSwitchCalibration Op


/-- Drazin support of a signal operator: `p = A Aᴰ`. -/
@[rep_depth operator]
structure DrazinHorizon
    (Op : Type*) [Ring Op] where
  A : Op
  AD : Op
  p : Op

  p_def :
    p = A * AD

  commute :
    A * AD = AD * A

  p_idempotent :
    p * p = p

theorem DrazinHorizon.support_commutes_with_A
    {Op : Type*} [Ring Op] (D : DrazinHorizon Op) :
    D.p * D.A = D.A * D.p := by
  calc
    D.p * D.A = (D.A * D.AD) * D.A := by rw [D.p_def]
    _ = D.A * (D.AD * D.A) := by simp [mul_assoc]
    _ = D.A * (D.A * D.AD) := by rw [D.commute]
    _ = D.A * D.p := by rw [D.p_def]

theorem DrazinHorizon.support_commutes_with_AD
    {Op : Type*} [Ring Op] (D : DrazinHorizon Op) :
    D.p * D.AD = D.AD * D.p := by
  calc
    D.p * D.AD = (D.A * D.AD) * D.AD := by rw [D.p_def]
    _ = D.A * (D.AD * D.AD) := by simp [mul_assoc]
    _ = (D.A * D.AD) * D.AD := by noncomm_ring
    _ = (D.AD * D.A) * D.AD := by rw [D.commute]
    _ = D.AD * (D.A * D.AD) := by simp [mul_assoc]
    _ = D.AD * D.p := by rw [D.p_def]

/-- Drazin-Green harmonic projector: `H = 1 - L Lᴰ`. -/
@[rep_depth operator]
structure DrazinGreenHarmonic
    (Op : Type*) [Ring Op] where
  L : Op
  LD : Op
  H : Op

  H_def :
    H = 1 - L * LD

  H_idempotent :
    H * H = H

theorem DrazinHorizon.projector_stable
    {Op : Type*} [Ring Op] (D : DrazinHorizon Op) (x : Op) :
    D.p * (D.p * x * D.p) * D.p = D.p * x * D.p := by
  calc
    D.p * (D.p * x * D.p) * D.p = (D.p * D.p) * x * (D.p * D.p) := by
      noncomm_ring
    _ = D.p * x * D.p := by rw [D.p_idempotent]

theorem DrazinGreenHarmonic.projector_stable
    {Op : Type*} [Ring Op] (G : DrazinGreenHarmonic Op) (x : Op) :
    G.H * (G.H * x * G.H) * G.H = G.H * x * G.H := by
  calc
    G.H * (G.H * x * G.H) * G.H = (G.H * G.H) * x * (G.H * G.H) := by
      noncomm_ring
    _ = G.H * x * G.H := by rw [G.H_idempotent]

/-- Matter envelope extracted from the Cantor/Fock observable. -/
@[rep_depth operator]
def fractalFockMatterEnvelope
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (x : Op) : Op :=
  G.H * (D.p * x * D.p) * G.H

theorem fractalFockMatterEnvelope_left_projector_stable
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op) (G : DrazinGreenHarmonic Op) (x : Op) :
    G.H * fractalFockMatterEnvelope D G x =
      fractalFockMatterEnvelope D G x := by
  unfold fractalFockMatterEnvelope
  calc
    G.H * (G.H * (D.p * x * D.p) * G.H) =
        (G.H * G.H) * (D.p * x * D.p) * G.H := by noncomm_ring
    _ = G.H * (D.p * x * D.p) * G.H := by rw [G.H_idempotent]

theorem fractalFockMatterEnvelope_right_projector_stable
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op) (G : DrazinGreenHarmonic Op) (x : Op) :
    fractalFockMatterEnvelope D G x * G.H =
      fractalFockMatterEnvelope D G x := by
  unfold fractalFockMatterEnvelope
  calc
    G.H * (D.p * x * D.p) * G.H * G.H =
        G.H * (D.p * x * D.p) * (G.H * G.H) := by noncomm_ring
    _ = G.H * (D.p * x * D.p) * G.H := by rw [G.H_idempotent]

/-- Real Fierz readout channels.  The phase-like channel is named `rotor`. -/
@[rep_depth operator]
inductive FierzChannel where
  | scalar
  | rotor
  | vector
  | axial
  | area
  deriving DecidableEq, Fintype

/-- Real Fierz readout packet. -/
@[rep_depth operator]
structure FierzReadout
    (Op : Type*) where
  channel : FierzChannel → Op → ℝ

/--
Fierz coordinates are read from the Drazin-Hodge envelope, not from the raw
Cantor/Fock operator.
-/
@[rep_depth operator]
def fractalFockFierzCoordinate
    {Op : Type*} [Ring Op]
    (D : DrazinHorizon Op)
    (G : DrazinGreenHarmonic Op)
    (R : FierzReadout Op)
    (x : Op)
    (ch : FierzChannel) : ℝ :=
  R.channel ch (fractalFockMatterEnvelope D G x)

end InfoGeometry.Topology.FractalCantorFock
