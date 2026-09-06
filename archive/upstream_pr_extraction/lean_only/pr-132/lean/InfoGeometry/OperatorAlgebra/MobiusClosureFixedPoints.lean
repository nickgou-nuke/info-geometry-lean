/-
InfoGeometry/OperatorAlgebra/MobiusClosureFixedPoints.lean

Möbius/Tomita closure fixed points.

This module processes the question:

  what survives the e₋ ↔ e₊ Möbius/Tomita inversion?

It separates:

* pointwise fixed elements;
* swapped-pair symmetric survivors;
* Tomita M ∩ M′ overlap survivors;
* grade-zero setwise survivors;
* invariant readouts.

No claim is made that all of these are definitionally the same object.
-/

import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints

/-! ## 1. Abstract closure involution -/

/--
A closure/Möbius/Tomita involution on a carrier.
-/
structure ClosureInvolution
    (X : Type*) where
  /-- The inversion / mirror / closure map. -/
  theta : X → X

  /-- Involution law. -/
  theta_sq :
    ∀ x : X, theta (theta x) = x

namespace ClosureInvolution

variable {X : Type*}
variable (Θ : ClosureInvolution X)

/--
Pointwise fixed elements of the closure inversion.
-/
def IsFixed
    (x : X) : Prop :=
  Θ.theta x = x

/--
The mirror of a mirror is the original element.
-/
theorem theta_theta
    (x : X) :
    Θ.theta (Θ.theta x) = x :=
  Θ.theta_sq x

end ClosureInvolution

/-! ## 2. Linear closure involution and e₋/e₊ pairs -/

/--
A real-linear closure involution.

This is the correct interface for grade-swapping statements such as `e₋ ↔ e₊`.
-/
structure LinearClosureInvolution
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  theta : V →ₗ[ℝ] V

  theta_sq :
    theta.comp theta = LinearMap.id

namespace LinearClosureInvolution

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (Θ : LinearClosureInvolution V)

/--
Pointwise fixed vectors/elements.
-/
def IsFixed
    (x : V) : Prop :=
  Θ.theta x = x

/--
Pointwise form of `θ² = 1`.
-/
theorem theta_theta
    (x : V) :
    Θ.theta (Θ.theta x) = x := by
  have h :=
    congrArg (fun T : V →ₗ[ℝ] V => T x) Θ.theta_sq
  simpa [LinearMap.comp_apply] using h

/--
If `θ e₋ = e₊` and `θ e₊ = e₋`, then the symmetric combination survives.
-/
theorem swapped_sum_fixed
    {eMinus ePlus : V}
    (hmp : Θ.theta eMinus = ePlus)
    (hpm : Θ.theta ePlus = eMinus) :
    Θ.IsFixed (eMinus + ePlus) := by
  dsimp [IsFixed]
  rw [map_add, hmp, hpm, add_comm]

/--
If `θ e₋ = e₊` and `θ e₊ = e₋`, then the antisymmetric combination flips sign.
-/
theorem swapped_sub_antifixed
    {eMinus ePlus : V}
    (hmp : Θ.theta eMinus = ePlus)
    (hpm : Θ.theta ePlus = eMinus) :
    Θ.theta (eMinus - ePlus) = -(eMinus - ePlus) := by
  calc
    Θ.theta (eMinus - ePlus)
        = Θ.theta eMinus - Θ.theta ePlus := by
            rw [map_sub]
    _ = ePlus - eMinus := by
            rw [hmp, hpm]
    _ = -(eMinus - ePlus) := by
            abel

end LinearClosureInvolution

/-! ## 3. Tomita split fixed points -/

/--
A Tomita-style split inversion.

`theta` maps observable data into commutant data and conversely.
-/
structure TomitaSplitInversion
    (Op : Type*) where
  mirror : ClosureInvolution Op

  /-- Observable algebra/sector predicate. -/
  InObservable : Set Op

  /-- Commutant/hidden sector predicate. -/
  InCommutant : Set Op

  /-- Tomita routing: observable maps into commutant. -/
  observable_to_commutant :
    ∀ x : Op,
      x ∈ InObservable →
        mirror.theta x ∈ InCommutant

  /-- Tomita routing: commutant maps into observable. -/
  commutant_to_observable :
    ∀ x : Op,
      x ∈ InCommutant →
        mirror.theta x ∈ InObservable

namespace TomitaSplitInversion

variable {Op : Type*}
variable (T : TomitaSplitInversion Op)

/--
Overlap of observable and commutant sectors.
-/
def InOverlap
    (x : Op) : Prop :=
  x ∈ T.InObservable ∧ x ∈ T.InCommutant

/--
If an observable element is fixed by the Tomita/Möbius mirror, then it lies in
the observable/commutant overlap.
-/
theorem fixed_observable_mem_overlap
    {x : Op}
    (hx : x ∈ T.InObservable)
    (hfix : T.mirror.IsFixed x) :
    T.InOverlap x := by
  constructor
  · exact hx
  · have hθ : T.mirror.theta x ∈ T.InCommutant :=
      T.observable_to_commutant x hx
    dsimp [ClosureInvolution.IsFixed] at hfix
    rw [hfix] at hθ
    exact hθ

/--
If a commutant element is fixed by the Tomita/Möbius mirror, then it lies in
the observable/commutant overlap.
-/
theorem fixed_commutant_mem_overlap
    {x : Op}
    (hx : x ∈ T.InCommutant)
    (hfix : T.mirror.IsFixed x) :
    T.InOverlap x := by
  constructor
  · have hθ : T.mirror.theta x ∈ T.InObservable :=
      T.commutant_to_observable x hx
    dsimp [ClosureInvolution.IsFixed] at hfix
    rw [hfix] at hθ
    exact hθ
  · exact hx

end TomitaSplitInversion

/-! ## 4. Factor/center collapse law -/

/--
A scalar/central collapse law for the observable-commutant overlap.

For a factor representation, this is the place where the model supplies:

`M ∩ M′ = scalars`.
-/
structure OverlapScalarLaw
    {Op : Type*}
    (T : TomitaSplitInversion Op) where
  /-- Scalar/central predicate. -/
  IsScalar : Op → Prop

  /-- Overlap elements are scalar/central. -/
  overlap_is_scalar :
    ∀ x : Op,
      T.InOverlap x →
        IsScalar x

namespace OverlapScalarLaw

variable {Op : Type*}
variable {T : TomitaSplitInversion Op}
variable (S : OverlapScalarLaw T)

/--
A fixed observable element is scalar/central once the overlap collapse law is
supplied.
-/
theorem fixed_observable_is_scalar
    {x : Op}
    (hx : x ∈ T.InObservable)
    (hfix : T.mirror.IsFixed x) :
    S.IsScalar x :=
  S.overlap_is_scalar x
    (T.fixed_observable_mem_overlap hx hfix)

/--
A fixed commutant element is scalar/central once the overlap collapse law is
supplied.
-/
theorem fixed_commutant_is_scalar
    {x : Op}
    (hx : x ∈ T.InCommutant)
    (hfix : T.mirror.IsFixed x) :
    S.IsScalar x :=
  S.overlap_is_scalar x
    (T.fixed_commutant_mem_overlap hx hfix)

end OverlapScalarLaw

/-! ## 5. Five-grade Möbius inversion -/

/--
A five-grade closure inversion.

The inversion swaps negative and positive grades and preserves grade zero
setwise.
-/
structure FiveGradeMobiusInversion
    (L : Type*) where
  closure : ClosureInvolution L

  gNegTwo : Set L
  gNegOne : Set L
  gZero : Set L
  gPosOne : Set L
  gPosTwo : Set L

  negTwo_to_posTwo :
    ∀ x : L, x ∈ gNegTwo → closure.theta x ∈ gPosTwo

  posTwo_to_negTwo :
    ∀ x : L, x ∈ gPosTwo → closure.theta x ∈ gNegTwo

  negOne_to_posOne :
    ∀ x : L, x ∈ gNegOne → closure.theta x ∈ gPosOne

  posOne_to_negOne :
    ∀ x : L, x ∈ gPosOne → closure.theta x ∈ gNegOne

  zero_to_zero :
    ∀ x : L, x ∈ gZero → closure.theta x ∈ gZero

namespace FiveGradeMobiusInversion

variable {L : Type*}
variable (G : FiveGradeMobiusInversion L)

/--
A fixed grade `-1` element must also lie in grade `+1`.
-/
theorem fixed_negOne_mem_posOne
    {x : L}
    (hx : x ∈ G.gNegOne)
    (hfix : G.closure.IsFixed x) :
    x ∈ G.gPosOne := by
  have hθ : G.closure.theta x ∈ G.gPosOne :=
    G.negOne_to_posOne x hx
  dsimp [ClosureInvolution.IsFixed] at hfix
  rw [hfix] at hθ
  exact hθ

/--
A fixed grade `+1` element must also lie in grade `-1`.
-/
theorem fixed_posOne_mem_negOne
    {x : L}
    (hx : x ∈ G.gPosOne)
    (hfix : G.closure.IsFixed x) :
    x ∈ G.gNegOne := by
  have hθ : G.closure.theta x ∈ G.gNegOne :=
    G.posOne_to_negOne x hx
  dsimp [ClosureInvolution.IsFixed] at hfix
  rw [hfix] at hθ
  exact hθ

/--
A fixed grade `-2` element must also lie in grade `+2`.
-/
theorem fixed_negTwo_mem_posTwo
    {x : L}
    (hx : x ∈ G.gNegTwo)
    (hfix : G.closure.IsFixed x) :
    x ∈ G.gPosTwo := by
  have hθ : G.closure.theta x ∈ G.gPosTwo :=
    G.negTwo_to_posTwo x hx
  dsimp [ClosureInvolution.IsFixed] at hfix
  rw [hfix] at hθ
  exact hθ

/--
A fixed grade `+2` element must also lie in grade `-2`.
-/
theorem fixed_posTwo_mem_negTwo
    {x : L}
    (hx : x ∈ G.gPosTwo)
    (hfix : G.closure.IsFixed x) :
    x ∈ G.gNegTwo := by
  have hθ : G.closure.theta x ∈ G.gNegTwo :=
    G.posTwo_to_negTwo x hx
  dsimp [ClosureInvolution.IsFixed] at hfix
  rw [hfix] at hθ
  exact hθ

/--
Grade zero survives setwise under the Möbius/Tomita inversion.
-/
theorem zero_grade_survives_setwise
    {x : L}
    (hx : x ∈ G.gZero) :
    G.closure.theta x ∈ G.gZero :=
  G.zero_to_zero x hx

end FiveGradeMobiusInversion

/-! ## 6. Grade disjointness obstructions -/

/--
Disjointness laws for opposite grades.

When opposite grades are disjoint, no nontrivial element of a single swapped
grade can be pointwise fixed.
-/
structure FiveGradeDisjointness
    {L : Type*}
    (G : FiveGradeMobiusInversion L) where
  negOne_posOne_disjoint :
    ∀ x : L, x ∈ G.gNegOne → x ∈ G.gPosOne → False

  negTwo_posTwo_disjoint :
    ∀ x : L, x ∈ G.gNegTwo → x ∈ G.gPosTwo → False

namespace FiveGradeDisjointness

variable {L : Type*}
variable {G : FiveGradeMobiusInversion L}
variable (D : FiveGradeDisjointness G)

/--
A grade `-1` element cannot be pointwise fixed if grades `-1` and `+1`
are disjoint.
-/
theorem no_fixed_negOne
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gNegOne)
    (hfix : G.closure.IsFixed x) :
    False :=
  FiveGradeDisjointness.negOne_posOne_disjoint D x hx
    (G.fixed_negOne_mem_posOne hx hfix)

/--
A grade `+1` element cannot be pointwise fixed if grades `-1` and `+1`
are disjoint.
-/
theorem no_fixed_posOne
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gPosOne)
    (hfix : G.closure.IsFixed x) :
    False :=
  FiveGradeDisjointness.negOne_posOne_disjoint D x
    (G.fixed_posOne_mem_negOne hx hfix)
    hx

/--
A grade `-2` element cannot be pointwise fixed if grades `-2` and `+2`
are disjoint.
-/
theorem no_fixed_negTwo
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gNegTwo)
    (hfix : G.closure.IsFixed x) :
    False :=
  FiveGradeDisjointness.negTwo_posTwo_disjoint D x hx
    (G.fixed_negTwo_mem_posTwo hx hfix)

/--
A grade `+2` element cannot be pointwise fixed if grades `-2` and `+2`
are disjoint.
-/
theorem no_fixed_posTwo
    (D : FiveGradeDisjointness G)
    {x : L}
    (hx : x ∈ G.gPosTwo)
    (hfix : G.closure.IsFixed x) :
    False :=
  FiveGradeDisjointness.negTwo_posTwo_disjoint D x
    (G.fixed_posTwo_mem_negTwo hx hfix)
    hx

end FiveGradeDisjointness

/-! ## 7. Invariant readouts -/

/--
A readout that survives the Möbius/Tomita inversion.
-/
def InvariantReadout
    (X Charge : Type*)
    (Θ : ClosureInvolution X) :=
  {read : X → Charge //
    ∀ x : X, read (Θ.theta x) = read x}

namespace InvariantReadout

variable {X Charge : Type*}
variable {Θ : ClosureInvolution X}
variable (R : InvariantReadout X Charge Θ)

abbrev read : X → Charge := R.1

theorem invariant
    (x : X) :
    R.read (Θ.theta x) = R.read x :=
  R.2 x

def mk
    (read : X → Charge)
    (invariant : ∀ x : X, read (Θ.theta x) = read x) :
    InvariantReadout X Charge Θ :=
  ⟨read, invariant⟩

/--
The readout is constant on closure-pairs.
-/
theorem read_theta
    (x : X) :
    R.read (Θ.theta x) = R.read x :=
  R.invariant x

/--
If two elements are related by closure inversion, their readouts agree.
-/
theorem read_eq_of_theta_eq
    {x y : X}
    (h : y = Θ.theta x) :
    R.read y = R.read x := by
  rw [h]
  exact R.read_theta x

end InvariantReadout

/-! ## 8. Processed answer package -/

/--
A processed survivor ledger for Möbius/Tomita closure.

This packages the three different kinds of survival:

* fixed-point survival;
* overlap/scalar survival;
* invariant-readout survival.
-/
structure MobiusSurvivalLedger
    (Op Charge : Type*) where
  tomita :
    TomitaSplitInversion Op

  readout :
    InvariantReadout Op Charge tomita.mirror

  /-- Optional overlap collapse law. -/
  scalarLaw :
    Option (OverlapScalarLaw tomita)

namespace MobiusSurvivalLedger

variable {Op Charge : Type*}
variable (S : MobiusSurvivalLedger Op Charge)

/--
Invariant charge/readout survives Tomita inversion.
-/
theorem readout_survives
    (x : Op) :
    S.readout.read (S.tomita.mirror.theta x) =
      S.readout.read x :=
  S.readout.read_theta x

/--
A fixed observable element belongs to the observable/commutant overlap.
-/
theorem fixed_observable_mem_overlap
    {x : Op}
    (hx : x ∈ S.tomita.InObservable)
    (hfix : S.tomita.mirror.IsFixed x) :
    S.tomita.InOverlap x :=
  S.tomita.fixed_observable_mem_overlap hx hfix

end MobiusSurvivalLedger

end InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints
