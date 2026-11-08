-- ConnesMarcolliShimura.lean

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
This file keeps the former Connes--Marcolli/Shimura interface honest by making
the required preservation and phase-transition statements fields of a finite
model, then instantiating that interface with a tiny concrete model.

It is not a proof of the analytic Connes--Marcolli theory.  The exported
theorems below are facts about the concrete model defined in this file.
-/

/-- The nonzero element of `Fin 2` swaps the two points. -/
def flipTwo (x : Fin 2) : Fin 2 :=
  if x = 0 then 1 else 0

/-- A concrete two-point action of `Fin 2` on `Fin 2`. -/
def twoPointAction (g x : Fin 2) : Fin 2 :=
  if g = 0 then x else flipTwo x

/-- Proof-carrying data for the finite Shimura cut-off interface used below. -/
structure ShimuraCutOffModel where
  AdelicInverseSystem : Type
  ImaginaryQuadraticField : Type
  AbelianGaloisGroup : Type
  milnorMorphism : AdelicInverseSystem → AdelicInverseSystem
  GaloisAction : AbelianGaloisGroup → AdelicInverseSystem → AdelicInverseSystem
  DedekindLFunction : Nat → Nat
  PhaseTransition : Nat → Prop
  symmetry :
    ∀ (g : AbelianGaloisGroup) (x : AdelicInverseSystem),
      milnorMorphism x = x → milnorMorphism (GaloisAction g x) = GaloisAction g x
  phaseTransitionAtTwo : PhaseTransition 2

namespace ConcreteShimuraModel

/-- The two-point adelic inverse-system model. -/
def finiteModel : ShimuraCutOffModel where
  AdelicInverseSystem := Fin 2
  ImaginaryQuadraticField := Fin 2
  AbelianGaloisGroup := Fin 2
  milnorMorphism := id
  GaloisAction := twoPointAction
  DedekindLFunction := fun n => n + 1
  PhaseTransition := fun β => β = 2
  symmetry := by
    intro _ _ _
    simp [twoPointAction]
  phaseTransitionAtTwo := by
    show 2 = 2
    rfl

end ConcreteShimuraModel

/-- The concrete carrier replacing the former black-box adelic inverse system. -/
abbrev AdelicInverseSystem : Type :=
  Fin 2

/-- The concrete endomorphism used to define the finite Shimura cut-off. -/
def milnorMorphism : AdelicInverseSystem → AdelicInverseSystem :=
  id

/-- The finite Shimura cut-off: fixed points of the concrete endomorphism. -/
def AdelicShimuraCutOff (x : AdelicInverseSystem) : Prop :=
  milnorMorphism x = x

/-- Concrete finite carrier for an imaginary quadratic field parameter. -/
abbrev ImaginaryQuadraticField : Type :=
  Fin 2

/-- Concrete two-point abelian Galois group used by the finite model. -/
abbrev AbelianGaloisGroup : Type :=
  Fin 2

/-- The concrete Galois action of the two-point group. -/
def GaloisAction : AbelianGaloisGroup → AdelicInverseSystem → AdelicInverseSystem :=
  twoPointAction

/-- In the finite model, the endomorphism fixes every element. -/
theorem milnorMorphism_eq_self (x : AdelicInverseSystem) :
    milnorMorphism x = x := by
  simp [milnorMorphism]

/-- The nonzero group element swaps the first point to the second. -/
theorem action_one_zero :
    GaloisAction 1 0 = 1 := by
  simp [GaloisAction, twoPointAction, flipTwo]

/-- The nonzero group element swaps the second point to the first. -/
theorem action_one_one :
    GaloisAction 1 1 = 0 := by
  simp [GaloisAction, twoPointAction, flipTwo]

/-- Applying the same finite action twice returns to the starting point. -/
theorem action_order_two (g : AbelianGaloisGroup) (x : AdelicInverseSystem) :
    GaloisAction g (GaloisAction g x) = x := by
  fin_cases g <;> fin_cases x <;> simp [GaloisAction, twoPointAction, flipTwo]

/-- Every element of the finite carrier lies in the finite Shimura cut-off. -/
theorem adelicShimuraCutOff_all (x : AdelicInverseSystem) :
    AdelicShimuraCutOff x := by
  simp [AdelicShimuraCutOff, milnorMorphism]

/--
In the concrete model, the two-point Galois action preserves the Shimura
cut-off.
-/
theorem connes_marcolli_symmetry :
    ∀ (g : AbelianGaloisGroup) (x : AdelicInverseSystem),
      AdelicShimuraCutOff x → AdelicShimuraCutOff (GaloisAction g x) := by
  intro _ _ _
  simp [AdelicShimuraCutOff, milnorMorphism]

/-- A concrete arithmetic observable for the toy model. -/
def DedekindLFunction : Nat → Nat :=
  fun n => n + 1

/-- The concrete arithmetic observable takes value `1` at `0`. -/
theorem dedekindLFunction_zero :
    DedekindLFunction 0 = 1 := by
  simp [DedekindLFunction]

/-- The concrete arithmetic observable is the successor function. -/
theorem dedekindLFunction_eq_succ (n : Nat) :
    DedekindLFunction n = n + 1 := by
  simp [DedekindLFunction]

/-- The model marks exactly `β = 2` as its phase-transition point. -/
def PhaseTransition : Nat → Prop :=
  fun β => β = 2

/-- The concrete model has its marked phase transition at `β = 2`. -/
theorem phase_transition_at_two :
    PhaseTransition 2 := by
  simp [PhaseTransition]
