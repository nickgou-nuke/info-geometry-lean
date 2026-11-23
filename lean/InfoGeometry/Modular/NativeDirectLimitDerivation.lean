/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.RingTheory.Derivation.Basic
import InfoGeometry.Modular.ModularColimitDerivation
import InfoGeometry.Arithmetic.FiniteEulerLogDerivative

/-!
# Native algebraic direct limits of compatible derivations

The existing representative-based `ColimitDerivation` interface is instantiated
on Mathlib's actual root `DirectLimit`. Its representability and eventual-equality
fields are proved from the native quotient, not supplied as new assumptions.
The resulting map is bundled as Mathlib's `Derivation`.

The unit logarithmic derivative and exact finite Euler remainder then transport
along the actual algebra injections. There is no assertion that growing partial
Euler products are a compatible element, or that an infinite product converges.
This is an algebraic construction; no modular-flow differentiability, topology,
completion, or arithmetic explicit formula is established here.
-/

noncomputable section

namespace InfoGeometry.Modular.NativeDirectLimitDerivation

open InfoGeometry.Modular.ColimitDerivation
open InfoGeometry.Arithmetic.FiniteEulerLogDerivative
open scoped BigOperators

variable {R I : Type*} [CommRing R]
variable [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (f : ∀ i j, i ≤ j → A i →ₐ[R] A j)
variable [DirectedSystem A (fun i j h x => f i j h x)]

/-- The existing algebra-system interface supplied by native compatible algebra maps. -/
def nativeSystem : DirectedAlgSystem (R := R) I A where
  map := fun {i j} h => f i j h
  map_self i x := DirectedSystem.map_self' f x
  map_trans hij hjk x := (DirectedSystem.map_map' f hij hjk x).symm

/-- The existing cocone interface realized by the actual native direct limit.
The field `surj_dense` is exact algebraic representability, not topological density. -/
def nativeCocone : AlgColimitCocone (R := R) I A (nativeSystem f)
    (_root_.DirectLimit A f) where
  inr := DirectLimit.Algebra.of A f
  inr_comm := by
    intro i j hij x
    exact DirectLimit.Algebra.of_f hij x
  surj_dense := by
    intro x
    obtain ⟨i, a, ha⟩ := DirectLimit.exists_eq_mk (f := f) x
    exact ⟨i, a, ha.symm⟩
  inr_inj := by
    intro i x y hxy
    change (⟦⟨i, x⟩⟧ : _root_.DirectLimit A f) = ⟦⟨i, y⟩⟧ at hxy
    obtain ⟨j, hij, hij', heq⟩ := Quotient.exact hxy
    exact ⟨j, hij, heq⟩

variable (D : ∀ i, Derivation R (A i) (A i))
variable (hD : ∀ i j (h : i ≤ j) (x : A i),
  D j (f i j h x) = f i j h (D i x))

/-- Native local derivations instantiate the existing compatibility interface. -/
def nativeLocalDerivations : LocalDerivationSystem (R := R) I A (nativeSystem f) where
  deriv := fun i => (D i).toLinearMap
  deriv_leibniz := by
    intro i x y
    simpa only [smul_eq_mul, mul_comm, add_comm] using (D i).leibniz x y
  intertwine := by
    intro i j hij x
    exact (hD i j hij x).symm

/-- The algebraic direct-limit derivation, bundled in native Mathlib. -/
def derivation : Derivation R (_root_.DirectLimit A f) (_root_.DirectLimit A f) :=
  Derivation.mk'
    (colimitDerivLinearMap (nativeSystem f) (nativeLocalDerivations f D hD)
      (nativeCocone f))
    (by
      intro x y
      simpa only [smul_eq_mul, mul_comm, add_comm] using
        colimitDerivLinearMap_leibniz (nativeSystem f)
          (nativeLocalDerivations f D hD) (nativeCocone f) x y)

/-- The constructed derivation agrees with every stage derivation. -/
@[simp]
theorem derivation_of (i : I) (x : A i) :
    derivation f D hD (DirectLimit.Algebra.of A f i x) =
      DirectLimit.Algebra.of A f i (D i x) :=
  colimitDerivVal_inr (nativeSystem f) (nativeLocalDerivations f D hD)
    (nativeCocone f) i x

/-- Stage readback determines the native derivation uniquely. -/
theorem derivation_unique
    (E : Derivation R (_root_.DirectLimit A f) (_root_.DirectLimit A f))
    (hE : ∀ i x, E (DirectLimit.Algebra.of A f i x) =
      DirectLimit.Algebra.of A f i (D i x)) :
    E = derivation f D hD := by
  apply Derivation.ext
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk (f := f) x
  exact (hE i a).trans (derivation_of f D hD i a).symm

/-- The logarithmic derivative of a unit commutes with its actual stage injection. -/
theorem units_logDeriv_of (i : I) (u : (A i)ˣ) :
    DirectLimit.Algebra.of A f i (((u⁻¹ : (A i)ˣ) : A i) * D i (u : A i)) =
      (((Units.map (DirectLimit.Algebra.of A f i).toRingHom.toMonoidHom u)⁻¹ :
          (_root_.DirectLimit A f)ˣ) : _root_.DirectLimit A f) *
        derivation f D hD
          (Units.map (DirectLimit.Algebra.of A f i).toRingHom.toMonoidHom u :
            _root_.DirectLimit A f) :=
  units_logDeriv_map (DirectLimit.Algebra.of A f i) (D i) (derivation f D hD)
    (fun x => (derivation_of f D hD i x).symm) u

/-- An Euler-factor relation and scale law transfer to the native limit and
retain the exact prime-power remainder. The power cutoff remains finite. -/
theorem negative_eulerFactor_of_eq_sum_add_remainder
    (i : I) (E : (A i)ˣ) (a ell : A i)
    (hEuler : ((E⁻¹ : (A i)ˣ) : A i) = 1 - a)
    (hScale : D i a = -ell * a) (M : ℕ) :
    let ι := DirectLimit.Algebra.of A f i
    let Einf := Units.map ι.toRingHom.toMonoidHom E
    -(((Einf⁻¹ : (_root_.DirectLimit A f)ˣ) : _root_.DirectLimit A f) *
        derivation f D hD (Einf : _root_.DirectLimit A f)) =
      (∑ j ∈ Finset.range M, ι ell * (ι a) ^ (j + 1)) +
        ι ell * ((Einf : _root_.DirectLimit A f) * (ι a) ^ (M + 1)) := by
  dsimp only
  apply negative_units_logDeriv_eulerFactor_eq_sum_add_remainder
  · change DirectLimit.Algebra.of A f i ((E⁻¹ : (A i)ˣ) : A i) =
      1 - DirectLimit.Algebra.of A f i a
    rw [hEuler, map_sub, map_one]
  · rw [derivation_of f D hD i a, hScale, map_mul, map_neg]

end InfoGeometry.Modular.NativeDirectLimitDerivation

end
