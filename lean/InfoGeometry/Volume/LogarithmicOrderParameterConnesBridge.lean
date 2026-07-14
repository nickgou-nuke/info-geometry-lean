import InfoGeometry.Cocycle.LogarithmicOrderParameter
import InfoGeometry.Volume.ConnesCocycle

/-!
# Logarithmic Order Parameter / Connes Bridge

This module keeps the dependency direction honest:

* `InfoGeometry.Cocycle.LogarithmicOrderParameter` owns the scalar `H¹`
  negative-log density calculus;
* `InfoGeometry.Volume.ConnesCocycle` owns the Connes cocycle interface and
  scalar descent from a noncommutative cocycle;
* this file identifies the scalar Connes descent with the negative-log
  order-parameter convention.

The Connes cocycle itself remains exponentiated/noncommutative.  The
`connesScalarModularHamiltonian` below is only the scalar commutative shadow
after a `ScalarCocycleBridge` has been supplied.
-/

noncomputable section

namespace LogarithmicOrderParameterConnesBridge

open InfoGeometry.Cocycle
open InfoGeometry.Volume.ConnesCocycle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Positive scalar density obtained from the scalar descent of a Connes cocycle. -/
def connesScalarDensity
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ) :
    Multiplicative ℝ → PUnit → ℝ :=
  fun t _ => |((scalarCocycle (H := H) σ u B t.toAdd : ℝˣ) : ℝ)|

/--
Scalar modular-Hamiltonian / surprisal convention extracted from a Connes
scalar cocycle: `K = -log ρ`.
-/
def connesScalarModularHamiltonian
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ) :
    ℝ → ℝ :=
  fun t => -cocycleLogPotential (H := H) σ u B t

/--
The scalar Connes modular Hamiltonian is exactly the generic logarithmic
order-parameter `logPotential` applied to the descended positive density.
-/
theorem connesScalarModularHamiltonian_eq_logPotential
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ) (t : ℝ) :
    connesScalarModularHamiltonian (H := H) σ u B t =
      logPotential (connesScalarDensity (H := H) σ u B)
        (Multiplicative.ofAdd t) PUnit.unit := by
  rfl

/-- The descended Connes scalar density is strictly positive. -/
theorem connesScalarDensity_pos
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ)
    (t : Multiplicative ℝ) (x : PUnit) :
    0 < connesScalarDensity (H := H) σ u B t x := by
  unfold connesScalarDensity
  exact abs_pos.mpr (Units.ne_zero _)

/--
If `u` satisfies the Connes cocycle identity, the scalar modular Hamiltonian is
additive in modular time.
-/
theorem connesScalarModularHamiltonian_add
    (σ : AdditiveModularFlow (H := H))
    (u : ℝ → AlgebraEnd H)
    (hCocycle : IsConnesCocycle σ u)
    (B : ScalarCocycleBridge (H := H) σ) (s t : ℝ) :
    connesScalarModularHamiltonian (H := H) σ u B (s + t) =
      connesScalarModularHamiltonian (H := H) σ u B s +
        connesScalarModularHamiltonian (H := H) σ u B t := by
  unfold connesScalarModularHamiltonian
  rw [cocycleLogPotential_add (H := H) σ u hCocycle B s t]
  ring

end LogarithmicOrderParameterConnesBridge

