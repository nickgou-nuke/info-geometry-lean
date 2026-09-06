import InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction

/-!
# The zero `B₃` intertwiner carrier

The native boundary representation is eight-dimensional, while the concrete
Fibonacci block is two-dimensional.  A candidate morphism on these matrix
carriers is required to intertwine both Artin generators.  The existing
spectral obstruction proves that this Hom carrier is the zero submodule.

This is a generator-level representation theorem; it does not invent a
global `FibCat` representation or a categorical equivalence between the two
carriers.
-/

namespace InfoGeometry.Canonical.BoundaryFibonacciHomObstruction

open InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
open InfoGeometry.Physics
open InfoGeometry.Canonical.YangBaxterProof

abbrev B3FibonacciHom :=
  LinearMap.ker simultaneousGeneratorDefect

theorem mem_B3FibonacciHom_iff
    (Φ : Matrix (Fin 2) (Fin 8) ℂ) :
    Φ ∈ B3FibonacciHom ↔
      IntertwinesFirstGenerator Φ ∧
        Φ * JonesBraidB3.s1 = B * Φ := by
  rw [mem_simultaneousGeneratorDefect_ker_iff,
    mem_firstGeneratorDefect_ker_iff,
    mem_secondGeneratorDefect_ker_iff]

theorem B3FibonacciHom_eq_bot :
    B3FibonacciHom = ⊥ :=
  simultaneousGeneratorDefect_ker_eq_bot

theorem B3FibonacciHom_eq_zero (Φ : B3FibonacciHom) :
    Φ = 0 := by
  apply Subtype.ext
  have h : (Φ : Matrix (Fin 2) (Fin 8) ℂ) ∈
      (⊥ : Submodule ℂ (Matrix (Fin 2) (Fin 8) ℂ)) := by
    rw [← B3FibonacciHom_eq_bot]
    exact Φ.property
  change (Φ : Matrix (Fin 2) (Fin 8) ℂ) = 0 at h
  exact h

theorem B3FibonacciHom_subsingleton :
    Subsingleton B3FibonacciHom := by
  constructor
  intro Φ Ψ
  exact (B3FibonacciHom_eq_zero Φ).trans
    (B3FibonacciHom_eq_zero Ψ).symm

end InfoGeometry.Canonical.BoundaryFibonacciHomObstruction
