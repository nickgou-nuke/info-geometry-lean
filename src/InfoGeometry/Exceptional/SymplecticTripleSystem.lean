import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Exceptional

/-!
# Symplectic triple systems

This file introduces only the property-gated interface needed by the
Freudenthal standard-envelope construction.  It does not strengthen or
modify `CubicJordanDatum`, and it does not claim an exceptional Lie algebra.
-/

structure SymplecticTripleSystemDatum
    (T : Type*) [AddCommGroup T] [Module ℝ T] where
  omega : T →ₗ[ℝ] T →ₗ[ℝ] ℝ
  omega_alt : ∀ x : T, omega x x = 0
  triple : T →ₗ[ℝ] T →ₗ[ℝ] T →ₗ[ℝ] T
  triple_symm₁₂ : ∀ x y z : T, triple x y z = triple y x z
  triple_swap₂₃ : ∀ x y z : T,
    triple x y z - triple x z y =
      omega x z • y - omega x y • z + (2 * omega y z) • x
  triple_derivation : ∀ x y u v w : T,
    triple x y (triple u v w) =
      triple (triple x y u) v w +
        triple u (triple x y v) w + triple u v (triple x y w)
  omega_invariant : ∀ x y u v : T,
    omega (triple x y u) v + omega u (triple x y v) = 0

theorem SymplecticTripleSystemDatum.omega_skew
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (S : SymplecticTripleSystemDatum T) (x y : T) :
    S.omega x y = -S.omega y x := by
  have h' := S.omega_alt x
  have h'' := S.omega_alt y
  have h : S.omega x x + S.omega y x +
      S.omega x y + S.omega y y = 0 := by
    simpa only [map_add, LinearMap.add_apply, add_assoc] using
      S.omega_alt (x + y)
  linarith

theorem SymplecticTripleSystemDatum.innerDerivation_preserves_omega
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (S : SymplecticTripleSystemDatum T) (x y u v : T) :
    S.omega (S.triple x y u) v +
      S.omega u (S.triple x y v) = 0 := by
  exact S.omega_invariant x y u v

def innerDerivation
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (S : SymplecticTripleSystemDatum T) (x y : T) :
    Module.End ℝ T := S.triple x y

theorem innerDerivation_commutator
    {T : Type*} [AddCommGroup T] [Module ℝ T]
    (S : SymplecticTripleSystemDatum T) (x y u v : T) :
    ⁅innerDerivation S x y, innerDerivation S u v⁆ =
      innerDerivation S (innerDerivation S x y u) v +
        innerDerivation S u (innerDerivation S x y v) := by
  apply LinearMap.ext
  intro w
  change S.triple x y (S.triple u v w) -
      S.triple u v (S.triple x y w) =
    S.triple (S.triple x y u) v w +
      S.triple u (S.triple x y v) w
  have h := S.triple_derivation x y u v w
  calc
    S.triple x y (S.triple u v w) - S.triple u v (S.triple x y w) =
        (S.triple (S.triple x y u) v w +
          (S.triple u (S.triple x y v) w +
            S.triple u v (S.triple x y w))) -
          S.triple u v (S.triple x y w) := by rw [h]; abel
    _ = S.triple (S.triple x y u) v w +
        S.triple u (S.triple x y v) w := by abel

end InfoGeometry.Exceptional
