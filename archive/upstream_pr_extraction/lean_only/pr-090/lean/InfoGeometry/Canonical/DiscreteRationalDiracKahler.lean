import Mathlib
import InfoGeometry.Canonical.DiscreteRationalHodgeConjugation

namespace InfoGeometry.Canonical

/-!
Rational Dirac--Kähler readouts.  This file records the consequences of
nilpotence and sector preservation; it does not assert a Hodge decomposition
or a geometric identification of the supplied star.
-/

def RationalIsExact
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d : V →ₗ[ℚ] V) (x : V) : Prop :=
  ∃ y, d y = x

def RationalIsCoexact
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (cod : V →ₗ[ℚ] V) (x : V) : Prop :=
  ∃ y, cod y = x

def RationalIsHarmonic
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) (x : V) : Prop :=
  d x = 0 ∧ cod x = 0

theorem rational_exact_closed_of_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d : V →ₗ[ℚ] V)
    (hd : d.comp d = 0)
    {x : V}
    (hx : RationalIsExact d x) :
    d x = 0 := by
  rcases hx with ⟨y, rfl⟩
  have h := congrArg (fun f : V →ₗ[ℚ] V => f y) hd
  simpa [LinearMap.comp_apply] using h

theorem rational_coexact_coclosed_of_nilpotent
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (cod : V →ₗ[ℚ] V)
    (hcod : cod.comp cod = 0)
    {x : V}
    (hx : RationalIsCoexact cod x) :
    cod x = 0 := by
  rcases hx with ⟨y, rfl⟩
  have h := congrArg (fun f : V →ₗ[ℚ] V => f y) hcod
  simpa [LinearMap.comp_apply] using h

theorem rational_harmonic_is_closed
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) {x : V}
    (hx : RationalIsHarmonic d cod x) :
    d x = 0 :=
  hx.1

theorem rational_harmonic_is_coclosed
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) {x : V}
    (hx : RationalIsHarmonic d cod x) :
    cod x = 0 :=
  hx.2

theorem rational_harmonic_annihilated_by_laplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (d cod : V →ₗ[ℚ] V) {x : V}
    (hx : RationalIsHarmonic d cod x) :
    rationalHodgeLaplacian d cod x = 0 := by
  simp [rationalHodgeLaplacian, LinearMap.add_apply,
    LinearMap.comp_apply, hx.1, hx.2]

structure RationalDiracKahlerData (V : Type*)
    [AddCommGroup V] [Module ℚ V] where
  d : V →ₗ[ℚ] V
  cod : V →ₗ[ℚ] V
  d_sq_zero : d.comp d = 0
  cod_sq_zero : cod.comp cod = 0

def RationalDiracKahlerData.dirac
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V) : V →ₗ[ℚ] V :=
  rationalDiracKahler D.d D.cod

def RationalDiracKahlerData.laplacian
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V) : V →ₗ[ℚ] V :=
  rationalHodgeLaplacian D.d D.cod

theorem RationalDiracKahlerData.dirac_sq
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V) :
    D.dirac.comp D.dirac = D.laplacian :=
  rationalDiracKahler_sq_eq_hodgeLaplacian D.d D.cod
    D.d_sq_zero D.cod_sq_zero

def RationalDiracKahlerData.Preserves
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V)
    (S : Submodule ℚ V) : Prop :=
  (∀ x, x ∈ S → D.d x ∈ S) ∧
  (∀ x, x ∈ S → D.cod x ∈ S)

theorem RationalDiracKahlerData.dirac_preserves
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V)
    (S : Submodule ℚ V)
    (hS : D.Preserves S) {x : V} (hx : x ∈ S) :
    D.dirac x ∈ S := by
  exact S.add_mem (hS.1 x hx) (hS.2 x hx)

theorem RationalDiracKahlerData.laplacian_preserves
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (D : RationalDiracKahlerData V)
    (S : Submodule ℚ V)
    (hS : D.Preserves S) {x : V} (hx : x ∈ S) :
    D.laplacian x ∈ S := by
  exact S.add_mem (hS.1 (D.cod x) (hS.2 x hx))
    (hS.2 (D.d x) (hS.1 x hx))

end InfoGeometry.Canonical
