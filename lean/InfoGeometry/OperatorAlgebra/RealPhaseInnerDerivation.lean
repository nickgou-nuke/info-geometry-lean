/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic

/-!
# A real internal phase and its noncommutative inner derivation

For a real associative algebra and an internal phase `J`, the generator with
surprisal convention `K = -log rho` is `-(J * K)`. Its commutator is always an
associative derivation. It factors as `-J * [K,x]` only when `x` commutes with
`J`. We construct the restriction to that native centralizer subalgebra,
prove its Leibniz law and determine its kernel when `J * J = -1`.

Skew-adjointness additionally requires `star J = -J`, `star K = K` and
`Commute J K`. No density, logarithm, Hilbert completion or modular flow is
silently supplied by this algebraic construction.
-/

namespace InfoGeometry.OperatorAlgebra.RealPhaseInnerDerivation

open InfoGeometry.Geometry.AssociativeGaugeConnection

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The real generator consistent with `K = -log rho`. -/
def generator (J K : A) : A := -(J * K)

/-- The native real algebra of observables preserving the internal phase. -/
abbrev phaseAlgebra (J : A) : Subalgebra ℝ A :=
  Subalgebra.centralizer ℝ ({J} : Set A)

theorem mem_phaseAlgebra_iff (J x : A) : x ∈ phaseAlgebra J ↔ Commute J x := by
  simp only [phaseAlgebra, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff]
  exact ⟨fun h => h J rfl, fun h g hg => hg ▸ h.eq⟩

/-- Moving the internal phase past an observable requires the stated commutation. -/
theorem innerDerivative_factor (J K x : A) (hx : Commute J x) :
    innerDerivative (R := ℝ) (generator J K) x = -(J * (K * x - x * K)) := by
  change -(J * K) * x - x * -(J * K) = -(J * (K * x - x * K))
  have hx' : x * (J * K) = J * (x * K) := by
    rw [← mul_assoc, ← hx.eq, mul_assoc]
  noncomm_ring [hx']

omit [Algebra ℝ A] in
theorem generator_commutes_phase (J K : A) (hJK : Commute J K) :
    Commute J (generator J K) :=
  ((Commute.refl J).mul_right hJK).neg_right

/-- The ambient inner derivation preserves the phase centralizer. -/
theorem innerDerivative_mem_phaseAlgebra (J K : A) (hJK : Commute J K)
    (x : phaseAlgebra J) :
    innerDerivative (R := ℝ) (generator J K) (x : A) ∈ phaseAlgebra J := by
  apply (mem_phaseAlgebra_iff _ _).mpr
  have hx := (mem_phaseAlgebra_iff _ _).mp x.2
  have hG := generator_commutes_phase J K hJK
  exact (hG.mul_right hx).sub_right (hx.mul_right hG)

/-- A native linear endomorphism of the full, potentially noncommutative centralizer. -/
def phaseDerivation (J K : A) (hJK : Commute J K) : Module.End ℝ (phaseAlgebra J) where
  toFun x := ⟨innerDerivative (R := ℝ) (generator J K) (x : A),
    innerDerivative_mem_phaseAlgebra J K hJK x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (innerDerivative (R := ℝ) (generator J K)) (x : A) (y : A)
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (innerDerivative (R := ℝ) (generator J K)) r (x : A)

@[simp] theorem phaseDerivation_apply (J K : A) (hJK : Commute J K)
    (x : phaseAlgebra J) :
    (phaseDerivation J K hJK x : A) =
      innerDerivative (R := ℝ) (generator J K) (x : A) := rfl

theorem phaseDerivation_leibniz (J K : A) (hJK : Commute J K)
    (x y : phaseAlgebra J) :
    phaseDerivation J K hJK (x * y) =
      phaseDerivation J K hJK x * y + x * phaseDerivation J K hJK y := by
  apply Subtype.ext
  exact innerDerivative_isLeibniz (R := ℝ) (generator J K) (x : A) (y : A)

/-- Invertibility of the internal phase makes stationarity exactly commutation with `K`. -/
theorem phaseDerivation_eq_zero_iff (J K : A) (hJ : J * J = -1)
    (hJK : Commute J K) (x : phaseAlgebra J) :
    phaseDerivation J K hJK x = 0 ↔ Commute K (x : A) := by
  have hfactor := innerDerivative_factor J K (x : A)
    ((mem_phaseAlgebra_iff _ _).mp x.2)
  constructor
  · intro h
    have hv := congrArg (fun y : phaseAlgebra J => (y : A)) h
    change innerDerivative (R := ℝ) (generator J K) (x : A) = 0 at hv
    rw [hfactor, neg_eq_zero] at hv
    have hi := congrArg (fun y : A => J * y) hv
    rw [← mul_assoc, hJ, neg_one_mul, mul_zero, neg_eq_zero, sub_eq_zero] at hi
    exact hi
  · intro h
    apply Subtype.ext
    change innerDerivative (R := ℝ) (generator J K) (x : A) = 0
    rw [hfactor, h.eq, sub_self, mul_zero, neg_zero]

section Star

variable [StarRing A]

omit [Algebra ℝ A] in
/-- The phase-energy product has the correct skew-adjointness without external scalars. -/
theorem generator_star (J K : A) (hJ : star J = -J) (hK : star K = K)
    (hJK : Commute J K) : star (generator J K) = -generator J K := by
  simp only [generator, star_neg, star_mul, hJ, hK, mul_neg, neg_neg]
  exact hJK.eq.symm

/-- The corresponding commutator preserves star, hence preserves self-adjoint observables. -/
theorem innerDerivative_star (J K x : A) (hJ : star J = -J) (hK : star K = K)
    (hJK : Commute J K) :
    innerDerivative (R := ℝ) (generator J K) (star x) =
      star (innerDerivative (R := ℝ) (generator J K) x) := by
  change generator J K * star x - star x * generator J K =
    star (generator J K * x - x * generator J K)
  rw [star_sub, star_mul, star_mul, generator_star J K hJ hK hJK]
  noncomm_ring

theorem innerDerivative_selfAdjoint (J K x : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (hx : star x = x) :
    star (innerDerivative (R := ℝ) (generator J K) x) =
      innerDerivative (R := ℝ) (generator J K) x := by
  rw [← innerDerivative_star J K x hJ hK hJK, hx]

end Star

end InfoGeometry.OperatorAlgebra.RealPhaseInnerDerivation
