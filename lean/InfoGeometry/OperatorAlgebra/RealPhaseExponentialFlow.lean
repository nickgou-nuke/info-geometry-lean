/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealPhaseInnerDerivation
import InfoGeometry.Canonical.TransportLieDerivative
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Analytic integration of the real phase derivation

In a complete normed real star algebra, a skew-adjoint internal phase `J`
commuting with a self-adjoint `K` gives a genuine one-parameter group of
unitaries `exp (t • (-(J * K)))`. Native unitary conjugation then gives a
one-parameter group of real star-algebra automorphisms. We connect its
analytic derivative to the existing noncommutative inner derivation and
prove that it preserves the centralizer of `J`.

The rational normed algebra structure is obtained by restricting real
scalars; it is needed only by Mathlib's exponential convergence API. No
external complex scalars or finite-dimensional hypotheses are used. This
is bounded exponential dynamics, not a construction of a Tomita standard
form or an identification with spacetime dynamics.
-/

namespace InfoGeometry.OperatorAlgebra.RealPhaseExponentialFlow

noncomputable section

open InfoGeometry.Canonical
open InfoGeometry.Geometry.AssociativeGaugeConnection
open RealPhaseInnerDerivation

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [StarModule ℝ A] [ContinuousStar A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

/-- The analytic exponential, packaged as an actual group homomorphism into unitaries. -/
noncomputable def unitaryFlow (J K : A) (hJ : star J = -J) (hK : star K = K)
    (hJK : Commute J K) : Multiplicative ℝ →* unitary A where
  toFun t := ⟨NormedSpace.exp (t.toAdd • generator J K), by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff]
    simp only [star_smul, star_trivial, generator_star J K hJ hK hJK, smul_neg]⟩
  map_one' := by
    apply Subtype.ext
    change NormedSpace.exp ((0 : ℝ) • generator J K) = 1
    simp
  map_mul' s t := by
    apply Subtype.ext
    change NormedSpace.exp ((s.toAdd + t.toAdd) • generator J K) =
      NormedSpace.exp (s.toAdd • generator J K) *
        NormedSpace.exp (t.toAdd • generator J K)
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute
      (((Commute.refl (generator J K)).smul_left s.toAdd).smul_right t.toAdd)

@[simp] theorem unitaryFlow_apply (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) :
    (unitaryFlow J K hJ hK hJK (Multiplicative.ofAdd t) : A) =
      NormedSpace.exp (t • generator J K) := rfl

/-- Native real star-algebra automorphisms, including their proved inverse and group law. -/
noncomputable def phaseFlow (J K : A) (hJ : star J = -J) (hK : star K = K)
    (hJK : Commute J K) : Multiplicative ℝ →* (A ≃⋆ₐ[ℝ] A) :=
  (Unitary.conjStarAlgAut ℝ A).comp (unitaryFlow J K hJ hK hJK)

/-- The native automorphism is exactly the existing exponential transport path. -/
theorem phaseFlow_apply_eq_expTransport (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) (x : A) :
    phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t) x =
      expTransport (generator J K) x t := by
  change NormedSpace.exp (t • generator J K) * x *
    star (NormedSpace.exp (t • generator J K)) = _
  rw [NormedSpace.star_exp]
  simp only [star_smul, star_trivial, generator_star J K hJ hK hJK]
  rfl

/-- The negative-time map is the actual inverse star-algebra equivalence. -/
theorem phaseFlow_neg (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) :
    phaseFlow J K hJ hK hJK (Multiplicative.ofAdd (-t)) =
      (phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t)).symm := by
  exact map_inv (phaseFlow J K hJ hK hJK) (Multiplicative.ofAdd t)

/-- The exponential has the already constructed real inner derivation as its generator. -/
theorem hasDerivAt_phaseFlow_zero (J K x : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) :
    HasDerivAt (fun t : ℝ => phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t) x)
      (innerDerivative (R := ℝ) (generator J K) x) 0 := by
  simp_rw [phaseFlow_apply_eq_expTransport]
  simpa only [Ring.lie_def, innerDerivative, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
    hasDerivAt_expTransport_at_zero (generator J K) x

/-- The derivative at arbitrary time is the flow applied to the same inner derivation. -/
theorem hasDerivAt_phaseFlow (J K x : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseFlow J K hJ hK hJK (Multiplicative.ofAdd s) x)
      (phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t)
        (innerDerivative (R := ℝ) (generator J K) x)) t := by
  simp_rw [phaseFlow_apply_eq_expTransport]
  simpa only [Ring.lie_def, innerDerivative, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
    hasDerivAt_expTransport (generator J K) x t

/-- The internal phase is fixed by the constructed automorphism group. -/
theorem phaseFlow_fixes_phase (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) :
    phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t) J = J := by
  rw [phaseFlow_apply_eq_expTransport]
  exact expTransport_eq_self_of_commute _ _ _ (generator_commutes_phase J K hJK)

/-- Finite-time dynamics preserves the same native centralizer as the infinitesimal generator. -/
theorem phaseFlow_mem_phaseAlgebra (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (t : ℝ) (x : phaseAlgebra J) :
    phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t) (x : A) ∈ phaseAlgebra J := by
  apply (mem_phaseAlgebra_iff _ _).mpr
  rw [commute_iff_eq]
  have hx := (mem_phaseAlgebra_iff _ _).mp x.2
  have ht := congrArg (phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t)) hx.eq
  simpa only [map_mul, phaseFlow_fixes_phase J K hJ hK hJK t] using ht

/-- On phase-preserving observables, the analytic generator equals the restricted derivation. -/
theorem hasDerivAt_phaseFlow_phaseAlgebra (J K : A) (hJ : star J = -J)
    (hK : star K = K) (hJK : Commute J K) (x : phaseAlgebra J) :
    HasDerivAt (fun t : ℝ => phaseFlow J K hJ hK hJK (Multiplicative.ofAdd t) (x : A))
      (phaseDerivation J K hJK x : A) 0 :=
  hasDerivAt_phaseFlow_zero J K (x : A) hJ hK hJK

end

end InfoGeometry.OperatorAlgebra.RealPhaseExponentialFlow
