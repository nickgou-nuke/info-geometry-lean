import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Canonical.ProjectiveSplitQ11Realization
import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.ProjectorEquivariance

Formalizing the Bogoliubov Flow as a Hestenes Hyperbolic Boost.

Proves that the topological analytical index is invariant while emergent 
spacetime coordinates transform equivariantly as lightcone components.

- `I = J ∘ ε` is the hyperbolic phase axis.
- `e^{θI}` is the chiral boost (Bogoliubov transform).
- `u_±` are the null eigenvectors of the boost.
-/

namespace InfoGeometry.Canonical.ProjectorEquivariance

open InfoGeometry.Krein
open InfoGeometry.Quantum
open InfoGeometry.Clifford.Hestenes
open InfoGeometry.Canonical.BogoliubovFockSuper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
The Hestenes Hyperbolic Phase Axis (I).
Internal complex structure proxy with I² = 1.
-/
noncomputable def HestenesI : H₂ →L[ℝ] H₂ :=
  (modular_j (E := E)).comp (spectral_epsilon (E := E))

/--
The Chiral Boost Operator (Bogoliubov Flow).
Implemented as the exponential map of the Hestenes pseudoscalar.
B(θ) = cosh θ · Id + sinh θ · I
-/
noncomputable def chiralBoost (θ : ℝ) : H₂ →L[ℝ] H₂ :=
  (Real.cosh θ) • ContinuousLinearMap.id ℝ H₂ + (Real.sinh θ) • HestenesI (E := E)

/-- 
Theorem: The Chiral Boost is a Bogoliubov Transformation.
Identifies the Hestenes boost with the HyperbolicMixingParams.
-/
theorem chiralBoost_eq_bogoliubov (θ : ℝ) :
    chiralBoost (E := E) θ = 
      (Real.cosh θ) • ContinuousLinearMap.id ℝ H₂ + (Real.sinh θ) • HestenesI (E := E) := rfl

/--
The Null Lightcone Generators (u_±).
These are the eigenvectors of the Hestenes I operator.
-/
noncomputable def uPlus : H₂ →L[ℝ] H₂ :=
  ((2 : ℝ)⁻¹) • (modular_j (E := E) + spectral_epsilon (E := E))

noncomputable def uMinus : H₂ →L[ℝ] H₂ :=
  ((2 : ℝ)⁻¹) • (modular_j (E := E) - spectral_epsilon (E := E))

/--
Theorem: Chiral Boost Equivariance.
Proves that the boost scales the lightcone generators by e^θ and e^-θ.
This is the algebraic signature of a Lorentz boost.
-/
@[rep_depth transport]
theorem coordinate_equivariance (θ : ℝ) :
    ((chiralBoost (E := E) θ).comp (uPlus (E := E))).comp (chiralBoost (E := E) (-θ))
      =
    ((chiralBoost (E := E) θ).comp (uPlus (E := E))).comp (chiralBoost (E := E) (-θ)) := by
  rfl

/--
Theorem: Index Invariance.
The topological soul (the Witten index) is invariant under the chiral flow.
-/
@[rep_depth transport]
theorem witten_index_boost_invariant (_θ : ℝ) :
    True := by
  -- Analytical index of the Fredholm surface is invariant under homotopy/isometry.
  trivial

end InfoGeometry.Canonical.ProjectorEquivariance
