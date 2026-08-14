import InfoGeometry.Twistor.Cl55ProjectivizationTopology
import InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
import InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem

/-!
# Concrete covering reduction for the `Cl(5,5)` projective-null carrier

This owner proves continuity of the native split quadratic form `Q55` and
specializes the finite permutation covering theorem to its projective-null
configuration spaces.  The ambient projectivization hypotheses are discharged
by the native compact Hausdorff topology proved in
`Cl55ProjectivizationTopology`.

No fundamental-group computation, braid identification, monodromy, or anyon
interpretation is asserted here.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor
open InfoGeometry.Twistor.Cl55ProjectivizationTopology
open InfoGeometry.Twistor.ProjectiveNullBoundaryTopology
open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCovering
open InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

/-- The native split quadratic form of signature `(5,5)` is continuous in its
finite-dimensional real coordinate topology. -/
theorem continuous_Q55 : Continuous (Q55 : V55 → ℝ) := by
  change Continuous (fun v : V55 => Q55 v)
  simp_rw [Q55_apply]
  fun_prop

/-- Ambient local compactness of the quotient projectivization descends to
the concrete `Q55` projective-null boundary. -/
theorem q55NullBoundary_locallyCompactSpace
    : @LocallyCompactSpace (TwistorSpace Q55) (nullBoundaryTopology Q55) :=
  nullBoundary_locallyCompactSpace Q55 continuous_Q55
    q55Projectivization_locallyCompactSpace

/-- Ambient Hausdorffness of the quotient projectivization descends to the
concrete `Q55` projective-null boundary. -/
theorem q55NullBoundary_t2Space
    : @T2Space (TwistorSpace Q55) (nullBoundaryTopology Q55) :=
  nullBoundary_t2Space Q55 q55Projectivization_t2Space

/-- Ordered distinct `Q55` null configurations are locally compact. -/
theorem q55OrderedConfiguration_locallyCompactSpace (n : ℕ) :
    @LocallyCompactSpace (Ordered Q55 n)
      (orderedConfigurationTopology Q55 n) :=
  orderedConfiguration_locallyCompactSpace Q55 n
    q55NullBoundary_locallyCompactSpace q55NullBoundary_t2Space

/-- Ordered distinct `Q55` null configurations are Hausdorff. -/
theorem q55OrderedConfiguration_t2Space (n : ℕ) :
    @T2Space (Ordered Q55 n) (orderedConfigurationTopology Q55 n) :=
  orderedConfiguration_t2Space Q55 n q55NullBoundary_t2Space

/-- The ordered-to-unordered projection for distinct `Q55` null lines is a
finite permutation quotient covering map. -/
theorem q55UnorderedProjection_isQuotientCoveringMap
    (n : ℕ) :
    let _ := orderedConfigurationTopology Q55 n
    let _ := unorderedConfigurationTopology Q55 n
    IsQuotientCoveringMap
      (@Quotient.mk' (Ordered Q55 n) (reindexSetoid Q55 n))
      (Equiv.Perm (Fin n)) := by
  exact unorderedProjection_isQuotientCoveringMap_of_projectivization
    Q55 n continuous_Q55 q55Projectivization_locallyCompactSpace
      q55Projectivization_t2Space

/-! The finite fiber cardinality of the concrete `Q55` covering. -/
theorem q55OrderedConfigurationFiber_finrank
    {F : Type*} [Field F] (n : ℕ) (p : Ordered Q55 n) :
    Module.finrank F
        ({q : Ordered Q55 n //
          Quotient.mk' q = (Quotient.mk' p : Unordered Q55 n)} →₀ F) =
      n.factorial := by
  exact unorderedConfigurationCoveringFiber_finrank Q55 n p

end InfoGeometry.Twistor.Cl55RealSplitPinNullConfigurationCovering
