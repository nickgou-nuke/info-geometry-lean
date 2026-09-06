import InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy

/-!
# Linear monodromy associated to the configuration deck group

The ordered-to-unordered configuration covering already supplies a concrete
permutation monodromy `pi_1 -> S_n`.  Composing it with any supplied linear
representation of `S_n` gives a genuine associated linear monodromy.  An
explicit ordered exchange path is evaluated by the representation of its
endpoint permutation.

This construction sees exactly the finite deck quotient.  It does not assert
that an arbitrary Artin or Yang--Baxter representation factors through `S_n`.
-/

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy

open InfoGeometry.Twistor.ProjectiveNullConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangeDeckMonodromy
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {R K V H : Type*} [Semiring R] [AddCommMonoid H] [Module R H]
variable [Field K] [AddCommGroup V] [Module K V]

/-- Linear monodromy associated to a representation of the finite deck group
`S_n`. -/
def associatedDeckLinearMonodromy
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n)
    (rho : Equiv.Perm (Fin n) →*
      LinearMap.GeneralLinearGroup R H) :
    @FundamentalGroup (Unordered Q n)
        (unorderedConfigurationTopology Q n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup R H :=
  rho.comp (unorderedCoveringPermutationMonodromy Q n hLC hT2 p)

/-- Associated monodromy of an explicit ordered exchange is exactly the
chosen deck-group representation evaluated at its endpoint permutation. -/
@[simp] theorem associatedDeckLinearMonodromy_orderedExchangeLoopClass
    [TopologicalSpace V]
    (Q : QuadraticForm K V) (n : ℕ)
    (hLC : @LocallyCompactSpace (Ordered Q n)
      (orderedConfigurationTopology Q n))
    (hT2 : @T2Space (Ordered Q n) (orderedConfigurationTopology Q n))
    (p : Ordered Q n) (sigma : Equiv.Perm (Fin n))
    (gamma : @Path (Ordered Q n) (orderedConfigurationTopology Q n)
      p (permute Q n sigma p))
    (rho : Equiv.Perm (Fin n) →*
      LinearMap.GeneralLinearGroup R H) :
    associatedDeckLinearMonodromy Q n hLC hT2 p rho
        (orderedExchangeLoopClass Q n p sigma gamma) = rho sigma := by
  rw [associatedDeckLinearMonodromy, MonoidHom.comp_apply,
    unorderedCoveringPermutationMonodromy_orderedExchangeLoopClass]

end InfoGeometry.Twistor.ProjectiveNullConfigurationAssociatedDeckMonodromy
