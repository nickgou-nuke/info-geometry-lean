import InfoGeometry.Canonical.CuntzGNSFilteredTomitaBridge
import InfoGeometry.Canonical.FilteredGNSTomitaRealColimit

/-!
# Cuntz real Tomita colimit

The finite closed Tomita operators are descended through the native real
`ModuleCat` colimit.  This exposes the categorical operator and its stage
inclusion law; it does not identify the result with a bounded modular
operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzGNSFilteredTomitaColimit

open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzGNSFilteredSystem
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaRealColimit

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
    Stage (cuntzSystem Stage T))
variable
  (hclos : ∀ n, IsClosableTomitaCore (ω.state n))

/-- Real categorical colimit of the Cuntz closed Tomita domains. -/
abbrev CuntzClosedTomitaDomainRealColimit : Type :=
  ClosedTomitaDomainRealColimit Stage (cuntzSystem Stage T) ω

/-- Real categorical colimit of the Cuntz completed GNS stages. -/
abbrev CuntzGNSRealColimit : Type :=
  GNSRealColimit Stage (cuntzSystem Stage T) ω

/-- The descended real-linear closed Tomita operator. -/
def cuntzClosedTomitaRealColimitOperator :
    CuntzClosedTomitaDomainRealColimit Stage T ω →ₗ[ℝ]
      CuntzGNSRealColimit Stage T ω :=
  closedTomitaRealColimitOperator
    Stage (cuntzSystem Stage T) ω hclos

/-- Canonical inclusion of a stage closed Tomita domain. -/
def cuntzClosedTomitaDomainRealInclusion (n : ℕ) :
    closedTomitaDomain (ω.state n) →ₗ[ℝ]
      CuntzClosedTomitaDomainRealColimit Stage T ω :=
  closedTomitaDomainRealInclusion
    Stage (cuntzSystem Stage T) ω n

/-- Canonical inclusion of a completed stage GNS space. -/
def cuntzGNSRealInclusion (n : ℕ) :
    (ω.state n).functional.GNS →ₗ[ℝ]
      CuntzGNSRealColimit Stage T ω :=
  gnsRealInclusion Stage (cuntzSystem Stage T) ω n

theorem cuntzClosedTomitaRealColimitOperator_inclusion
    (n : ℕ) (x : closedTomitaDomain (ω.state n)) :
    cuntzClosedTomitaRealColimitOperator Stage T ω hclos
        (cuntzClosedTomitaDomainRealInclusion Stage T ω n x) =
      cuntzGNSRealInclusion Stage T ω n
        (closedTomitaOperator (ω.state n) (hclos n) x) :=
  closedTomitaRealColimitOperator_inclusion
    Stage (cuntzSystem Stage T) ω hclos n x

end InfoGeometry.Canonical.CuntzGNSFilteredTomitaColimit
