import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.CuntzGNSFilteredSystem
import InfoGeometry.Canonical.CuntzGNSFilteredTomitaBridge
import InfoGeometry.Canonical.CuntzGNSFilteredTomitaColimit
import InfoGeometry.Canonical.FilteredGNSTomitaClosedTransport
import InfoGeometry.Canonical.FilteredGNSTomitaRealColimit

open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzGNSFilteredSystem
open InfoGeometry.Canonical.CuntzGNSFilteredTomitaBridge
open InfoGeometry.Canonical.CuntzGNSFilteredTomitaColimit
open CStarStateColimit
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSTomitaRealColimit

noncomputable section

namespace InfoGeometry.Canonical.UHFTomitaTakesakiColimitBridge

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage (cuntzSystem Stage T))

/-- The stagewise closed Tomita modular form for the non-commutative Cuntz GNS family. -/
def uhfClosedTomitaModularForm
    (hclos : ∀ n, IsClosableTomitaCore (ω.state n)) (n : ℕ) :
    closedTomitaDomain (ω.state n) →ₛₗ[starRingEnd ℂ]
      closedTomitaDomain (ω.state n) →ₗ[ℂ] ℂ :=
  cuntzClosedTomitaModularForm Stage T ω hclos n

/-- Non-negativity of the descended Tomita modular form q(x, x) ≥ 0 on each stage n. -/
theorem uhfClosedTomitaModularForm_nonneg
    (hclos : ∀ n, IsClosableTomitaCore (ω.state n)) (n : ℕ)
    (x : closedTomitaDomain (ω.state n)) :
    0 ≤ Complex.re (uhfClosedTomitaModularForm Stage T ω hclos n x x) :=
  cuntzClosedTomitaModularForm_nonneg Stage T ω hclos n x

/-- Functorial transition preservation of the Tomita modular form across the GNS colimit tower. -/
theorem uhfClosedTomitaModularForm_transition
    (hclos : ∀ n, IsClosableTomitaCore (ω.state n))
    {m n : ℕ} (hmn : m ≤ n)
    (x y : closedTomitaDomain (ω.state m)) :
    uhfClosedTomitaModularForm Stage T ω hclos n
        (filteredClosedTomitaDomainMap Stage (cuntzSystem Stage T) ω hmn x)
        (filteredClosedTomitaDomainMap Stage (cuntzSystem Stage T) ω hmn y) =
      uhfClosedTomitaModularForm Stage T ω hclos m x y :=
  cuntzFilteredClosedTomitaForm_transition Stage T ω hclos hmn x y

/-- Real categorical colimit operator for the Tomita involutive core over the Cuntz GNS colimit. -/
def uhfClosedTomitaColimitOperator
    (hclos : ∀ n, IsClosableTomitaCore (ω.state n)) :
    CuntzClosedTomitaDomainRealColimit Stage T ω →ₗ[ℝ]
      CuntzGNSRealColimit Stage T ω :=
  cuntzClosedTomitaRealColimitOperator Stage T ω hclos

end InfoGeometry.Canonical.UHFTomitaTakesakiColimitBridge
