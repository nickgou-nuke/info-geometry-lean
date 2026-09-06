import InfoGeometry.Canonical.CuntzGNSFilteredSystem
import InfoGeometry.Canonical.FilteredGNSTomitaModularForm

/-!
# Cuntz filtered GNS Tomita-form bridge

This is the honest modular-theoretic boundary of the current Cuntz data.  A
stagewise closability witness is an explicit input; from it we transport the
native closed Tomita form through the Cuntz GNS colimit.  No bounded modular
operator or Tomita--Takesaki completion is postulated here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzGNSFilteredTomitaBridge

open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzGNSFilteredSystem
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
open CStarStateColimit.Native.FilteredGNSTomitaModularForm

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

/-- The stagewise closed Tomita modular form for the Cuntz GNS family. -/
def cuntzClosedTomitaModularForm (n : ℕ) :
    closedTomitaDomain (ω.state n) →ₛₗ[starRingEnd ℂ]
      closedTomitaDomain (ω.state n) →ₗ[ℂ] ℂ :=
  closedTomitaModularForm Stage (cuntzSystem Stage T) ω hclos n

@[simp] theorem cuntzClosedTomitaModularForm_apply
    (n : ℕ) (x y : closedTomitaDomain (ω.state n)) :
    cuntzClosedTomitaModularForm Stage T ω hclos n x y =
      inner ℂ
        (closedTomitaOperator (ω.state n) (hclos n) y)
        (closedTomitaOperator (ω.state n) (hclos n) x) :=
  closedTomitaModularForm_apply Stage (cuntzSystem Stage T) ω hclos n x y

theorem cuntzClosedTomitaModularForm_nonneg
    (n : ℕ) (x : closedTomitaDomain (ω.state n)) :
    0 ≤ Complex.re (cuntzClosedTomitaModularForm Stage T ω hclos n x x) :=
  closedTomitaModularForm_nonneg Stage (cuntzSystem Stage T) ω hclos n x

theorem cuntzFilteredClosedTomitaForm_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x y : closedTomitaDomain (ω.state m)) :
    cuntzClosedTomitaModularForm Stage T ω hclos n
        (filteredClosedTomitaDomainMap
          Stage (cuntzSystem Stage T) ω hmn x)
        (filteredClosedTomitaDomainMap
          Stage (cuntzSystem Stage T) ω hmn y) =
      cuntzClosedTomitaModularForm Stage T ω hclos m x y :=
  filteredClosedTomitaDomainMap_preserves_modularForm
    Stage (cuntzSystem Stage T) ω hclos hmn x y

end InfoGeometry.Canonical.CuntzGNSFilteredTomitaBridge
