import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport
import InfoGeometry.Canonical.CalogeroMoserZeroRepulsion

/-!
# Calogero--Moser interaction on the Hestenes--Krein colimit

This owner transports the finite real inverse-distance interaction kernel to
canonical Hestenes--Krein colimit images.  It records only finite pair
energies and explicit position-readout compatibility; it does not construct a
root flow or prove collision avoidance for an analytic zero family.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinCalogeroColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity
open InfoGeometry.Canonical.CalogeroMoserZeroRepulsion
open InfoGeometry.Krein
open scoped BigOperators

def stagePairEnergy
    {C : HestenesKreinCone} {N : ℕ}
    (position : ∀ n, Fin N → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  finitePairEnergy (fun i => position n i x)

def limitPairEnergy
    {C : HestenesKreinCone} {N : ℕ}
    (position : Fin N → DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  finitePairEnergy (fun i => position i x)

theorem stagePairEnergy_eq_limitPairEnergy
    {C : HestenesKreinCone} {N : ℕ}
    (position : ∀ n, Fin N → DoubledSpace (C.Base n) → ℝ)
    (limitPosition : Fin N → DoubledSpace C.LimitBase → ℝ)
    (hposition : ∀ n i x, position n i x = limitPosition i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stagePairEnergy position n x = limitPairEnergy limitPosition (C.ι n x) := by
  unfold stagePairEnergy limitPairEnergy
  apply congrArg finitePairEnergy
  funext i
  rw [hposition n i x]

theorem stagePairEnergy_bondIterate_eq
    {C : HestenesKreinCone} {N : ℕ}
    (position : ∀ n, Fin N → DoubledSpace (C.Base n) → ℝ)
    (hposition : ∀ n m i x,
      position (n + m) i
          (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
        position n i x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    stagePairEnergy position (n + m)
        (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m x) =
      stagePairEnergy position n x := by
  unfold stagePairEnergy
  congr 1
  funext i
  rw [hposition n m i x]

theorem stagePairEnergy_nonneg
    {C : HestenesKreinCone} {N : ℕ}
    (position : ∀ n, Fin N → DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ stagePairEnergy position n x := by
  exact finitePairEnergy_nonneg (fun i => position n i x)

theorem limitPairEnergy_nonneg_of_stage
    {C : HestenesKreinCone} {N : ℕ}
    (position : ∀ n, Fin N → DoubledSpace (C.Base n) → ℝ)
    (limitPosition : Fin N → DoubledSpace C.LimitBase → ℝ)
    (hposition : ∀ n i x, position n i x = limitPosition i (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ limitPairEnergy limitPosition (C.ι n x) := by
  rw [← stagePairEnergy_eq_limitPairEnergy position limitPosition hposition n x]
  exact stagePairEnergy_nonneg position n x

end InfoGeometry.Canonical.HestenesKreinCalogeroColimit

end noncomputable section
