import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Hadjiivanov--Hestenes--Krein filtered descent

This owner uses the repository's canonical doubled filtered cone directly.
-/

noncomputable section

namespace InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Canonical.HestenesAnalyticity
open InfoGeometry.Canonical.FilteredInductiveHestenesAnalyticity

variable (C : HestenesKreinCone)

theorem bond_phase_linear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.bond n) (clockPhaseStructure (C.Base (n + 1))) :=
  C.bond_hestenes n

theorem inclusion_phase_linear {n : ℕ} :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (C.ι n) (clockPhaseStructure C.LimitBase) :=
  C.ι_hestenes n

theorem inclusion_bond_iterate (n m : ℕ)
    (x : DoubledSpace (C.Base n)) :
    C.ι (n + m) (FilteredPhaseCone.bondIterate
      C.toFilteredPhaseCone n m x) = C.ι n x := by
  exact FilteredPhaseCone.ι_bondIterate_apply C.toFilteredPhaseCone n m x

theorem bond_iterate_phase_linear (n m : ℕ) :
    (clockPhaseStructure (C.Base n)).IsPhaseLinearMap
      (FilteredPhaseCone.bondIterate C.toFilteredPhaseCone n m)
      (clockPhaseStructure (C.Base (n + m))) := by
  exact FilteredPhaseCone.bondIterate_phaseLinear C.toFilteredPhaseCone n m

end InfoGeometry.Projective.HadjiivanovHestenesKreinFilteredColimit
