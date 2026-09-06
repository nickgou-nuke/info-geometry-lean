import InfoGeometry.Canonical.DiracSouriauOperator

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DiracSouriau

example : AddCommGroup (ZornMatrix ℝ) :=
  inferInstance

example : Module ℝ (ZornMatrix ℝ) :=
  inferInstance

example (z : ZornMatrix ℝ) :
    z.coarseGrain = !![z.a, 0; 0, z.b] :=
  rfl

example (S : DiracSouriauSector ℝ) :
    ∃ k, S.HasDrazinInverse k :=
  DiracSouriauSector.hasDrazinInverse_of_field S
