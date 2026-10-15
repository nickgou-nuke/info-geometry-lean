module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

namespace LinearMap

theorem baseChangeHom_injective_of_flat_of_free
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R S] [FaithfulSMul R S] [Module.Free R M] :
    Function.Injective (LinearMap.baseChangeHom R S M M) :=
  LinearMap.baseChangeHom_injective R M S

end LinearMap

