module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Flat.Localization

namespace LinearMap

theorem baseChangeHom_injective_of_flat_of_free
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Flat R S] [FaithfulSMul R S] [Module.Free R M] :
    Function.Injective (LinearMap.baseChangeHom R S M M) := by
  let b := Module.Free.chooseBasis R M
  have hb : LinearIndependent S (fun i => (1 : S) ⊗ₜ[R] b i) :=
    Module.Flat.linearIndependent_one_tmul b.linearIndependent
  intro f g h
  apply Module.Basis.ext b
  intro i
  have hi := LinearMap.congr_fun h ((1 : S) ⊗ₜ[R] b i)
  have hi' : (1 : S) ⊗ₜ[R] f (b i) = (1 : S) ⊗ₜ[R] g (b i) := by
    simpa only [LinearMap.baseChangeHom_apply] using hi
  have hi_repr := congrArg ((b.baseChange S).repr) hi'
  simp only [Module.Basis.baseChange_repr_tmul] at hi_repr
  have hcoeff : b.repr (f (b i)) = b.repr (g (b i)) := by
    ext j
    apply (FaithfulSMul.algebraMap_injective R S)
    simpa only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
      using congrArg (fun q => q j) hi_repr
  exact b.repr.injective hcoeff

end LinearMap
