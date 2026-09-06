import InfoGeometry.LinearAlgebra.TraceUpperTriangular
import Mathlib.LinearAlgebra.Projection

noncomputable section

namespace InfoGeometry.LinearAlgebra.TraceInvariantSubmodule

open InfoGeometry.LinearAlgebra.TraceUpperTriangular

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

def invariantRestriction
    (T : Module.End ℝ V)
    (S : Submodule ℝ V)
    (hS : S ≤ Submodule.comap T S) :
    Module.End ℝ S :=
  T.restrict fun _ hx => hS hx

def invariantQuotientMap
    (T : Module.End ℝ V)
    (S : Submodule ℝ V)
    (hS : S ≤ Submodule.comap T S) :
    Module.End ℝ (V ⧸ S) :=
  Submodule.mapQ S S T hS

def transportedEndomorphism
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q) :
    Module.End ℝ (S × Q) :=
  (S.prodEquivOfIsCompl Q hSQ).symm.conj T

def transportedUpperLeft
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q) :
    Module.End ℝ S :=
  (LinearMap.fst ℝ S Q).comp
    ((transportedEndomorphism T S Q hSQ).comp
      (LinearMap.inl ℝ S Q))

def transportedUpperRight
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q) :
    Q →ₗ[ℝ] S :=
  (LinearMap.fst ℝ S Q).comp
    ((transportedEndomorphism T S Q hSQ).comp
      (LinearMap.inr ℝ S Q))

def transportedLowerRight
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q) :
    Module.End ℝ Q :=
  (LinearMap.snd ℝ S Q).comp
    ((transportedEndomorphism T S Q hSQ).comp
      (LinearMap.inr ℝ S Q))

theorem endomorphism_eq_upperTriangular_of_lowerLeft_zero
    {M N : Type*}
    [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N]
    (F : Module.End ℝ (M × N))
    (hLower : ∀ x : M, (F (x, 0)).2 = 0) :
    F =
      upperTriangular
        ((LinearMap.fst ℝ M N).comp
          (F.comp (LinearMap.inl ℝ M N)))
        ((LinearMap.fst ℝ M N).comp
          (F.comp (LinearMap.inr ℝ M N)))
        ((LinearMap.snd ℝ M N).comp
          (F.comp (LinearMap.inr ℝ M N))) := by
  apply LinearMap.ext
  intro x
  rw [upperTriangular_apply]
  simp only [LinearMap.comp_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]
  rw [← show (x.1, 0) + (0, x.2) = x by ext <;> simp, map_add]
  apply Prod.ext
  · simp
  · simp [hLower]

theorem transported_lowerLeft_zero
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (hS : S ≤ Submodule.comap T S) :
    ∀ x : S, ((transportedEndomorphism T S Q hSQ) (x, 0)).2 = 0 := by
  intro x
  let e : (S × Q) ≃ₗ[ℝ] V := S.prodEquivOfIsCompl Q hSQ
  have hTx : T x ∈ S := hS x.2
  have hDecomp :
      e.symm (T x) = (⟨T x, hTx⟩, 0) := by
    apply e.injective
    rw [e.apply_symm_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  change (e.symm (T (e (x, 0)))).2 = 0
  rw [show e (x, 0) = (x : V) by
    simp [e, Submodule.coe_prodEquivOfIsCompl'], hDecomp]

theorem transportedEndomorphism_eq_upperTriangular
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (hS : S ≤ Submodule.comap T S) :
    transportedEndomorphism T S Q hSQ =
      upperTriangular
        (transportedUpperLeft T S Q hSQ)
        (transportedUpperRight T S Q hSQ)
        (transportedLowerRight T S Q hSQ) := by
  exact endomorphism_eq_upperTriangular_of_lowerLeft_zero
    (transportedEndomorphism T S Q hSQ)
    (transported_lowerLeft_zero T S Q hSQ hS)

theorem transportedUpperLeft_eq_invariantRestriction
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (hS : S ≤ Submodule.comap T S) :
    transportedUpperLeft T S Q hSQ =
      invariantRestriction T S hS := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let e : (S × Q) ≃ₗ[ℝ] V := S.prodEquivOfIsCompl Q hSQ
  have hTx : T x ∈ S := hS x.2
  have hDecomp :
      e.symm (T x) = (⟨T x, hTx⟩, 0) := by
    apply e.injective
    rw [e.apply_symm_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  change (e.symm (T (e (x, 0)))).1.1 = T x
  rw [show e (x, 0) = (x : V) by
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp, hDecomp]

theorem quotientEquiv_apply_mk_eq_snd_prodEquiv_symm
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (v : V) :
    (S.quotientEquivOfIsCompl Q hSQ) (Submodule.Quotient.mk v) =
      ((S.prodEquivOfIsCompl Q hSQ).symm v).2 := by
  let e : (S × Q) ≃ₗ[ℝ] V := S.prodEquivOfIsCompl Q hSQ
  let q : (V ⧸ S) ≃ₗ[ℝ] Q := S.quotientEquivOfIsCompl Q hSQ
  apply q.symm.injective
  rw [q.symm_apply_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  apply (Submodule.Quotient.eq S).2
  have hv : v = e (e.symm v) := (e.apply_symm_apply v).symm
  rw [show v - ((e.symm v).2 : V) =
      ((e.symm v).1 : V) by
    nth_rewrite 1 [hv]
    rw [Submodule.coe_prodEquivOfIsCompl']
    abel]
  exact (e.symm v).1.2

theorem transportedLowerRight_eq_quotientConj
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (hS : S ≤ Submodule.comap T S) :
    transportedLowerRight T S Q hSQ =
      (S.quotientEquivOfIsCompl Q hSQ).conj
        (invariantQuotientMap T S hS) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let e : (S × Q) ≃ₗ[ℝ] V := S.prodEquivOfIsCompl Q hSQ
  let q : (V ⧸ S) ≃ₗ[ℝ] Q := S.quotientEquivOfIsCompl Q hSQ
  change (e.symm (T (e (0, x)))).2.1 =
    (q (invariantQuotientMap T S hS (q.symm x))).1
  rw [show e (0, x) = (x : V) by
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp]
  rw [show q.symm x = Submodule.Quotient.mk (x : V) by
    exact Submodule.quotientEquivOfIsCompl_symm_apply S Q hSQ x]
  change (e.symm (T x)).2.1 =
    (q (Submodule.Quotient.mk (T x))).1
  rw [quotientEquiv_apply_mk_eq_snd_prodEquiv_symm S Q hSQ]

theorem trace_eq_transported_diagonal
    [FiniteDimensional ℝ V]
    (T : Module.End ℝ V)
    (S Q : Submodule ℝ V)
    (hSQ : IsCompl S Q)
    (hS : S ≤ Submodule.comap T S) :
    LinearMap.trace ℝ V T =
      LinearMap.trace ℝ S (transportedUpperLeft T S Q hSQ) +
        LinearMap.trace ℝ Q (transportedLowerRight T S Q hSQ) := by
  let e : (S × Q) ≃ₗ[ℝ] V := S.prodEquivOfIsCompl Q hSQ
  have hConj :
      LinearMap.trace ℝ (S × Q) (e.symm.conj T) =
        LinearMap.trace ℝ V T :=
    LinearMap.trace_conj' T e.symm
  rw [← hConj, show e.symm.conj T =
      transportedEndomorphism T S Q hSQ by rfl,
    transportedEndomorphism_eq_upperTriangular T S Q hSQ hS,
    trace_upperTriangular]

theorem trace_eq_trace_restriction_add_trace_quotient
    [FiniteDimensional ℝ V]
    (T : Module.End ℝ V)
    (S : Submodule ℝ V)
    (hS : S ≤ Submodule.comap T S) :
    LinearMap.trace ℝ V T =
      LinearMap.trace ℝ S (invariantRestriction T S hS) +
        LinearMap.trace ℝ (V ⧸ S)
          (invariantQuotientMap T S hS) := by
  obtain ⟨Q, hSQ⟩ := Submodule.exists_isCompl S
  rw [trace_eq_transported_diagonal T S Q hSQ hS,
    transportedUpperLeft_eq_invariantRestriction T S Q hSQ hS,
    transportedLowerRight_eq_quotientConj T S Q hSQ hS]
  rw [LinearMap.trace_conj'
    (invariantQuotientMap T S hS)
    (S.quotientEquivOfIsCompl Q hSQ)]

end InfoGeometry.LinearAlgebra.TraceInvariantSubmodule
