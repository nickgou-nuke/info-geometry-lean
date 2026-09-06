module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Algebra.Lie.TraceForm
public import InfoGeometry.Lie.MathlibBackportBasisLieEnd
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Project-owned trace-form scalar extension lemma

The pinned Mathlib snapshot already contains the Lie-module base-change
instances, `toEnd_baseChange`, and `LinearMap.trace_baseChange`, but predates
the corresponding trace-form transport lemma.  This file supplies that one
missing theorem without modifying the pinned dependency.
-/

open scoped TensorProduct

noncomputable section
public section

namespace InfoGeometry.Lie.MathlibBackport

open LieModule LieAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

lemma coe_derivedSeries_one_eq :
    derivedSeries R L 1 = Submodule.span R {⁅x, y⁆ | (x : L) (y : L)} := by
  ext z
  simp only [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span']
  aesop

end LieAlgebra

namespace LinearMap

lemma trace_lie_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g h : M →ₗ[R] M) : _root_.LinearMap.trace R M (⁅f, g⁆ * h) =
      _root_.LinearMap.trace R M (f * ⁅g, h⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [_root_.LinearMap.trace_mul_comm R g (f * h), mul_assoc]

end LinearMap

lemma trace_toEnd_mul_eq_zero_of_traceForm_eq_zero
    [Module.Free R M] (h : traceForm R L M = 0)
    (y : Module.End R M)
    (hy : ∀ z ∈ LieHom.range (toEnd R L M), ⁅y, z⁆ ∈ LieHom.range (toEnd R L M))
    (x : L) (hx : x ∈ LieAlgebra.derivedSeries R L 1) :
    _root_.LinearMap.trace R M (toEnd R L M x * y) = 0 := by
  replace hx : x ∈ Submodule.span R {⁅u, v⁆ | (u : L) (v : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]
    exact hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c : L, hbc : toEnd R L M c = ⁅y, toEnd R L M b⁆⟩ :=
      hy (toEnd R L M b) (LieHom.mem_range_self (toEnd R L M) b)
    replace hbc : ⁅toEnd R L M b, y⁆ = -toEnd R L M c := by
      calc
        ⁅toEnd R L M b, y⁆ = -⁅y, toEnd R L M b⁆ := (lie_skew _ _).symm
        _ = -toEnd R L M c := by rw [hbc]
    rw [LieHom.map_lie, InfoGeometry.Lie.MathlibBackport.LinearMap.trace_lie_mul_eq,
      Ring.lie_def,
      ← LieRing.of_associative_ring_bracket, hbc, mul_neg, map_neg,
      neg_eq_zero, Module.End.mul_eq_comp, ← traceForm_apply_apply, h,
      LinearMap.zero_apply, LinearMap.zero_apply]
  | zero => simp
  | add u v _ _ hu hv => simp [add_mul, hu, hv]
  | smul t u _ hu => simp [hu]

theorem traceForm_baseChange
    {R L M A : Type*}
    [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [Module.Free R M] [Module.Finite R M]
    [CommRing A] [Algebra R A] :
    LieModule.traceForm A (A ⊗[R] L) (A ⊗[R] M) =
      (LieModule.traceForm R L M).baseChange A := by
  ext x y
  simp [LieModule.traceForm_apply_apply, ← LinearMap.baseChange_comp,
    LieModule.toEnd_baseChange, Algebra.algebraMap_eq_smul_one]

theorem bilinForm_baseChange_zero
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    LinearMap.BilinForm.baseChange A (0 : LinearMap.BilinForm R M) = 0 := by
  apply LinearMap.BilinForm.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' m' => simp [LinearMap.BilinForm.baseChange_tmul]
    | add y z hy hz => simp [hy, hz]
  | add x y hx hy => simp [hx, hy]

end MathlibBackport

end Lie

end InfoGeometry
