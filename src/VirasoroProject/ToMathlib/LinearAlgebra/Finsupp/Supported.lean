import Mathlib.LinearAlgebra.Finsupp.Supported
--import Mathlib

lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  let f : ι → V := fun i ↦ cfs i • vs i
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ (cfs i)
      (Submodule.subset_span (Set.mem_range_self i))
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

lemma finsum_mem_mem_span {ι R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  let f : ι → V := fun i ↦ cfs i • vs i
  by_cases h : (s ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum f h]
    apply Submodule.sum_mem
    intro i hi
    have his : i ∈ s := (h.mem_toFinset.mp hi).1
    exact Submodule.smul_mem _ (cfs i)
      (Submodule.subset_span (Set.mem_image_of_mem vs his))
  · rw [finsum_mem_eq_zero_of_infinite h]
    exact Submodule.zero_mem _


--#min_imports
