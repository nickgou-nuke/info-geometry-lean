import Mathlib.LinearAlgebra.Finsupp.Supported

lemma finsum_mem_span {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) :
    ∑ᶠ i, cfs i • vs i ∈ Submodule.span R (Set.range vs) := by
  let f := fun i => cfs i • vs i
  by_cases h : (Function.support f).Finite
  · let s : Finset ι := h.toFinset
    rw [finsum_eq_finsetSum_of_support_subset (s := s) (f := f) (fun i hi => by simpa [s] using hi)]
    apply Submodule.sum_smul_mem
    exact fun i his => Submodule.mem_span_of_mem (Set.mem_range_self i)
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

lemma finsum_mem_mem_span {ι R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (vs : ι → V) (cfs : ι → R) (s : Set ι) :
    ∑ᶠ i ∈ s, cfs i • vs i ∈ Submodule.span R (vs '' s) := by
  let f := fun i => cfs i • vs i
  by_cases h : (s ∩ Function.support f).Finite
  · rw [← finsum_mem_inter_support]
    rw [finsum_mem_eq_finite_toFinset_sum f h]
    apply Submodule.sum_smul_mem
    intro i hi
    have his : i ∈ s := (h.mem_toFinset.mp hi).1
    exact Submodule.mem_span_of_mem (Set.mem_image_of_mem vs his)
  · rw [finsum_mem_eq_zero_of_infinite h]
    exact Submodule.zero_mem _
