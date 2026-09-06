import InfoGeometry.JordanDecomposition
noncomputable section
open FiniteDimensional Submodule
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

lemma linearIndependent_cyclic [FiniteDimensional K V] (N : Module.End K V) (k : ℕ)
    (hN : NilpotentIndex N k) (x : V) (hx : (N ^ (k - 1)) x ≠ 0) :
    LinearIndependent K (fun (i : Fin k) => (N ^ (i : ℕ)) x) := by
  have hzero : (N ^ k) x = 0 := by
    simpa using congrArg (fun f : Module.End K V => f x) hN.1
  exact JordanDecomposition.chain_linear_independent (N := N) (x := x) (j := k) hx hzero
