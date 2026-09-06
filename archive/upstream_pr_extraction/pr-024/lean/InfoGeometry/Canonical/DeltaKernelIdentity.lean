import Mathlib

/-!
# InfoGeometry.Canonical.DeltaKernelIdentity

Finite kernel formalization of the identity operator.

This is the finite-index analogue of
`K_I(x,y) = δ(x-y)` and
`(If)(x) = ∫ δ(x-y) f(y) dy = f(x)`.
-/

namespace InfoGeometry.Canonical.DeltaKernelIdentity

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [Semiring 𝕜]

/-- Kronecker-delta kernel on a finite index type. -/
def deltaKernel (i j : ι) : 𝕜 :=
  if i = j then 1 else 0

/-- Kernel action on a function (`f` as a finite column). -/
def applyKernel (K : ι → ι → 𝕜) (f : ι → 𝕜) (i : ι) : 𝕜 :=
  ∑ j, K i j * f j

/-- Composition of two finite kernels. -/
def composeKernel (K L : ι → ι → 𝕜) : ι → ι → 𝕜 :=
  fun i k => ∑ j, K i j * L j k

/-- The delta kernel acts as identity. -/
theorem deltaKernel_apply (f : ι → 𝕜) (i : ι) :
    applyKernel deltaKernel f i = f i := by
  unfold applyKernel deltaKernel
  classical
  calc
    (∑ j, (if i = j then 1 else 0) * f j)
      = ∑ j, if i = j then f j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          split_ifs with h
          · simp [h]
          · simp [h]
    _ = f i := by
          simpa [Finset.sum_ite_eq', Finset.mem_univ]

/-- Matrix entry form: delta kernel equals identity matrix entries. -/
theorem deltaKernel_eq_identity_entry (i j : ι) :
    deltaKernel (𝕜 := 𝕜) i j = (1 : Matrix ι ι 𝕜) i j := by
  classical
  by_cases h : i = j
  · simp [deltaKernel, Matrix.one_apply, h]
  · simp [deltaKernel, Matrix.one_apply, h]

/-- Left identity: `δ ∘ K = K`. -/
theorem compose_delta_left (K : ι → ι → 𝕜) :
    composeKernel deltaKernel K = K := by
  funext i
  funext k
  unfold composeKernel deltaKernel
  classical
  calc
    (∑ j, (if i = j then 1 else 0) * K j k)
      = ∑ j, if i = j then K j k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          split_ifs with h
          · simp [h]
          · simp [h]
    _ = K i k := by
          simpa [Finset.sum_ite_eq', Finset.mem_univ]

/-- Right identity: `K ∘ δ = K`. -/
theorem compose_delta_right (K : ι → ι → 𝕜) :
    composeKernel K deltaKernel = K := by
  funext i
  funext k
  unfold composeKernel deltaKernel
  classical
  calc
    (∑ j, K i j * (if j = k then 1 else 0))
      = ∑ j, if j = k then K i j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          split_ifs with h
          · simp [h]
          · simp [h]
    _ = K i k := by
          simpa [Finset.sum_ite_eq', Finset.mem_univ]

/-- Kernel action is compatible with kernel composition. -/
theorem apply_composeKernel (K L : ι → ι → 𝕜) (f : ι → 𝕜) (i : ι) :
    applyKernel (composeKernel K L) f i = applyKernel K (fun j => applyKernel L f j) i := by
  unfold applyKernel composeKernel
  classical
  calc
    (∑ k, (∑ j, K i j * L j k) * f k)
        = ∑ j, K i j * (∑ k, L j k * f k) := by
            simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
              (Finset.sum_comm (f := fun k j => (K i j * L j k) * f k))
    _ = ∑ j, K i j * applyKernel L f j := by
          rfl
    _ = applyKernel K (fun j => applyKernel L f j) i := by
          rfl

/-- Composition of finite kernels is associative. -/
theorem composeKernel_assoc
    (K L M : ι → ι → 𝕜) :
    composeKernel (composeKernel K L) M = composeKernel K (composeKernel L M) := by
  funext i
  funext k
  unfold composeKernel
  classical
  calc
    (∑ j, (∑ x, K i x * L x j) * M j k)
      = ∑ x, K i x * (∑ j, L x j * M j k) := by
          simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc] using
            (Finset.sum_comm (f := fun j x => (K i x * L x j) * M j k))
    _ = ∑ x, K i x * composeKernel L M x k := by
          rfl
    _ = composeKernel K (composeKernel L M) i k := by
          rfl

/-- Idempotence of the delta kernel under kernel composition. -/
theorem compose_delta_delta :
    composeKernel (ι := ι) (𝕜 := 𝕜) deltaKernel deltaKernel = deltaKernel := by
  calc
    composeKernel (ι := ι) (𝕜 := 𝕜) deltaKernel deltaKernel
      = deltaKernel := compose_delta_left (ι := ι) (𝕜 := 𝕜) deltaKernel

/-- Applying the identity-matrix kernel is the same as applying `deltaKernel`. -/
theorem applyKernel_matrixOne_eq_applyKernel_delta (f : ι → 𝕜) (i : ι) :
    applyKernel (fun a b => (1 : Matrix ι ι 𝕜) a b) f i
      = applyKernel (ι := ι) (𝕜 := 𝕜) deltaKernel f i := by
  unfold applyKernel
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa using congrArg (fun x => x * f j)
    (deltaKernel_eq_identity_entry (ι := ι) (𝕜 := 𝕜) i j).symm

/-- Additivity of kernel action in the state argument. -/
theorem applyKernel_add (K : ι → ι → 𝕜) (f g : ι → 𝕜) (i : ι) :
    applyKernel K (fun j => f j + g j) i
      = applyKernel K f i + applyKernel K g i := by
  unfold applyKernel
  simp [mul_add, Finset.sum_add_distrib]

/-- Left additivity of kernel composition. -/
theorem composeKernel_add_left (K₁ K₂ L : ι → ι → 𝕜) :
    composeKernel (fun i j => K₁ i j + K₂ i j) L
      = fun i k => composeKernel K₁ L i k + composeKernel K₂ L i k := by
  funext i
  funext k
  unfold composeKernel
  simp [add_mul, Finset.sum_add_distrib]

/-- Right additivity of kernel composition. -/
theorem composeKernel_add_right (K L₁ L₂ : ι → ι → 𝕜) :
    composeKernel K (fun i j => L₁ i j + L₂ i j)
      = fun i k => composeKernel K L₁ i k + composeKernel K L₂ i k := by
  funext i
  funext k
  unfold composeKernel
  simp [mul_add, Finset.sum_add_distrib]

/-- Scalar linearity of kernel action (left scaling of kernel entries). -/
theorem applyKernel_scale_left (a : 𝕜) (K : ι → ι → 𝕜) (f : ι → 𝕜) (i : ι) :
    applyKernel (fun x y => a * K x y) f i = a * applyKernel K f i := by
  unfold applyKernel
  calc
    (∑ j, (a * K i j) * f j)
      = ∑ j, a * (K i j * f j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [mul_assoc]
    _ = a * (∑ j, K i j * f j) := by
          simpa using (Finset.mul_sum Finset.univ (fun j => K i j * f j) a).symm
    _ = a * applyKernel K f i := by
          rfl

/-- Left scaling distributes over kernel composition. -/
theorem composeKernel_scale_left (a : 𝕜) (K L : ι → ι → 𝕜) :
    composeKernel (fun i j => a * K i j) L
      = fun i k => a * composeKernel K L i k := by
  funext i
  funext k
  unfold composeKernel
  calc
    (∑ j, (a * K i j) * L j k)
      = ∑ j, a * (K i j * L j k) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [mul_assoc]
    _ = a * (∑ j, K i j * L j k) := by
          simpa using (Finset.mul_sum Finset.univ (fun j => K i j * L j k) a).symm
    _ = a * composeKernel K L i k := by
          rfl

/-- Right-kernel scaling in composition (commutative coefficient semiring). -/
theorem composeKernel_scale_right
    {𝕜 : Type*} [CommSemiring 𝕜]
    (a : 𝕜) (K L : ι → ι → 𝕜) :
    composeKernel (ι := ι) (𝕜 := 𝕜) K (fun i j => a * L i j)
      = fun i k => a * composeKernel (ι := ι) (𝕜 := 𝕜) K L i k := by
  funext i
  funext k
  unfold composeKernel
  calc
    (∑ j, K i j * (a * L j k))
      = ∑ j, a * (K i j * L j k) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ = a * (∑ j, K i j * L j k) := by
          simpa using (Finset.mul_sum Finset.univ (fun j => K i j * L j k) a).symm
    _ = a * composeKernel K L i k := by
          rfl

/-- Right scaling of the state factors through kernel action. -/
theorem applyKernel_scale_state_right (a : 𝕜) (K : ι → ι → 𝕜) (f : ι → 𝕜) (i : ι) :
    applyKernel K (fun j => f j * a) i = applyKernel K f i * a := by
  unfold applyKernel
  calc
    (∑ j, K i j * (f j * a))
      = ∑ j, (K i j * f j) * a := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [mul_assoc]
    _ = (∑ j, K i j * f j) * a := by
          simpa using (Finset.sum_mul Finset.univ (fun j => K i j * f j) a).symm
    _ = applyKernel K f i * a := by
          rfl

/-- Owner-side bridge: kernel action is matrix `mulVec` entrywise. -/
theorem applyKernel_eq_mulVec
    (M : Matrix ι ι 𝕜) (f : ι → 𝕜) (i : ι) :
    applyKernel (fun a b => M a b) f i = (M.mulVec f) i := by
  unfold applyKernel Matrix.mulVec
  rfl

/-- Matrix-owner corollary: identity matrix acts trivially on vectors. -/
theorem one_mulVec (f : ι → 𝕜) :
    (1 : Matrix ι ι 𝕜).mulVec f = f := by
  funext i
  simpa using (applyKernel_eq_mulVec (ι := ι) (𝕜 := 𝕜) (M := (1 : Matrix ι ι 𝕜)) (f := f) i).trans
    (applyKernel_matrixOne_eq_applyKernel_delta (ι := ι) (𝕜 := 𝕜) f i).trans
    (deltaKernel_apply (ι := ι) (𝕜 := 𝕜) f i)

/-- Delta-kernel owner corollary in matrix form. -/
theorem deltaKernel_mulVec_eq (f : ι → 𝕜) :
    (fun i => applyKernel (ι := ι) (𝕜 := 𝕜) deltaKernel f i) = f := by
  funext i
  exact deltaKernel_apply (ι := ι) (𝕜 := 𝕜) f i

end InfoGeometry.Canonical.DeltaKernelIdentity
