import InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge

/-!
# Topology of finite projective count readouts

The localization packet contains discrete finite-support data.  For topology,
the support is fixed explicitly and the count profile is the varying
coordinate.  The normalized ray is continuous only on the nonzero-partition
locus, where its denominator is nonzero.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays

instance gwProjectiveCountStateTopologicalSpace
    {G T Target Coeff : Type*} :
    TopologicalSpace (GWProjectiveCountState G T Target Coeff) :=
  TopologicalSpace.induced
    (fun C : GWProjectiveCountState G T Target Coeff => C.counts) inferInstance

def finitePartitionReadout
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ)
    (C : GWProjectiveCountState G T Target Coeff) : ℝ :=
  finiteArithmeticPartition C.counts support β

theorem continuous_finitePartitionReadout
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    Continuous (finitePartitionReadout support β :
      GWProjectiveCountState G T Target Coeff → ℝ) := by
  unfold finitePartitionReadout finiteArithmeticPartition
    finiteArithmeticWeight
  have hcounts : Continuous
      (fun C : GWProjectiveCountState G T Target Coeff => C.counts) :=
    continuous_induced_dom
  apply continuous_finset_sum
  intro n hn
  exact ((continuous_apply n).comp hcounts).mul continuous_const

def finitePartitionZeroLocus
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    Set (GWProjectiveCountState G T Target Coeff) :=
  {C | finitePartitionReadout support β C = 0}

theorem finitePartitionZeroLocus_isClosed
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    IsClosed (finitePartitionZeroLocus (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β) := by
  simpa only [finitePartitionZeroLocus, Set.preimage, Set.mem_setOf_eq] using
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).preimage
      (continuous_finitePartitionReadout (G := G) (T := T) (Target := Target)
        (Coeff := Coeff) support β)

def finitePartitionNonzeroLocus
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    Set (GWProjectiveCountState G T Target Coeff) :=
  {C | finitePartitionReadout support β C ≠ 0}

theorem finitePartitionNonzeroLocus_isOpen
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    IsOpen (finitePartitionNonzeroLocus (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β) := by
  have hclosed :=
    finitePartitionZeroLocus_isClosed (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β
  change IsOpen (finitePartitionZeroLocus (G := G) (T := T) (Target := Target)
    (Coeff := Coeff) support β)ᶜ
  exact hclosed.isOpen_compl

theorem continuousOn_finiteNormalizedRayReadout
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) (n : ℕ) :
    ContinuousOn
      (fun C : GWProjectiveCountState G T Target Coeff =>
        finiteArithmeticNormalizedRay C.counts support β n)
      (finitePartitionNonzeroLocus (G := G) (T := T) (Target := Target)
        (Coeff := Coeff) support β) := by
  unfold finiteArithmeticNormalizedRay finiteArithmeticWeight
  have hcounts : Continuous
      (fun C : GWProjectiveCountState G T Target Coeff => C.counts) :=
    continuous_induced_dom
  have hweight : Continuous
      (fun C : GWProjectiveCountState G T Target Coeff =>
        C.counts n * InfoGeometry.Arithmetic.primitiveMellinKernel n β) :=
    ((continuous_apply n).comp hcounts).mul continuous_const
  apply hweight.continuousOn.div
    (continuous_finitePartitionReadout (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β).continuousOn
  intro C hC
  exact hC

theorem continuous_finiteNormalizedRayReadout_on_subtype
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) (n : ℕ) :
    Continuous
      (fun C : finitePartitionNonzeroLocus (G := G) (T := T) (Target := Target)
        (Coeff := Coeff) support β =>
        finiteArithmeticNormalizedRay C.1.counts support β n) :=
  (continuousOn_finiteNormalizedRayReadout (G := G) (T := T) (Target := Target)
    (Coeff := Coeff) support β n).restrict

def finiteNormalizedShapeVectorOnNonzero
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    finitePartitionNonzeroLocus (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β → support → ℝ :=
  fun C n => finiteArithmeticNormalizedRay C.1.counts support β n.1

theorem continuous_finiteNormalizedShapeVectorOnNonzero
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ) :
    Continuous (finiteNormalizedShapeVectorOnNonzero
      (G := G) (T := T) (Target := Target) (Coeff := Coeff) support β) := by
  apply continuous_pi
  intro n
  simpa [finiteNormalizedShapeVectorOnNonzero] using
    (continuousOn_finiteNormalizedRayReadout (G := G) (T := T)
      (Target := Target) (Coeff := Coeff) support β n.1).restrict

theorem finiteNormalizedShapeVectorOnNonzero_sum_eq_one
    {G T Target Coeff : Type*}
    (support : Finset ℕ) (β : ℝ)
    (C : finitePartitionNonzeroLocus (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β)
    (hZ : finitePartitionReadout (G := G) (T := T) (Target := Target)
      (Coeff := Coeff) support β C.1 ≠ 0) :
    (∑ n ∈ support.attach, finiteNormalizedShapeVectorOnNonzero (G := G) (T := T)
        (Target := Target) (Coeff := Coeff) support β C n) = 1 := by
  calc
    (∑ n ∈ support.attach, finiteNormalizedShapeVectorOnNonzero (G := G) (T := T)
        (Target := Target) (Coeff := Coeff) support β C n) =
        (∑ n ∈ support.attach, finiteArithmeticNormalizedRay C.1.counts support β n.1) := by
      rfl
    _ = ∑ n ∈ support, finiteArithmeticNormalizedRay C.1.counts support β n := by
      simpa using
        (Finset.sum_attach support
          (fun n => finiteArithmeticNormalizedRay C.1.counts support β n))
    _ = 1 := finiteArithmeticNormalizedRay_sum_eq_one C.1.counts support β hZ

end InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge
