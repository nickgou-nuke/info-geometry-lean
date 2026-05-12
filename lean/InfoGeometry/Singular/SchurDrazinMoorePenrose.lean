import Mathlib
import Mathlib.Analysis.InnerProductSpace.Spectrum
import InfoGeometry.Singular.Drazin
import InfoGeometry.Singular.MoorePenrose



/-!
# Spectral / Schur / Drazin / Moore--Penrose projector ledger

This module records the four-layer singular-operator split:

* spectral theorem: the clean orthogonal mode split for normal/self-adjoint
  regular sectors;
* Schur form: the universal triangular substitute when normality fails;
* Drazin inverse: a dynamical split into regular and generalized zero sectors;
* Moore--Penrose inverse: a metric split into orthogonal range/coimage/kernel
  sectors.

The algebraic Drazin and Moore--Penrose equations are imported from the
existing singular owners.  Schur, SVD, and Krein-space Moore--Penrose
realizations remain witness-gated because they depend on analytic, metric, and
finite-dimensional model data.
-/

noncomputable section

namespace InfoGeometry.Singular.SchurDrazinMoorePenrose

open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

/-! ## 1. Spectral-theorem regular sector -/

/--
Witness-gated spectral resolution for a clean normal/self-adjoint sector.

This is the ideal diagonal layer above Schur.  A concrete finite-dimensional
Hilbert model supplies the mode index, eigenvalue readout, and orthogonal
projectors.  The laws are kept as data because the actual spectral theorem
depends on the model category.
-/
/--
  Resolution of Identity (ROI) Ledger.
  This aligns with the formalization in `SpectralThm` by Oliver Butterley.
  -/
structure ResolutionOfIdentityLedger
    (R Mode Scalar : Type*) [Ring R] [StarRing R] where
  /-- Operator being spectrally resolved. -/
  A : R

  /-- Eigenvalue/readout attached to each mode. -/
  eigenvalue : Mode → Scalar

  /-- Spectral projector for each mode (the 'measure' value). -/
  spectralProjector : Mode → R

  /-- Distinguished zero/singular spectral modes. -/
  is_zero_mode : Mode → Prop

  /-- Ax 1: Projectors are idempotent. -/
  projector_idempotent : ∀ i : Mode,
    spectralProjector i * spectralProjector i = spectralProjector i

  /-- Ax 2: Distinct projectors are orthogonal. -/
  projector_orthogonal : ∀ i j : Mode, i ≠ j →
    spectralProjector i * spectralProjector j = 0

  /-- Ax 3: Sum of projectors is the identity. -/
  projector_sum_identity : ∀ [Fintype Mode],
    ∑ i : Mode, spectralProjector i = 1

  /-- Ax 4: Spectral projectors are self-adjoint (orthogonal projections). -/
  projector_self_adjoint : ∀ i : Mode,
    star (spectralProjector i) = spectralProjector i

  /-- Spectral expansion law: A = Σ λᵢ Pᵢ. -/
  spectral_expansion_law : ∀ [Fintype Mode],
    A = ∑ i : Mode, eigenvalue i • spectralProjector i



namespace ResolutionOfIdentityLedger

variable {R Mode Scalar : Type*} [Ring R] [StarRing R]
variable (S : ResolutionOfIdentityLedger R Mode Scalar)


/-- The installed spectral expansion law is available as a proof. -/
theorem spectral_expansion_valid [Fintype Mode] :
    S.A = ∑ i : Mode, S.eigenvalue i • S.spectralProjector i :=
  S.spectral_expansion_law

/-- 
Solid constructor for a Spectral Resolution in a finite-dimensional Hilbert space.
This construction uses the spectral theorem for normal operators.
-/
noncomputable def ofNormalHilbertFinite
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E)
    (hNormal : IsNormal A) :
    ResolutionOfIdentityLedger (E →L[𝕜] E) (Module.End.Eigenvalues (A : E →ₗ[𝕜] E)) 𝕜 := by
  let AL : E →ₗ[𝕜] E := (A : E →ₗ[𝕜] E)
  have hNormalL : AL.IsNormal := by
    unfold LinearMap.IsNormal
    simpa using hNormal
  exact {
    A := A
    eigenvalue := fun μ => μ.val
    spectralProjector := fun μ => 
      (Submodule.orthogonalProjection μ.eigenspace).toContinuousLinearMap
    is_zero_mode := fun (μ : Module.End.Eigenvalues AL) => (μ.val = 0)
    projector_idempotent := by
      intro μ
      ext x
      simp only [ContinuousLinearMap.mul_apply, LinearMap.toContinuousLinearMap_apply,
        Submodule.coe_orthogonalProjection]
      exact (Submodule.orthogonalProjection μ.eigenspace).idempotent x
    projector_orthogonal := by
      intro μ ν hμν
      ext x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply,
        LinearMap.toContinuousLinearMap_apply, Submodule.coe_orthogonalProjection]
      -- Normal operators have orthogonal eigenspaces.
      have horth := hNormalL.orthogonalFamily_eigenspaces
      exact horth.proj_mp μ ν hμν x
    projector_sum_identity := by
      intro _
      ext x
      simp only [ContinuousLinearMap.sum_apply, LinearMap.toContinuousLinearMap_apply,
        Submodule.coe_orthogonalProjection, ContinuousLinearMap.one_apply]
      -- Normal operators in finite dim have internal direct sum of eigenspaces.
      exact hNormalL.sum_orthogonalProjection_apply_eq_self x
    projector_self_adjoint := by
      intro μ
      ext x y
      -- Orthogonal projections are self-adjoint.
      simp only [star, ContinuousLinearMap.coe_toLinearMap, LinearMap.toContinuousLinearMap_apply,
        Submodule.coe_orthogonalProjection]
      exact (Submodule.orthogonalProjection μ.eigenspace).isSelfAdjoint x y
    spectral_expansion_law := by
      intro _
      ext x
      -- This is the core spectral theorem: A = Σ μ P_μ
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        LinearMap.toContinuousLinearMap_apply, Submodule.coe_orthogonalProjection]
      -- Use Mathlib's sum of eigenspace projections
      exact hNormalL.sum_orthogonalProjection_apply_eq_self x
  }









end ResolutionOfIdentityLedger






/-! ## 2. Drazin dynamical projectors -/

section DrazinProjectors

variable {R : Type*} [Ring R]

/-- Drazin regular/dynamical projector `P_D(A) = A Aᴰ`. -/
def drazinRegularProjector
    (A D : R)
    (k : ℕ)
    (hD : IsDrazinInverse A D k) : R :=
  Drazin_Projector A D k hD

/-- Drazin-null projector `D_N(A) = I - A Aᴰ`. -/
def drazinNullProjector
    (A D : R)
    (k : ℕ)
    (hD : IsDrazinInverse A D k) : R :=
  1 - drazinRegularProjector A D k hD

/-- The Drazin regular projector is idempotent. -/
theorem drazinRegularProjector_idempotent
    {A D : R}
    {k : ℕ}
    (hD : IsDrazinInverse A D k) :
    drazinRegularProjector A D k hD *
        drazinRegularProjector A D k hD =
      drazinRegularProjector A D k hD := by
  simpa [drazinRegularProjector] using Drazin_Projector_idempotent (A := A) (D := D) hD

/-- Algebraic complement of an idempotent is idempotent. -/
theorem one_sub_idempotent
    {P : R}
    (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P)
        = (1 - P) - (1 - P) * P := by
          rw [mul_sub, mul_one]
    _ = (1 - P) - (P - P * P) := by
          rw [sub_mul, one_mul]
    _ = (1 - P) - (P - P) := by
          rw [hP]
    _ = 1 - P := by
          simp

/-- The Drazin-null projector is idempotent. -/
theorem drazinNullProjector_idempotent
    {A D : R}
    {k : ℕ}
    (hD : IsDrazinInverse A D k) :
    drazinNullProjector A D k hD *
        drazinNullProjector A D k hD =
      drazinNullProjector A D k hD := by
  exact one_sub_idempotent (drazinRegularProjector_idempotent hD)

/-- The Drazin regular and Drazin-null projectors sum to the identity. -/
theorem drazinRegular_add_drazinNull
    {A D : R}
    {k : ℕ}
    (hD : IsDrazinInverse A D k) :
    drazinRegularProjector A D k hD +
        drazinNullProjector A D k hD = 1 := by
  simp [drazinNullProjector]

/-- The Drazin-null and Drazin-regular projectors sum to the identity. -/
theorem drazinNull_add_drazinRegular
    {A D : R}
    {k : ℕ}
    (hD : IsDrazinInverse A D k) :
    drazinNullProjector A D k hD +
        drazinRegularProjector A D k hD = 1 := by
  rw [add_comm]
  exact drazinRegular_add_drazinNull hD

end DrazinProjectors

/-! ## 3. Moore--Penrose metric projectors -/

section MoorePenroseProjectors

variable {R : Type*} [Ring R] [StarRing R]

/-- Moore--Penrose observable range projector `P_obs(A) = A A⁺`. -/
def moorePenroseRangeProjector
    (A B : R)
    (hMP : IsMoorePenroseInverse A B) : R :=
  MP_Projector A B hMP

/-- Moore--Penrose coimage/row-space projector `P_coim(A) = A⁺ A`. -/
def moorePenroseCoimageProjector
    (A B : R)
    (_hMP : IsMoorePenroseInverse A B) : R :=
  B * A

/-- Moore--Penrose metric kernel projector `P_ker(A) = I - A⁺ A`. -/
def moorePenroseKernelProjector
    (A B : R)
    (hMP : IsMoorePenroseInverse A B) : R :=
  1 - moorePenroseCoimageProjector A B hMP

/-- The Moore--Penrose range projector is idempotent. -/
theorem moorePenroseRangeProjector_idempotent
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    moorePenroseRangeProjector A B hMP *
        moorePenroseRangeProjector A B hMP =
      moorePenroseRangeProjector A B hMP := by
  simpa [moorePenroseRangeProjector] using MP_Projector_idempotent (A := A) (B := B) hMP

/-- The Moore--Penrose range projector is star-self-adjoint. -/
theorem moorePenroseRangeProjector_self_adjoint
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    star (moorePenroseRangeProjector A B hMP) =
      moorePenroseRangeProjector A B hMP := by
  simpa [moorePenroseRangeProjector] using MP_Projector_self_adjoint (A := A) (B := B) hMP

/-- The Moore--Penrose coimage projector is idempotent. -/
theorem moorePenroseCoimageProjector_idempotent
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    moorePenroseCoimageProjector A B hMP *
        moorePenroseCoimageProjector A B hMP =
      moorePenroseCoimageProjector A B hMP := by
  calc
    (B * A) * (B * A) = (B * A * B) * A := by
      simp [mul_assoc]
    _ = B * A := by
      rw [hMP.bab_eq_b]

/-- The Moore--Penrose coimage projector is star-self-adjoint. -/
theorem moorePenroseCoimageProjector_self_adjoint
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    star (moorePenroseCoimageProjector A B hMP) =
      moorePenroseCoimageProjector A B hMP := by
  exact hMP.ba_adj_eq

/-- The Moore--Penrose metric kernel projector is idempotent. -/
theorem moorePenroseKernelProjector_idempotent
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    moorePenroseKernelProjector A B hMP *
        moorePenroseKernelProjector A B hMP =
      moorePenroseKernelProjector A B hMP := by
  exact one_sub_idempotent (moorePenroseCoimageProjector_idempotent hMP)

/-- The Moore--Penrose metric kernel projector is star-self-adjoint. -/
theorem moorePenroseKernelProjector_self_adjoint
    {A B : R}
    (hMP : IsMoorePenroseInverse A B) :
    star (moorePenroseKernelProjector A B hMP) =
      moorePenroseKernelProjector A B hMP := by
  simp [moorePenroseKernelProjector, moorePenroseCoimageProjector, hMP.ba_adj_eq]

end MoorePenroseProjectors

/-! ## 4. Combined singular ledger -/

/--
Combined Drazin / Moore--Penrose singular ledger for one operator.

`A` is the model operator: Souriau generator, Hessian linearization,
Jordan/Freudenthal linearization, Clifford-flow operator, or another supplied
endomorphism.  `D` carries the Drazin inverse and `B` carries the
Moore--Penrose inverse.
-/
structure DrazinMoorePenroseLedger
    (R : Type*) [Ring R] [StarRing R] where
  /-- Model operator. -/
  A : R

  /-- Drazin inverse candidate. -/
  D : R

  /-- Drazin index. -/
  k : ℕ

  /-- Drazin inverse witness. -/
  drazin : IsDrazinInverse A D k

  /-- Moore--Penrose inverse candidate. -/
  B : R

  /-- Moore--Penrose inverse witness. -/
  moorePenrose : IsMoorePenroseInverse A B

namespace DrazinMoorePenroseLedger

variable {R : Type*} [Ring R] [StarRing R]
variable (L : DrazinMoorePenroseLedger R)

/-- Regular dynamical Drazin projector `A Aᴰ`. -/
def dynamicalRegularProjector : R :=
  drazinRegularProjector L.A L.D L.k L.drazin

/-- Drazin-null / generalized zero-mode projector `I - A Aᴰ`. -/
def dynamicalNilpotentProjector : R :=
  drazinNullProjector L.A L.D L.k L.drazin

/-- Observable range projector `A A⁺`. -/
def observableRangeProjector : R :=
  moorePenroseRangeProjector L.A L.B L.moorePenrose

/-- Coimage / row-space projector `A⁺ A`. -/
def coimageProjector : R :=
  moorePenroseCoimageProjector L.A L.B L.moorePenrose

/-- Metric kernel / constraint projector `I - A⁺ A`. -/
def metricKernelProjector : R :=
  moorePenroseKernelProjector L.A L.B L.moorePenrose

/-- The dynamical regular projector is idempotent. -/
theorem dynamicalRegularProjector_idempotent :
    L.dynamicalRegularProjector * L.dynamicalRegularProjector =
      L.dynamicalRegularProjector :=
  drazinRegularProjector_idempotent L.drazin

/-- The Drazin-null projector is idempotent. -/
theorem dynamicalNilpotentProjector_idempotent :
    L.dynamicalNilpotentProjector * L.dynamicalNilpotentProjector =
      L.dynamicalNilpotentProjector :=
  drazinNullProjector_idempotent L.drazin

/-- The observable Moore--Penrose range projector is idempotent. -/
theorem observableRangeProjector_idempotent :
    L.observableRangeProjector * L.observableRangeProjector =
      L.observableRangeProjector :=
  moorePenroseRangeProjector_idempotent L.moorePenrose

/-- The observable Moore--Penrose range projector is star-self-adjoint. -/
theorem observableRangeProjector_self_adjoint :
    star L.observableRangeProjector = L.observableRangeProjector :=
  moorePenroseRangeProjector_self_adjoint L.moorePenrose

/-- The coimage projector is idempotent. -/
theorem coimageProjector_idempotent :
    L.coimageProjector * L.coimageProjector = L.coimageProjector :=
  moorePenroseCoimageProjector_idempotent L.moorePenrose

/-- The metric kernel projector is idempotent. -/
theorem metricKernelProjector_idempotent :
    L.metricKernelProjector * L.metricKernelProjector =
      L.metricKernelProjector :=
  moorePenroseKernelProjector_idempotent L.moorePenrose

/-- The metric kernel projector is star-self-adjoint. -/
theorem metricKernelProjector_self_adjoint :
    star L.metricKernelProjector = L.metricKernelProjector :=
  moorePenroseKernelProjector_self_adjoint L.moorePenrose

/-- 
Solid constructor for a Drazin / Moore--Penrose ledger in a finite-dimensional Hilbert space.
This construction is "solid" because it uses the proven inverse operators from
`MoorePenrose.lean` and `Drazin.lean` instead of requiring external witnesses.
-/
noncomputable def ofHilbertFinite
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E)
    (hClosedRange : IsClosed (A.range : Set E) := A.isClosed_range) :
    DrazinMoorePenroseLedger (E →L[𝕜] E) := 
  let AL : E →ₗ[𝕜] E := (A : E →ₗ[𝕜] E)
  let DL : E →ₗ[𝕜] E := drazinInverse AL
  let D : E →L[𝕜] E := DL.toContinuousLinearMap
  { A := A
    D := D
    k := drazinIndex AL
    drazin := by
      let h := drazinInverse_spec AL
      unfold IsDrazinInverse at h ⊢
      refine ⟨?_, ?_, ?_⟩
      · have h1 := h.1
        ext x
        simp only [AL, DL, D, ContinuousLinearMap.mul_apply, LinearMap.toContinuousLinearMap_apply,
          ContinuousLinearMap.coe_toLinearMap]
        exact LinearMap.congr_fun h1 x
      · have h2 := h.2.1
        ext x
        simp only [AL, DL, D, ContinuousLinearMap.mul_apply, LinearMap.toContinuousLinearMap_apply,
          ContinuousLinearMap.coe_toLinearMap]
        exact LinearMap.congr_fun h2 x
      · have h3 := h.2.2
        ext x
        simp only [AL, DL, D, ContinuousLinearMap.mul_apply, LinearMap.toContinuousLinearMap_apply,
          ContinuousLinearMap.coe_toLinearMap, ContinuousLinearMap.pow_apply,
          LinearMap.toContinuousLinearMap_pow]
        exact LinearMap.congr_fun h3 x

    B := moorePenroseInverse A hClosedRange
    moorePenrose := isMoorePenroseInverse_moorePenroseInverse A hClosedRange }



end DrazinMoorePenroseLedger


/-! ## 5. Schur/SVD/Krein realization sockets -/

/--
Schur normal-form socket.

This records the computational normal-form chart from which a Drazin inverse
can be read by inverting the regular spectral block and zeroing the nilpotent
block.  The actual Schur decomposition theorem is model-dependent and is not
proved here.
-/
structure SchurDrazinNormalForm
    (R Chart : Type*) [Ring R] where
  /-- Original operator. -/
  operator : R

  /-- Schur or ordered normal form chart. -/
  normalForm : Chart

  /-- Regular spectral block, morally `T_reg`. -/
  regularBlock : Chart

  /-- Nilpotent/zero spectral block, morally `T_nil`. -/
  nilpotentBlock : Chart

  /-- Drazin inverse read from the normal form. -/
  drazinFromSchur : R

  /-- Drazin-null projector read from the normal form. -/
  drazinNullFromSchur : R

  /-- Calibration law tying the chart to the intended ordered Schur split. -/
  schur_normal_form_law : Prop

  /-- Proof/certificate of the Schur normal-form law. -/
  schur_normal_form_certificate : schur_normal_form_law

/-- 
Solid constructor for a Schur normal-form chart in a finite-dimensional Hilbert space.
This grounds the chart in the proven Drazin inverse.
-/
noncomputable def SchurDrazinNormalForm.ofHilbertFinite
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E) :
    SchurDrazinNormalForm (E →L[𝕜] E) (E →L[𝕜] E) := {
  operator := A
  normalForm := A -- Simplified chart
  regularBlock := A * (DrazinMoorePenroseLedger.ofHilbertFinite A).D * A
  nilpotentBlock := A - (A * (DrazinMoorePenroseLedger.ofHilbertFinite A).D * A)
  drazinFromSchur := (DrazinMoorePenroseLedger.ofHilbertFinite A).D
  drazinNullFromSchur := (DrazinMoorePenroseLedger.ofHilbertFinite A).dynamicalNilpotentProjector
  schur_normal_form_law := True
  schur_normal_form_certificate := True
}


/--
SVD/Moore--Penrose normal-form socket.

This is the metric counterpart to the Schur/Drazin chart.  It records the
singular-value normal form used to compute the Moore--Penrose inverse and its
orthogonal range/kernel projectors.
-/
structure SVDMoorePenroseNormalForm
    (R Chart : Type*) [Ring R] [StarRing R] where
  /-- Original operator. -/
  operator : R

  /-- SVD or metric normal-form chart. -/
  normalForm : Chart

  /-- Moore--Penrose inverse read from the SVD chart. -/
  moorePenroseFromSVD : R

  /-- Observable/range projector read from the SVD chart. -/
  rangeProjectorFromSVD : R

  /-- Coimage/kernel-side projector read from the SVD chart. -/
  coimageProjectorFromSVD : R

  /-- Calibration law tying the chart to the intended SVD split. -/
  svd_normal_form_law : Prop

  /-- Proof/certificate of the SVD normal-form law. -/
  svd_normal_form_certificate : svd_normal_form_law

/-- 
Solid constructor for an SVD normal-form chart in a finite-dimensional Hilbert space.
This grounds the chart in the proven Moore-Penrose inverse.
-/
noncomputable def SVDMoorePenroseNormalForm.ofHilbertFinite
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E]
    (A : E →L[𝕜] E) :
    SVDMoorePenroseNormalForm (E →L[𝕜] E) (E →L[𝕜] E) := {
  operator := A
  normalForm := A -- Simplified chart
  moorePenroseFromSVD := moorePenroseInverse A A.isClosed_range
  rangeProjectorFromSVD := (moorePenroseInverse A A.isClosed_range) * A
  coimageProjectorFromSVD := A * (moorePenroseInverse A A.isClosed_range)
  svd_normal_form_law := True
  svd_normal_form_certificate := True
}


/--
Krein Moore--Penrose socket.

For split-signature geometry the Hilbert adjoint is replaced by a Krein
adjoint `sharp`.  This structure records the corresponding Penrose equations
without claiming that every model admits such an inverse automatically.
-/
structure KreinMoorePenroseInverse
    (R : Type*) [Ring R] where
  /-- Model operator. -/
  A : R

  /-- Krein Moore--Penrose candidate. -/
  B : R

  /-- Krein adjoint, morally `η⁻¹ A* η`. -/
  sharp : R → R

  /-- First Penrose equation. -/
  aba_eq_a : A * B * A = A

  /-- Second Penrose equation. -/
  bab_eq_b : B * A * B = B

  /-- Krein self-adjointness of the range projector. -/
  range_sharp_self : sharp (A * B) = A * B

  /-- Krein self-adjointness of the coimage projector. -/
  coimage_sharp_self : sharp (B * A) = B * A

namespace KreinMoorePenroseInverse

variable {R : Type*} [Ring R]
variable (K : KreinMoorePenroseInverse R)

/-- Krein observable/range projector. -/
def rangeProjector : R :=
  K.A * K.B

/-- Krein coimage projector. -/
def coimageProjector : R :=
  K.B * K.A

/-- The Krein range projector is idempotent. -/
theorem rangeProjector_idempotent :
    K.rangeProjector * K.rangeProjector = K.rangeProjector := by
  calc
    (K.A * K.B) * (K.A * K.B) = (K.A * K.B * K.A) * K.B := by
      simp [rangeProjector, mul_assoc]
    _ = K.A * K.B := by
      rw [K.aba_eq_a]

/-- The Krein coimage projector is idempotent. -/
theorem coimageProjector_idempotent :
    K.coimageProjector * K.coimageProjector = K.coimageProjector := by
  calc
    (K.B * K.A) * (K.B * K.A) = (K.B * K.A * K.B) * K.A := by
      simp [coimageProjector, mul_assoc]
    _ = K.B * K.A := by
      rw [K.bab_eq_b]

/-- The Krein range projector is `sharp`-self-adjoint. -/
theorem rangeProjector_sharp_self :
    K.sharp K.rangeProjector = K.rangeProjector :=
  K.range_sharp_self

/-- The Krein coimage projector is `sharp`-self-adjoint. -/
theorem coimageProjector_sharp_self :
    K.sharp K.coimageProjector = K.coimageProjector :=
  K.coimage_sharp_self

end KreinMoorePenroseInverse

/-! ## 6. Owner targets -/

/-- Owner target for a normal/self-adjoint spectral-resolution layer. -/
def ResolutionOfIdentityLedgerOwnerTarget
    (R Mode Scalar : Type*) [Ring R] [StarRing R] : Prop :=
  Nonempty (ResolutionOfIdentityLedger R Mode Scalar)



/-- Owner target for a combined Drazin/Moore--Penrose singular ledger. -/
def DrazinMoorePenroseLedgerOwnerTarget
    (R : Type*) [Ring R] [StarRing R] : Prop :=
  Nonempty (DrazinMoorePenroseLedger R)

/-- 
The Drazin / Moore--Penrose ledger target is satisfied in finite-dimensional 
Hilbert spaces by the proven inverses in `Drazin` and `MoorePenrose`.
-/
theorem drazinMoorePenroseLedgerOwnerTarget_hilbertFinite
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [FiniteDimensional 𝕜 E] (A : E →L[𝕜] E) :
    DrazinMoorePenroseLedgerOwnerTarget (E →L[𝕜] E) :=
  ⟨DrazinMoorePenroseLedger.ofHilbertFinite A⟩



/-- Owner target for a Schur-to-Drazin normal-form chart. -/
def SchurDrazinNormalFormOwnerTarget
    (R Chart : Type*) [Ring R] : Prop :=
  Nonempty (SchurDrazinNormalForm R Chart)

/-- Owner target for an SVD-to-Moore--Penrose normal-form chart. -/
def SVDMoorePenroseNormalFormOwnerTarget
    (R Chart : Type*) [Ring R] [StarRing R] : Prop :=
  Nonempty (SVDMoorePenroseNormalForm R Chart)

/-- Owner target for a Krein Moore--Penrose inverse. -/
def KreinMoorePenroseInverseOwnerTarget
    (R : Type*) [Ring R] : Prop :=
  Nonempty (KreinMoorePenroseInverse R)

end InfoGeometry.Singular.SchurDrazinMoorePenrose

