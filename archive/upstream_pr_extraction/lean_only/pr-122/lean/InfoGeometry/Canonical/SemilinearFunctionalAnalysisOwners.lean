import Mathlib

/-!
# Kernel-checked semilinear functional-analysis owners

This file promotes the three reusable statements from the semilinear API
smoke-test into named theorem owners.  The isocrystal result is deliberately
the one-dimensional classification theorem supplied by Mathlib, not a claim
of arbitrary-dimensional Dieudonne--Manin classification.
-/

namespace InfoGeometry.Canonical.SemilinearFunctionalAnalysisOwners

noncomputable section

theorem frechetRiesz_evaluation
    {𝕜 E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (x y : E) :
    ((InnerProductSpace.toDual 𝕜 E) x) y = inner 𝕜 x y :=
  InnerProductSpace.toDual_apply_apply

theorem adjoint_pairing
    {𝕜 E F : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (A : E →L[𝕜] F) (x : E) (y : F) :
    inner 𝕜 ((ContinuousLinearMap.adjoint A) y) x = inner 𝕜 y (A x) :=
  ContinuousLinearMap.adjoint_inner_left A x y

theorem adjoint_involutive
    {𝕜 E F : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint A) = A :=
  ContinuousLinearMap.adjoint_adjoint A

theorem adjoint_comp_reverse
    {𝕜 E F G : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G]
    [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (A.comp B) =
      (ContinuousLinearMap.adjoint B).comp
        (ContinuousLinearMap.adjoint A) :=
  ContinuousLinearMap.adjoint_comp A B

theorem one_dimensional_isocrystal_classification
    (p : ℕ) [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [IsAlgClosed k] [CharP k p]
    (V : Type*) [AddCommGroup V]
    [WittVector.Isocrystal p k V]
    (h_dim :
      Module.finrank (FractionRing (WittVector p k)) V = 1) :
    ∃ m, Nonempty
      (WittVector.IsocrystalEquiv p k
        (WittVector.StandardOneDimIsocrystal p k m) V) :=
  WittVector.isocrystal_classification p k V h_dim

end
end InfoGeometry.Canonical.SemilinearFunctionalAnalysisOwners
