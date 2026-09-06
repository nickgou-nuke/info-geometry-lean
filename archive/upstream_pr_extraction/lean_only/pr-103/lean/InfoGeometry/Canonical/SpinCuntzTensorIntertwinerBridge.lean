import Mathlib

/-!
# Tensor transport for a Spin--Cuntz intertwiner

This owner isolates the algebraic part of a possible Spin--Cuntz bridge.
It does **not** assert that the repository already contains a Spin--Cuntz
equivalence, nor does it construct a Yang--Baxter operator.  Given an actual
linear equivalence `J` between two carriers, it transports any checked local
operator on the tensor square and proves the resulting intertwining square.
The construction is therefore reusable once a concrete carrier equivalence is
available, without turning that missing equivalence into an axiom.
-/

noncomputable section

open scoped TensorProduct

namespace InfoGeometry.Canonical.SpinCuntzTensorIntertwinerBridge

open TensorProduct

variable {𝕜 Spin C : Type*}
  [CommRing 𝕜]
  [AddCommGroup Spin] [Module 𝕜 Spin]
  [AddCommGroup C] [Module 𝕜 C]

/-- Tensor-square transport induced by a carrier equivalence. -/
def tensorSquareEquiv (J : Spin ≃ₗ[𝕜] C) :
    (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (C ⊗[𝕜] C) :=
  TensorProduct.congr J J

/-- Conjugate a local tensor operator along the tensor-square equivalence. -/
def transportedCheckR
    (J : Spin ≃ₗ[𝕜] C)
    (R : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (Spin ⊗[𝕜] Spin)) :
    (C ⊗[𝕜] C) ≃ₗ[𝕜] (C ⊗[𝕜] C) :=
  (tensorSquareEquiv J).symm.trans (R.trans (tensorSquareEquiv J))

@[simp] theorem tensorSquareEquiv_pure
    (J : Spin ≃ₗ[𝕜] C) (x y : Spin) :
    tensorSquareEquiv J (x ⊗ₜ[𝕜] y) = J x ⊗ₜ[𝕜] J y := by
  simp [tensorSquareEquiv]

/-- The tensor-square commuting square for the transported operator. -/
theorem tensorSquare_intertwines
    (J : Spin ≃ₗ[𝕜] C)
    (R : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (Spin ⊗[𝕜] Spin)) :
    (tensorSquareEquiv J).trans (transportedCheckR J R) =
      R.trans (tensorSquareEquiv J) := by
  apply LinearEquiv.ext
  intro x
  simp [transportedCheckR, LinearEquiv.trans_apply]

/-- Conjugation preserves composition of local tensor operators. -/
theorem transportedCheckR_comp
    (J : Spin ≃ₗ[𝕜] C)
    (R S : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (Spin ⊗[𝕜] Spin)) :
    transportedCheckR J (R.trans S) =
      (transportedCheckR J R).trans (transportedCheckR J S) := by
  apply LinearEquiv.ext
  intro x
  simp [transportedCheckR, LinearEquiv.trans_apply]

/-- The transported monodromy is the conjugate of the source monodromy. -/
theorem transportedMonodromy_intertwines
    (J : Spin ≃ₗ[𝕜] C)
    (R : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (Spin ⊗[𝕜] Spin)) :
    transportedCheckR J (R.trans R) =
      (transportedCheckR J R).trans (transportedCheckR J R) := by
  exact transportedCheckR_comp J R R

/-- Nontrivial source monodromy remains nontrivial after equivalence transport. -/
theorem transportedMonodromy_ne_id
    (J : Spin ≃ₗ[𝕜] C)
    (R : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (Spin ⊗[𝕜] Spin))
    (hR : R.trans R ≠ LinearEquiv.refl 𝕜 (Spin ⊗[𝕜] Spin)) :
    (transportedCheckR J R).trans (transportedCheckR J R) ≠
      LinearEquiv.refl 𝕜 (C ⊗[𝕜] C) := by
  intro hC
  apply hR
  apply LinearEquiv.ext
  intro x
  have hcomm := congrArg
    (fun e : (Spin ⊗[𝕜] Spin) ≃ₗ[𝕜] (C ⊗[𝕜] C) => e x)
    (tensorSquare_intertwines J (R.trans R))
  have hfixed := congrArg
    (fun e : (C ⊗[𝕜] C) ≃ₗ[𝕜] (C ⊗[𝕜] C) =>
      e (tensorSquareEquiv J x)) hC
  rw [← transportedCheckR_comp J R R] at hfixed
  have hcomm' :
      transportedCheckR J (R.trans R) (tensorSquareEquiv J x) =
        tensorSquareEquiv J ((R.trans R) x) := by
    simpa [LinearEquiv.trans_apply] using hcomm
  have hfixed' :
      transportedCheckR J (R.trans R) (tensorSquareEquiv J x) =
        tensorSquareEquiv J x := by
    simpa [LinearEquiv.trans_apply] using hfixed
  exact (tensorSquareEquiv J).injective (hcomm'.symm.trans hfixed')

end InfoGeometry.Canonical.SpinCuntzTensorIntertwinerBridge
