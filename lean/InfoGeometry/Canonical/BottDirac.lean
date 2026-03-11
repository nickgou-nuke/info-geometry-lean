import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.SpectralInference
import Mathlib.LinearAlgebra.TensorProduct.Map

open scoped TensorProduct

namespace InfoGeometry.Canonical.BottDirac

section Core

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Real-linear endomorphisms. -/
abbrev Endomorphism (V : Type*) [AddCommMonoid V] [Module ℝ V] := V →ₗ[ℝ] V

/--
Dirac operator on the Bott tensor product:
`D_bott = D₁ ⊗ Id + Γ₁ ⊗ Dₙ`.
-/
def bottDirac
    (D1 Γ1 : Endomorphism E) (Dn : Endomorphism F) :
    Endomorphism (E ⊗[ℝ] F) :=
  (TensorProduct.map D1 (LinearMap.id : Endomorphism F)) +
    (TensorProduct.map Γ1 Dn)

/-- Chiral anti-commutation condition on the first factor. -/
def IsChiralDirac (D1 Γ1 : Endomorphism E) : Prop :=
  D1.comp Γ1 + Γ1.comp D1 = 0

/-- Involutive grading condition `Γ₁² = Id`. -/
def IsInvolutiveGrading (Γ1 : Endomorphism E) : Prop :=
  Γ1.comp Γ1 = (LinearMap.id : Endomorphism E)

@[simp] lemma bottDirac_apply_tmul
    (D1 Γ1 : Endomorphism E) (Dn : Endomorphism F) (u : E) (v : F) :
    bottDirac D1 Γ1 Dn (u ⊗ₜ[ℝ] v)
      = D1 u ⊗ₜ[ℝ] v + Γ1 u ⊗ₜ[ℝ] Dn v := by
  simp [bottDirac, TensorProduct.map_tmul]

/--
Pure-tensor form of Bott-Dirac Laplacian splitting:
cross terms cancel under chiral anti-commutation.
-/
lemma bottDirac_sq_eq_sum_laplacians_tmul
    (D1 Γ1 : Endomorphism E) (Dn : Endomorphism F)
    (hChiral : IsChiralDirac D1 Γ1)
    (hGrading : IsInvolutiveGrading Γ1)
    (u : E) (v : F) :
    ((bottDirac D1 Γ1 Dn).comp (bottDirac D1 Γ1 Dn)) (u ⊗ₜ[ℝ] v) =
      ((TensorProduct.map (D1.comp D1) (LinearMap.id : Endomorphism F)) +
        (TensorProduct.map (LinearMap.id : Endomorphism E) (Dn.comp Dn))) (u ⊗ₜ[ℝ] v) := by
  have hChiral_u : D1 (Γ1 u) + Γ1 (D1 u) = 0 := by
    have h := congrArg (fun T : Endomorphism E => T u) hChiral
    simpa [IsChiralDirac, LinearMap.comp_apply, LinearMap.add_apply] using h
  have hGrading_u : Γ1 (Γ1 u) = u := by
    have h := congrArg (fun T : Endomorphism E => T u) hGrading
    simpa [IsInvolutiveGrading, LinearMap.comp_apply] using h
  unfold bottDirac
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, add_assoc, add_comm]
  have hMid : D1 (Γ1 u) ⊗ₜ[ℝ] Dn v + Γ1 (D1 u) ⊗ₜ[ℝ] Dn v = 0 := by
    calc
      D1 (Γ1 u) ⊗ₜ[ℝ] Dn v + Γ1 (D1 u) ⊗ₜ[ℝ] Dn v
          = (D1 (Γ1 u) + Γ1 (D1 u)) ⊗ₜ[ℝ] Dn v := by
              rw [TensorProduct.add_tmul]
      _ = 0 := by simp [hChiral_u]
  calc
    D1 (Γ1 u) ⊗ₜ[ℝ] Dn v + (Γ1 (D1 u) ⊗ₜ[ℝ] Dn v + Γ1 (Γ1 u) ⊗ₜ[ℝ] Dn (Dn v))
        = (D1 (Γ1 u) ⊗ₜ[ℝ] Dn v + Γ1 (D1 u) ⊗ₜ[ℝ] Dn v)
            + Γ1 (Γ1 u) ⊗ₜ[ℝ] Dn (Dn v) := by
              simp [add_assoc]
    _ = 0 + Γ1 (Γ1 u) ⊗ₜ[ℝ] Dn (Dn v) := by rw [hMid]
    _ = u ⊗ₜ[ℝ] Dn (Dn v) := by simp [hGrading_u]

/--
Global Bott-Dirac Laplacian splitting:
`D_bott² = D₁² ⊗ Id + Id ⊗ Dₙ²`.
-/
theorem bottDirac_sq_eq_sum_laplacians
    (D1 Γ1 : Endomorphism E) (Dn : Endomorphism F)
    (hChiral : IsChiralDirac D1 Γ1)
    (hGrading : IsInvolutiveGrading Γ1) :
    (bottDirac D1 Γ1 Dn).comp (bottDirac D1 Γ1 Dn) =
      (TensorProduct.map (D1.comp D1) (LinearMap.id : Endomorphism F)) +
      (TensorProduct.map (LinearMap.id : Endomorphism E) (Dn.comp Dn)) := by
  ext u v
  exact bottDirac_sq_eq_sum_laplacians_tmul D1 Γ1 Dn hChiral hGrading u v

end Core

section SpectralBridge

open InfoGeometry.Canonical.SpectralInference

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- `InfoSpectralTriple.D` exposed as a linear endomorphism for tensor lifting. -/
abbrev spectralDiracLinear (IST : InfoSpectralTriple E) : Endomorphism E :=
  IST.D.toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] lemma spectralDiracLinear_apply (IST : InfoSpectralTriple E) (x : E) :
    spectralDiracLinear IST x = IST.D x := rfl

end SpectralBridge

section Cl11Bridge

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `Cl(1,1)` Dirac seed from modular conjugation. -/
noncomputable abbrev cl11DiracSeed : Endomorphism (DoubledSpace E) :=
  (modular_j (E := E)).toLinearMap

/-- `Cl(1,1)` chiral grading from spectral sign involution. -/
noncomputable abbrev cl11Grading : Endomorphism (DoubledSpace E) :=
  (spectral_epsilon (E := E)).toLinearMap

/-- Lemma `cl11_isChiralDirac`. -/
lemma cl11_isChiralDirac :
    IsChiralDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) := by
  have hAnti :
      cl11DiracSeed (E := E).comp (cl11Grading (E := E))
        = -(cl11Grading (E := E).comp (cl11DiracSeed (E := E))) := by
    simpa [cl11DiracSeed, cl11Grading] using
      congrArg ContinuousLinearMap.toLinearMap (modular_j_spectral_epsilon_anticommute (E := E))
  calc
    cl11DiracSeed (E := E).comp (cl11Grading (E := E))
        + cl11Grading (E := E).comp (cl11DiracSeed (E := E))
      = -(cl11Grading (E := E).comp (cl11DiracSeed (E := E)))
          + cl11Grading (E := E).comp (cl11DiracSeed (E := E)) := by
            rw [hAnti]
    _ = 0 := by simp

/-- Lemma `cl11Grading_involutive`. -/
lemma cl11Grading_involutive :
    IsInvolutiveGrading (cl11Grading (E := E)) := by
  simpa [IsInvolutiveGrading, cl11Grading] using
    congrArg ContinuousLinearMap.toLinearMap (spectral_epsilon_involution (E := E))

/--
Concrete Bott-Dirac splitting for the `Cl(1,1)` pair
`(modular_j, spectral_epsilon)` on the first tensor factor.
-/
theorem cl11_bottDirac_sq_eq_sum_laplacians
    (Dn : Endomorphism F) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
      =
    (TensorProduct.map
      ((cl11DiracSeed (E := E)).comp (cl11DiracSeed (E := E)))
      (LinearMap.id : Endomorphism F))
      +
    (TensorProduct.map
      (LinearMap.id : Endomorphism (DoubledSpace E))
      (Dn.comp Dn)) := by
  exact bottDirac_sq_eq_sum_laplacians
    (D1 := cl11DiracSeed (E := E))
    (Γ1 := cl11Grading (E := E))
    (Dn := Dn)
    (hChiral := cl11_isChiralDirac (E := E))
    (hGrading := cl11Grading_involutive (E := E))

/--
Canonical `Cl(1,1)` Bott Laplacian operator reused by downstream modules.
-/
noncomputable def cl11BottLaplacian (Dn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  (TensorProduct.map
    ((cl11DiracSeed (E := E)).comp (cl11DiracSeed (E := E)))
    (LinearMap.id : Endomorphism F))
    +
  (TensorProduct.map
    (LinearMap.id : Endomorphism (DoubledSpace E))
    (Dn.comp Dn))

/--
Rewriting form of the split Bott-Dirac square into the canonical
`cl11BottLaplacian`.
-/
theorem cl11_bottDirac_sq_eq_cl11BottLaplacian
    (Dn : Endomorphism F) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
      = cl11BottLaplacian (E := E) Dn := by
  simpa [cl11BottLaplacian] using
    (cl11_bottDirac_sq_eq_sum_laplacians (E := E) (F := F) (Dn := Dn))

end Cl11Bridge

end InfoGeometry.Canonical.BottDirac
