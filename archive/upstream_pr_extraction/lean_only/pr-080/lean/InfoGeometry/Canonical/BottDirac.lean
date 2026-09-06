import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Canonical.SpectralInference
import Mathlib.LinearAlgebra.TensorProduct.Map
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace InfoGeometry.Canonical.BottDirac

open InfoGeometry.Krein
open InfoGeometry.Quantum

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

/--
Conjugacy on the base space lifts exactly to the Bott-Dirac operator on the product.
-/
theorem bottDirac_comp_tensor_eq_tensor_comp_bottDirac
    (D1 Γ1 : Endomorphism E) (Dn Dn' e : Endomorphism F)
    (hConj : Dn.comp e = e.comp Dn') :
    (bottDirac D1 Γ1 Dn).comp (TensorProduct.map (LinearMap.id : Endomorphism E) e)
      =
    (TensorProduct.map (LinearMap.id : Endomorphism E) e).comp (bottDirac D1 Γ1 Dn') := by
  ext u v
  simp [bottDirac, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.add_apply]
  have h_eval : Dn (e v) = e (Dn' v) := by
    have h := congrArg (fun T : Endomorphism F => T v) hConj
    simpa [LinearMap.comp_apply] using h
  rw [h_eval]

end Core

section SpectralBridge

open SpectralInference

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
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Packaged doubled-space split `Cl(1,1)` seed used internally by the Bott branch. -/
private noncomputable abbrev cl11Action : RealSplitCl11Action (DoubledSpace E) :=
  doubledSpaceCl11Action (E := E)

/-- `Cl(1,1)` Dirac seed from the packaged doubled-space split action. -/
private noncomputable abbrev cl11DiracSeed : Endomorphism (DoubledSpace E) :=
  (cl11Action (E := E)).J.toLinearMap

/-- `Cl(1,1)` chiral grading from the packaged doubled-space split action. -/
private noncomputable abbrev cl11Grading : Endomorphism (DoubledSpace E) :=
  (cl11Action (E := E)).eps.toLinearMap

/-- Canonical `Cl(1,1)` Bott-Dirac operator reused by downstream modules. -/
noncomputable def cl11BottDirac (Dn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn

/-- Pointwise action formula for the canonical `Cl(1,1)` Bott-Dirac operator. -/
theorem cl11BottDirac_apply_tmul
    (Dn : Endomorphism F) (u : DoubledSpace E) (v : F) :
    cl11BottDirac (E := E) Dn (u ⊗ₜ[ℝ] v)
      = modular_j (E := E) u ⊗ₜ[ℝ] v + spectral_epsilon (E := E) u ⊗ₜ[ℝ] Dn v := by
  simp [cl11BottDirac, bottDirac, cl11DiracSeed, cl11Grading, cl11Action, TensorProduct.map_tmul]

/-- The split `Cl(1,1)` Dirac seed squares to identity. -/
theorem cl11DiracSeed_sq_eq_id :
    (cl11DiracSeed (E := E)).comp (cl11DiracSeed (E := E))
      = (LinearMap.id : Endomorphism (DoubledSpace E)) := by
  simpa [cl11DiracSeed] using
    congrArg ContinuousLinearMap.toLinearMap (modular_j_involution (E := E))

/-- The packaged doubled-space split action satisfies the Bott chiral relation. -/
private lemma cl11_isChiralDirac :
    IsChiralDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) := by
  have hAnti :
      cl11DiracSeed (E := E).comp (cl11Grading (E := E))
        = -(cl11Grading (E := E).comp (cl11DiracSeed (E := E))) := by
    simpa [cl11DiracSeed, cl11Grading, cl11Action] using
      congrArg ContinuousLinearMap.toLinearMap ((cl11Action (E := E)).J_eps_anti)
  calc
    cl11DiracSeed (E := E).comp (cl11Grading (E := E))
        + cl11Grading (E := E).comp (cl11DiracSeed (E := E))
      = -(cl11Grading (E := E).comp (cl11DiracSeed (E := E)))
          + cl11Grading (E := E).comp (cl11DiracSeed (E := E)) := by
            rw [hAnti]
    _ = 0 := by simp

/-- The packaged doubled-space split action satisfies the Bott grading involution. -/
private lemma cl11Grading_involutive :
    IsInvolutiveGrading (cl11Grading (E := E)) := by
  simpa [IsInvolutiveGrading, cl11Grading, cl11Action] using
    congrArg ContinuousLinearMap.toLinearMap ((cl11Action (E := E)).eps_sq)

/--
Concrete Bott-Dirac splitting for the `Cl(1,1)` pair
`(modular_j, spectral_epsilon)` on the first tensor factor.
-/
private theorem cl11_bottDirac_sq_eq_sum_laplacians
    (Dn : Endomorphism F) :
    (cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn)
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
    (cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn)
      = cl11BottLaplacian (E := E) Dn := by
  simpa [cl11BottDirac, cl11BottLaplacian] using
    (cl11_bottDirac_sq_eq_sum_laplacians (E := E) (F := F) (Dn := Dn))

/--
Explicit `Cl(1,1)` Bott Laplacian formula:
the first tensor channel is the identity, while the second channel carries the
square of the input Dirac operator.
-/
theorem cl11BottLaplacian_eq_tensor_id_add_tensor_dirac_sq
    (Dn : Endomorphism F) :
    cl11BottLaplacian (E := E) Dn =
      (TensorProduct.map
        (LinearMap.id : Endomorphism (DoubledSpace E))
        (LinearMap.id : Endomorphism F))
        +
      (TensorProduct.map
        (LinearMap.id : Endomorphism (DoubledSpace E))
        (Dn.comp Dn)) := by
  simp [cl11BottLaplacian, cl11DiracSeed_sq_eq_id]

/--
Explicit `Cl(1,1)` Bott-square formula:
`D_bott² = Id ⊗ Id + Id ⊗ Dₙ²`.
-/
theorem cl11_bottDirac_sq_eq_tensor_id_add_tensor_dirac_sq
    (Dn : Endomorphism F) :
    (cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn)
      =
    (TensorProduct.map
      (LinearMap.id : Endomorphism (DoubledSpace E))
      (LinearMap.id : Endomorphism F))
      +
    (TensorProduct.map
      (LinearMap.id : Endomorphism (DoubledSpace E))
      (Dn.comp Dn)) := by
  rw [cl11_bottDirac_sq_eq_cl11BottLaplacian]
  exact cl11BottLaplacian_eq_tensor_id_add_tensor_dirac_sq
    (E := E) (F := F) (Dn := Dn)

/-- Pointwise `Cl(1,1)` Bott-square formula on pure tensors. -/
theorem cl11_bottDirac_sq_apply_tmul
    (Dn : Endomorphism F)
    (u : DoubledSpace E) (v : F) :
    ((cl11BottDirac (E := E) Dn).comp
      (cl11BottDirac (E := E) Dn)) (u ⊗ₜ[ℝ] v)
      = u ⊗ₜ[ℝ] v + u ⊗ₜ[ℝ] Dn (Dn v) := by
  rw [cl11_bottDirac_sq_eq_tensor_id_add_tensor_dirac_sq (E := E) (F := F) (Dn := Dn)]
  simp [LinearMap.comp_apply, TensorProduct.map_tmul]

/--
Conjugacy of the base operator lifts exactly to the `Cl(1,1)` Bott-Dirac module.
-/
theorem cl11BottDirac_comp_tensor_eq_tensor_comp_cl11BottDirac
    (Dn Dn' e : Endomorphism F)
    (hConj : Dn.comp e = e.comp Dn') :
    (cl11BottDirac (E := E) Dn).comp (TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) e)
      =
    (TensorProduct.map (LinearMap.id : Endomorphism (DoubledSpace E)) e).comp (cl11BottDirac (E := E) Dn') := by
  exact bottDirac_comp_tensor_eq_tensor_comp_bottDirac _ _ _ _ _ hConj

/--
The lifted projective involution `J` on the doubled-space factor transports the
canonical `Cl(1,1)` Bott-Dirac operator to the sign-twisted second-factor
Dirac input.
-/
theorem cl11BottDirac_comp_tensor_modular_j_eq_tensor_comp_cl11BottDirac_neg
    (Dn Dn' e : Endomorphism F)
    (hConj : Dn.comp e = e.comp Dn') :
    (cl11BottDirac (E := E) Dn).comp
      (TensorProduct.map (modular_jLE E).toLinearMap e)
      =
    (TensorProduct.map (modular_jLE E).toLinearMap e).comp
      (cl11BottDirac (E := E) (-Dn')) := by
  ext u v
  have hEval : Dn (e v) = e (Dn' v) := by
    have h := congrArg (fun T : Endomorphism F => T v) hConj
    simpa [LinearMap.comp_apply] using h
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, cl11BottDirac_apply_tmul,
    modular_jLE, hEval]
  have hSign :
      WithLp.toLp (2 : ENNReal) (WithLp.snd u, -WithLp.fst u)
        =
      -WithLp.toLp (2 : ENNReal) (-WithLp.snd u, WithLp.fst u) := by
    apply DoubledSpace.ext <;> simp
  rw [hSign]
  simp [TensorProduct.neg_tmul, TensorProduct.tmul_neg]

end Cl11Bridge

section Cl22Bridge

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
`Cl(2,2)` Bott-Dirac module:
first split atom on `DoubledSpace E`, second split atom on `DoubledSpace F`.
-/
noncomputable def cl22Dirac :
    Endomorphism (DoubledSpace E ⊗[ℝ] DoubledSpace F) :=
  bottDirac
    (cl11DiracSeed (E := E))
    (cl11Grading (E := E))
    (cl11DiracSeed (E := F))

/--
Canonical Laplacian expression associated to the `Cl(2,2)` Bott-Dirac module.
-/
noncomputable def cl22BottLaplacian :
    Endomorphism (DoubledSpace E ⊗[ℝ] DoubledSpace F) :=
  (TensorProduct.map
    ((cl11DiracSeed (E := E)).comp (cl11DiracSeed (E := E)))
    (LinearMap.id : Endomorphism (DoubledSpace F)))
    +
  (TensorProduct.map
    (LinearMap.id : Endomorphism (DoubledSpace E))
    ((cl11DiracSeed (E := F)).comp (cl11DiracSeed (E := F)))
)

/--
`Cl(2,2)` Bott-square splitting:
`D₍₂,₂₎² = J_E² ⊗ Id + Id ⊗ J_F²`.
-/
theorem cl22_bottDirac_sq_eq_cl22BottLaplacian :
    (cl22Dirac (E := E) (F := F)).comp (cl22Dirac (E := E) (F := F))
      = cl22BottLaplacian (E := E) (F := F) := by
  simpa [cl22Dirac, cl22BottLaplacian] using
    (cl11_bottDirac_sq_eq_sum_laplacians (E := E) (F := DoubledSpace F)
      (Dn := cl11DiracSeed (E := F)))

/--
Simplified `Cl(2,2)` Bott-square:
both Laplacian channels reduce to the tensor identity, giving a doubled scale.
-/
theorem cl22_bottDirac_sq_eq_two_tensor_id :
    (cl22Dirac (E := E) (F := F)).comp (cl22Dirac (E := E) (F := F))
      =
    (2 : ℝ) •
      (TensorProduct.map
        (LinearMap.id : Endomorphism (DoubledSpace E))
        (LinearMap.id : Endomorphism (DoubledSpace F))) := by
  rw [cl22_bottDirac_sq_eq_cl22BottLaplacian (E := E) (F := F)]
  simp [cl22BottLaplacian, cl11DiracSeed_sq_eq_id, two_smul]

end Cl22Bridge

end InfoGeometry.Canonical.BottDirac
