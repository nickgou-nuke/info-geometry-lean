import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.Algebra.Module.StrongTopology
import InfoGeometry.Singular.MoorePenroseAdjoint
import InfoGeometry.Singular.DrazinAdjoint
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Core.Involution

/-!
# Singular Natural Gradient Flow on Krein Spaces

This module wires singular-flow structures to the canonical Mathlib-based Krein stack.
It keeps the API used by downstream singular-bridge modules.
-/

namespace InfoGeometry.Singular.Architecture

open InfoGeometry.Singular.MoorePenroseAdjoint
open InfoGeometry.Singular.DrazinAdjoint
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Commutator on doubled endomorphisms. -/
def clmComm
    (A B : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  A * B - B * A

/-- Hilbert-side Krein adjoint alias used by the singular boundary stack. -/
noncomputable abbrev kreinAdjointH
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  KreinSpace.kreinAdjoint (H := HilbertDoubled E) A

@[simp] lemma kreinAdjointH_involutive
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (kreinAdjointH (E := E) A) = A := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_involutive (H := HilbertDoubled E) A

@[simp] lemma kreinAdjointH_comp
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (A * B) =
      kreinAdjointH (E := E) B * kreinAdjointH (E := E) A := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_mul (H := HilbertDoubled E) A B

@[simp] lemma kreinAdjointH_add
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    kreinAdjointH (E := E) (A + B) =
      kreinAdjointH (E := E) A + kreinAdjointH (E := E) B := by
  unfold kreinAdjointH
  exact KreinSpace.kreinAdjoint_add (H := HilbertDoubled E) A B

/-- Hilbert-carrier skew-adjointness predicate used by singular bridge files. -/
abbrev IsKreinSkewAdjointH
    (X : HilbertDoubled E →L[ℝ] HilbertDoubled E) : Prop :=
  kreinAdjointH (E := E) X = -X

/--
The adjoint interface for singular Moore-Penrose/Drazin algebraic API
on the Hilbert-doubled carrier.
-/
noncomputable instance KreinAdjointH_AdjointLike :
    AdjointLike (HilbertDoubled E →L[ℝ] HilbertDoubled E) where
  adj := kreinAdjointH (E := E)
  invol := fun A => kreinAdjointH_involutive (E := E) A
  mul_rev := fun A B => kreinAdjointH_comp (E := E) A B
  add := fun A B => kreinAdjointH_add (E := E) A B
  zero := by
    ext v
    simp [kreinAdjointH, KreinSpace.kreinAdjoint]
  one := by
    change kreinAdjointH (E := E) (ContinuousLinearMap.id ℝ (HilbertDoubled E))
      = ContinuousLinearMap.id ℝ (HilbertDoubled E)
    unfold kreinAdjointH
    exact KreinSpace.kreinAdjoint_id (H := HilbertDoubled E)
  neg := by
    intro A
    ext v
    simp [kreinAdjointH, KreinSpace.kreinAdjoint]

/--
Natural gradient operator on the singular boundary:
`G⁺ grad_f` relative to a Moore-Penrose witness.
-/
noncomputable def OperatorNaturalGradient
    (G G_pinv grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E)
    (_hMP : IsMoorePenroseInverse G G_pinv) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  G_pinv * grad_f

/-- Placeholder infinitesimal-isometry predicate on doubled coordinates. -/
def IsInfinitesimalIsometry
    (_A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) : Prop := True

/--
Singular Natural Gradient Flow package.
-/
structure SingularNaturalGradientFlow (G grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E) where
  G_pinv : HilbertDoubled E →L[ℝ] HilbertDoubled E
  is_mp : IsMoorePenroseInverse G G_pinv
  generator : HilbertDoubled E →L[ℝ] HilbertDoubled E
  gen_def : generator = OperatorNaturalGradient G G_pinv grad_f is_mp
  D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E
  k_index : ℕ
  is_drazin : IsDrazinInverse G D_inv k_index
  transport_generator : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E
  isometry : IsInfinitesimalIsometry (E := E) transport_generator

/--
Extract the chiral anomaly associated to a singular flow package.
-/
noncomputable def extractFlowAnomaly
    {G grad_f : HilbertDoubled E →L[ℝ] HilbertDoubled E}
    (flow : SingularNaturalGradientFlow G grad_f) :
    HilbertDoubled E →L[ℝ] HilbertDoubled E :=
  ChiralAnomaly G flow.G_pinv flow.D_inv flow.k_index flow.is_mp flow.is_drazin

/-! ## Transport morphism: Hilbert doubled ↔ coordinate doubled -/

/-- Canonical equivalence between Hilbert/coordinate doubled carriers (identity by alias). -/
noncomputable def hilbertToDoubledEquiv :
    HilbertDoubled E ≃L[ℝ] Krein.DoubledSpace E :=
  ContinuousLinearEquiv.refl ℝ (Krein.DoubledSpace E)

/-- Inverse canonical equivalence `E×E ≃L[ℝ] WithLp 2 (E×E)`. -/
noncomputable def doubledToHilbertEquiv :
    Krein.DoubledSpace E ≃L[ℝ] HilbertDoubled E :=
  (hilbertToDoubledEquiv (E := E)).symm

/-- Operator transport by conjugation with the Hilbert/coordinate equivalence. -/
noncomputable def transportToDoubled
    (A : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  A

lemma transportToDoubled_sub
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    transportToDoubled (E := E) (A - B)
      = transportToDoubled (E := E) A - transportToDoubled (E := E) B := by
  rfl

lemma transportToDoubled_comp
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    transportToDoubled (E := E) (A * B)
      = (transportToDoubled (E := E) A).comp (transportToDoubled (E := E) B) := by
  rfl

lemma transportToDoubled_comm
    (A B : HilbertDoubled E →L[ℝ] HilbertDoubled E) :
    transportToDoubled (E := E) (A * B - B * A)
      = clmComm (transportToDoubled (E := E) A) (transportToDoubled (E := E) B) := by
  unfold clmComm
  rw [transportToDoubled_sub, transportToDoubled_comp, transportToDoubled_comp]
  simp [ContinuousLinearMap.mul_def]

/-! ## Cartan involution on doubled endomorphisms -/

/-- Cartan involution by conjugation with `modularJ` on doubled operators. -/
noncomputable def cartanInvolution
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  (modularJ (E := E)).comp (A.comp (modularJ (E := E)))

omit [CompleteSpace E] in
lemma cartanInvolution_add
    (A B : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    cartanInvolution (E := E) (A + B)
      = cartanInvolution (E := E) A + cartanInvolution (E := E) B := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective 2)
  simp [cartanInvolution]

omit [CompleteSpace E] in
lemma cartanInvolution_smul (a : ℝ)
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    cartanInvolution (E := E) (a • A) = a • cartanInvolution (E := E) A := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective 2)
  simp [cartanInvolution]

omit [CompleteSpace E] in
lemma cartanInvolution_involutive
    (A : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    cartanInvolution (E := E) (cartanInvolution (E := E) A) = A := by
  have hJ : ∀ z : Krein.DoubledSpace E,
      modularJ (E := E) (modularJ (E := E) z) = z := by
    intro z
    simpa using congrArg (fun F => F z) (modularJ_involution (E := E))
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective 2)
  simp [cartanInvolution, hJ]

omit [CompleteSpace E] in
lemma cartanInvolution_clmComm
    (A B : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    cartanInvolution (E := E) (clmComm A B)
      = clmComm (cartanInvolution (E := E) A) (cartanInvolution (E := E) B) := by
  have hJ : ∀ z : Krein.DoubledSpace E,
      modularJ (E := E) (modularJ (E := E) z) = z := by
    intro z
    simpa using congrArg (fun F => F z) (modularJ_involution (E := E))
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.ofLp_injective 2)
  simp [clmComm, cartanInvolution, hJ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Cartan involution packaged in the core involution API. -/
noncomputable def cartanInvolutionAuto :
    InfoGeometry.Core.InvolutiveAutomorphism
      (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) where
  toFun := cartanInvolution (E := E)
  involutive := by
    intro A
    simpa using cartanInvolution_involutive (E := E) A

omit [CompleteSpace E] in
lemma cartanInvolutionAuto_preservesLinear :
    InfoGeometry.Core.PreservesLinear
      (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E)
      (cartanInvolutionAuto (E := E)) where
  map_add := by
    intro A B
    exact cartanInvolution_add (E := E) A B
  map_smul := by
    intro a A
    exact cartanInvolution_smul (E := E) a A

omit [CompleteSpace E] in
lemma clmComm_neg_neg
    (A B : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    clmComm (-A) (-B) = clmComm A B := by
  change (-A) * (-B) - (-B) * (-A) = A * B - B * A
  have hLie :
      (⁅-A, -B⁆ : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) = ⁅A, B⁆ := by
    rw [neg_lie, lie_neg, neg_neg]
  simpa [Ring.lie_def] using hLie

/-- Tangent-space projection to the `-1` Cartan component. -/
noncomputable def tangentProjection
    (X : Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :
    Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E :=
  InfoGeometry.Core.cartanMinus
    ⟨cartanInvolutionAuto (E := E), cartanInvolutionAuto_preservesLinear (E := E)⟩ X

/--
Anomaly stability: if transported MP and Drazin projectors are `-1` eigenvectors
for the Cartan involution, then the transported anomaly is fixed by `cartanPlus`.
-/
lemma chiralAnomaly_in_compact_subalgebra
    (G G_pinv D_inv : HilbertDoubled E →L[ℝ] HilbertDoubled E) (k : ℕ)
    (hMP : IsMoorePenroseInverse G G_pinv) (hD : IsDrazinInverse G D_inv k)
    (hP_MP_p :
      cartanInvolution (E := E) (transportToDoubled (E := E) (MP_Projector G G_pinv hMP))
        = -transportToDoubled (E := E) (MP_Projector G G_pinv hMP))
    (hP_D_p :
      cartanInvolution (E := E) (transportToDoubled (E := E) (Drazin_Projector G D_inv k hD))
        = -transportToDoubled (E := E) (Drazin_Projector G D_inv k hD)) :
    InfoGeometry.Core.cartanPlus
      ⟨cartanInvolutionAuto (E := E), cartanInvolutionAuto_preservesLinear (E := E)⟩
      (transportToDoubled (E := E) (ChiralAnomaly G G_pinv D_inv k hMP hD))
      = transportToDoubled (E := E) (ChiralAnomaly G G_pinv D_inv k hMP hD) := by
  unfold ChiralAnomaly
  rw [transportToDoubled_comm]
  let X := transportToDoubled (E := E) (MP_Projector G G_pinv hMP)
  let Y := transportToDoubled (E := E) (Drazin_Projector G D_inv k hD)
  have hX : cartanInvolution (E := E) X = -X := by
    simpa [X] using hP_MP_p
  have hY : cartanInvolution (E := E) Y = -Y := by
    simpa [Y] using hP_D_p
  have h_theta_fix : cartanInvolution (E := E) (clmComm X Y) = clmComm X Y := by
    rw [cartanInvolution_clmComm, hX, hY, clmComm_neg_neg]
  let θlin :
      InfoGeometry.Core.LinearInvolutiveAutomorphism
        (Krein.DoubledSpace E →L[ℝ] Krein.DoubledSpace E) :=
    ⟨cartanInvolutionAuto (E := E), cartanInvolutionAuto_preservesLinear (E := E)⟩
  have h_minus_zero' :
      InfoGeometry.Core.Projector.minus (cartanInvolutionAuto (E := E))
        (clmComm X Y) = 0 := by
    exact (InfoGeometry.Core.Projector.fixed_iff_minus_eq_zero
      (θ := cartanInvolutionAuto (E := E)) (v := clmComm X Y)).mp <| by
        simpa [cartanInvolutionAuto] using h_theta_fix
  have h_minus_zero :
      InfoGeometry.Core.cartanMinus θlin (clmComm X Y) = 0 := by
    simpa [InfoGeometry.Core.cartanMinus, θlin] using h_minus_zero'
  have h_decomp := InfoGeometry.Core.cartan_decomposition θlin (clmComm X Y)
  rw [h_minus_zero, add_zero] at h_decomp
  exact h_decomp.symm

end InfoGeometry.Singular.Architecture
