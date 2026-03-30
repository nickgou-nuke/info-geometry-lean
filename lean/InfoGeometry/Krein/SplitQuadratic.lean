import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Representation
import Mathlib.Analysis.InnerProductSpace.Calculus
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Krein.SplitQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
The split quadratic potential on the doubled/Krein carrier.
Unlike the Euclidean convex case, this potential is indefinite.
-/
noncomputable def potential (u : H₂) : ℝ :=
  (1 / 2 : ℝ) * KreinSpace.kreinInner (H := H₂) u u

/-- The gradient is the concrete fundamental symmetry action on doubled space. -/
noncomputable def grad (u : H₂) : H₂ :=
  spectral_epsilon (E := E) u

/-- The metric operator is the same fundamental symmetry, independent of basepoint. -/
noncomputable abbrev metricOp (_u : H₂) : H₂ →L[ℝ] H₂ :=
  spectral_epsilon (E := E)

omit [CompleteSpace E] in
@[simp] theorem grad_apply (u : H₂) :
    grad (E := E) u = spectral_epsilon (E := E) u := rfl

omit [CompleteSpace E] in
@[simp] theorem metricOp_eq_spectral_epsilon (u : H₂) :
    metricOp (E := E) u = spectral_epsilon (E := E) := rfl

/-- The indefinite metric operator is exactly the split pseudoscalar action on doubled space. -/
theorem metricOp_eq_cl11Rep_pseudoscalar (u : H₂) :
    metricOp (E := E) u
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
            * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa [metricOp] using (InfoGeometry.Krein.cl11Rep_pseudoscalar (E := E)).symm

/-- The indefinite split quadratic gradient is the split pseudoscalar action applied to the state. -/
@[simp] theorem grad_eq_cl11Rep_pseudoscalar_apply (u : H₂) :
    grad (E := E) u
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)
            * CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) u := by
  rw [grad, ←InfoGeometry.Krein.cl11Rep_pseudoscalar (E := E)]

/-- The doubled-space fundamental symmetry is Hilbert-self-adjoint. -/
lemma spectral_epsilon_selfAdj (u v : H₂) :
    inner ℝ (spectral_epsilon (E := E) u) v = inner ℝ u (spectral_epsilon (E := E) v) := by
  simp [spectral_epsilon, WithLp.prod_inner_apply]

lemma hasFDerivAt_grad (u : H₂) :
    HasFDerivAt (fun x : H₂ => grad (E := E) x) (metricOp (E := E) u) u := by
  simpa [grad, metricOp] using (spectral_epsilon (E := E)).hasFDerivAt

/-- The split quadratic potential differentiates to the fundamental symmetry action. -/
lemma hasFDerivAt_potential (u : H₂) :
    HasFDerivAt (potential (E := E))
      (InnerProductSpace.toDual ℝ H₂ (grad (E := E) u)) u := by
  unfold potential
  have h_id : HasFDerivAt (fun x : H₂ => x) (1 : H₂ →L[ℝ] H₂) u := by
    simpa using (hasFDerivAt_id u)
  have h_grad :
      HasFDerivAt (fun x : H₂ => grad (E := E) x) (metricOp (E := E) u) u :=
    hasFDerivAt_grad (E := E) u
  have h_inner :
      HasFDerivAt (fun x : H₂ => inner ℝ (grad (E := E) x) x)
        ((fderivInnerCLM ℝ (grad (E := E) u, u)).comp
          ((metricOp (E := E) u).prod (1 : H₂ →L[ℝ] H₂))) u :=
    h_grad.inner ℝ h_id
  convert h_inner.const_smul (1 / 2 : ℝ) using 1
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  have hsymm :
      inner ℝ (metricOp (E := E) u v) u = inner ℝ (grad (E := E) u) v := by
    change inner ℝ (spectral_epsilon (E := E) v) u = inner ℝ (spectral_epsilon (E := E) u) v
    rw [spectral_epsilon_selfAdj]
    rw [real_inner_comm]
  rw [hsymm]
  simp [grad, InnerProductSpace.toDual_apply_apply]
  ring

/-- Signed quadratic divergence induced by the split/Krein potential. -/
noncomputable def divergence (x y : H₂) : ℝ :=
  potential (E := E) x - potential (E := E) y - inner ℝ (grad (E := E) y) (x - y)

@[simp] theorem inner_grad_eq_kreinInner (x y : H₂) :
    inner ℝ (grad (E := E) x) y = KreinSpace.kreinInner (H := H₂) x y := by
  rw [krein_inner_prod_l2 (E := E) x y]
  simp [grad, spectral_epsilon, sub_eq_add_neg]

private theorem kreinInner_right_sub (x y z : H₂) :
    KreinSpace.kreinInner (H := H₂) x (y - z)
      = KreinSpace.kreinInner (H := H₂) x y - KreinSpace.kreinInner (H := H₂) x z := by
  repeat rw [krein_inner_prod_l2 (E := E)]
  repeat rw [WithLp.ofLp_fst, WithLp.ofLp_snd]
  rw [WithLp.sub_fst, WithLp.sub_snd, inner_sub_right, inner_sub_right]
  ring

private theorem kreinInner_sub_sq (x y : H₂) :
    KreinSpace.kreinInner (H := H₂) (x - y) (x - y)
      = KreinSpace.kreinInner (H := H₂) x x
          - 2 * KreinSpace.kreinInner (H := H₂) x y
          + KreinSpace.kreinInner (H := H₂) y y := by
  repeat rw [krein_inner_prod_l2 (E := E)]
  repeat rw [WithLp.ofLp_fst, WithLp.ofLp_snd]
  rw [WithLp.sub_fst, WithLp.sub_snd]
  simp [norm_sub_sq_real]
  ring_nf

/-- The split/Krein divergence is the signed half Krein norm-square. -/
@[rep_depth krein]
theorem divergence_eq_half_signed_krein_sq (x y : H₂) :
    divergence (E := E) x y
      = (1 / 2 : ℝ) * KreinSpace.kreinInner (H := H₂) (x - y) (x - y) := by
  unfold divergence potential
  rw [inner_grad_eq_kreinInner, kreinInner_right_sub]
  have hsymm : KreinSpace.kreinInner (H := H₂) y x = KreinSpace.kreinInner (H := H₂) x y :=
    KreinSpace.kreinInner_symm (H := H₂) y x
  rw [hsymm, kreinInner_sub_sq]
  ring

/--
The signed split/Krein interaction score decomposes into the Krein bilinear pairing
minus the two diagonal quadratic penalties.
-/
theorem neg_divergence_eq_krein_minus_half_diagonals (q k : H₂) :
    -divergence (E := E) q k
      = KreinSpace.kreinInner (H := H₂) q k
          - (1 / 2 : ℝ) * KreinSpace.kreinInner (H := H₂) q q
          - (1 / 2 : ℝ) * KreinSpace.kreinInner (H := H₂) k k := by
  rw [divergence_eq_half_signed_krein_sq, kreinInner_sub_sq]
  ring

end InfoGeometry.Krein.SplitQuadratic
