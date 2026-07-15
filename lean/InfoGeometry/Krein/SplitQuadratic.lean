import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.Representation
import Mathlib.Analysis.InnerProductSpace.Calculus
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace
open InfoGeometry.Krein

namespace SplitQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The split/Krein carrier used by the quadratic layer. -/
abbrev SplitKreinSpace := H₂

/-- Indefinite Krein quadratic form: q(x) = B(x, x). -/
noncomputable def qform (u : SplitKreinSpace (E := E)) : ℝ :=
  KreinSpace.kreinInner (H := H₂) u u

@[simp] theorem qform_eq_kreinInner (u : SplitKreinSpace (E := E)) :
    qform (E := E) u = KreinSpace.kreinInner (H := H₂) u u := rfl

/-- Hilbertized J-positive form: <x, x>_J = B(x, Jx). -/
noncomputable def jForm (u : SplitKreinSpace (E := E)) : ℝ :=
  KreinSpace.kreinInner (H := H₂) u (spectral_epsilon (E := E) u)

@[simp] theorem jForm_eq_kreinInner_twist (u : SplitKreinSpace (E := E)) :
    jForm (E := E) u = KreinSpace.kreinInner (H := H₂) u (spectral_epsilon (E := E) u) := rfl

/-- A vector is null when its split quadratic form vanishes. -/
def IsNull (u : SplitKreinSpace (E := E)) : Prop :=
  qform (E := E) u = 0

/-- A vector is Krein-positive when its indefinite split quadratic form is positive. -/
def IsKreinPositive (u : SplitKreinSpace (E := E)) : Prop :=
  0 < qform (E := E) u

/-- A vector is Krein-negative when its indefinite split quadratic form is negative. -/
def IsKreinNegative (u : SplitKreinSpace (E := E)) : Prop :=
  qform (E := E) u < 0

/-- A vector is J-positive when its Hilbertized form is positive. -/
def IsJPositive (u : SplitKreinSpace (E := E)) : Prop :=
  0 < jForm (E := E) u

/-- Alias for the sign sector of the indefinite quadratic form. -/
abbrev IsPositive (u : SplitKreinSpace (E := E)) : Prop :=
  IsKreinPositive (E := E) u

/-- Alias for the negative sign sector of the indefinite quadratic form. -/
abbrev IsNegative (u : SplitKreinSpace (E := E)) : Prop :=
  IsKreinNegative (E := E) u

@[simp] theorem qform_neg (u : SplitKreinSpace (E := E)) :
    qform (E := E) (-u) = qform (E := E) u := by
  unfold qform
  simp [KreinSpace.kreinInner, inner_neg_left, inner_neg_right]

@[simp] theorem jForm_neg (u : SplitKreinSpace (E := E)) :
    jForm (E := E) (-u) = jForm (E := E) u := by
  unfold jForm
  have h_J_neg : spectral_epsilon (E := E) (-u) = - spectral_epsilon (E := E) u :=
    map_neg (spectral_epsilon (E := E)) u
  rw [h_J_neg]
  simp [KreinSpace.kreinInner, inner_neg_left, inner_neg_right]

@[simp] theorem isNull_neg (u : SplitKreinSpace (E := E)) :
    IsNull (E := E) (-u) ↔ IsNull (E := E) u := by
  unfold IsNull
  rw [qform_neg]

@[simp] theorem isKreinPositive_neg (u : SplitKreinSpace (E := E)) :
    IsKreinPositive (E := E) (-u) ↔ IsKreinPositive (E := E) u := by
  unfold IsKreinPositive
  rw [qform_neg]

@[simp] theorem isKreinNegative_neg (u : SplitKreinSpace (E := E)) :
    IsKreinNegative (E := E) (-u) ↔ IsKreinNegative (E := E) u := by
  unfold IsKreinNegative
  rw [qform_neg]

@[simp] theorem isJPositive_neg (u : SplitKreinSpace (E := E)) :
    IsJPositive (E := E) (-u) ↔ IsJPositive (E := E) u := by
  unfold IsJPositive
  rw [jForm_neg]

/--
The split quadratic potential on the doubled/Krein carrier.
Unlike the Euclidean convex case, this potential is indefinite.
-/
noncomputable def potential (u : H₂) : ℝ :=
  (1 / 2 : ℝ) * KreinSpace.kreinInner (H := H₂) u u

@[simp] theorem potential_eq_half_qform (u : H₂) :
    potential (E := E) u = (1 / 2 : ℝ) * qform (E := E) u := rfl

/-- Nullness is equivalent to vanishing potential. -/
theorem isNull_iff_potential_eq_zero (u : H₂) :
    IsNull (E := E) u ↔ potential (E := E) u = 0 := by
  constructor
  · intro hu
    unfold IsNull qform potential at *
    nlinarith
  · intro hu
    unfold IsNull qform potential at *
    nlinarith

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

omit [CompleteSpace E] in
/-- The doubled-space fundamental symmetry is Hilbert-self-adjoint. -/
lemma spectral_epsilon_selfAdj (u v : H₂) :
    inner ℝ (spectral_epsilon (E := E) u) v = inner ℝ u (spectral_epsilon (E := E) v) := by
  simp [spectral_epsilon, WithLp.prod_inner_apply]

omit [CompleteSpace E] in
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

end SplitQuadratic
