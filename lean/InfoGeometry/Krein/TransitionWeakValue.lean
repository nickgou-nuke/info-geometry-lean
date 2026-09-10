import InfoGeometry.Krein.DoubledSpace
import Mathlib.Tactic

/-!
# Transition weak readouts on the existing doubled Krein carrier

The transition overlap pairs the two base components in the Hilbert metric.
It is distinct from the diagonal Krein self-pairing. All readouts are ordinary
Mathlib quotients; the physically admissible chart additionally requires a
nonzero denominator. A null vector is not an operator kernel vector.

The final transport theorem uses the existing `KreinHom` owner. No matrix
replacement of the categorical carrier, continuum completion, PDE equivalence,
or phase-conjugate continuation is introduced here.
-/

noncomputable section
open scoped InnerProductSpace

namespace InfoGeometry.Krein.TransitionWeakValue

section Doubled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Real transition overlap between the two base components. -/
def overlap (v : DoubledSpace E) : ℝ :=
  inner ℝ (WithLp.snd v) (WithLp.fst v)

/-- Transition matrix element of a base-carrier observable. -/
def numerator (A : E →L[ℝ] E) (v : DoubledSpace E) : ℝ :=
  inner ℝ (WithLp.snd v) (A (WithLp.fst v))

/-- Algebraic readout; interpretation as a weak value requires `overlap v ≠ 0`. -/
def readout (A : E →L[ℝ] E) (v : DoubledSpace E) : ℝ :=
  numerator A v / overlap v

@[simp] theorem overlap_to_doubled (x y : E) :
    overlap (to_doubled x y) = inner ℝ y x := rfl

@[simp] theorem numerator_to_doubled (A : E →L[ℝ] E) (x y : E) :
    numerator A (to_doubled x y) = inner ℝ y (A x) := rfl

/-- Diagonal Krein nullity is equality of sheet norms, not orthogonality. -/
theorem krein_self_to_doubled (x y : E) :
    KreinSpace.kreinInner (to_doubled x y) (to_doubled x y) =
      ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [krein_inner_prod_l2]
  change inner ℝ x x - inner ℝ y y = ‖x‖ ^ 2 - ‖y‖ ^ 2
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- A nonzero diagonal state is null and has nonzero transition overlap. -/
theorem diagonal_null_nonzero_overlap {x : E} (hx : x ≠ 0) :
    KreinSpace.kreinInner (to_doubled x x) (to_doubled x x) = 0 ∧
      overlap (to_doubled x x) ≠ 0 := by
  constructor
  · rw [krein_self_to_doubled]
    simp
  · rw [overlap_to_doubled, real_inner_self_eq_norm_sq]
    exact ne_of_gt (pow_pos (norm_pos_iff.mpr hx) 2)

/-- Orthogonality with unequal norms gives the converse separation. -/
theorem orthogonal_overlap_zero_nonnull {x y : E}
    (hxy : inner ℝ y x = 0) (hnorm : ‖x‖ ^ 2 ≠ ‖y‖ ^ 2) :
    overlap (to_doubled x y) = 0 ∧
      KreinSpace.kreinInner (to_doubled x y) (to_doubled x y) ≠ 0 := by
  constructor
  · exact hxy
  · rw [krein_self_to_doubled]
    exact sub_ne_zero.mpr hnorm

/-- An explicit change of coordinates encodes the real overlap as a null test. -/
theorem hadamard_krein_self (x y : E) :
    KreinSpace.kreinInner (to_doubled (x + y) (x - y))
        (to_doubled (x + y) (x - y)) = 4 * inner ℝ y x := by
  rw [krein_inner_prod_l2]
  change inner ℝ (x + y) (x + y) - inner ℝ (x - y) (x - y) =
    4 * inner ℝ y x
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm x y]
  ring

/-- Nullity encodes overlap only after the stated Hadamard repacking. -/
theorem hadamard_null_iff_overlap_zero (x y : E) :
    KreinSpace.kreinInner (to_doubled (x + y) (x - y))
        (to_doubled (x + y) (x - y)) = 0 ↔
      overlap (to_doubled x y) = 0 := by
  rw [hadamard_krein_self, overlap_to_doubled]
  constructor <;> intro h <;> linarith

/-- Numerator cancellation: every admissible identity readout is exactly one. -/
theorem readout_id (v : DoubledSpace E) (hv : overlap v ≠ 0) :
    readout (ContinuousLinearMap.id ℝ E) v = 1 := by
  simpa [readout, numerator, overlap] using div_self hv

/-- A preselected eigenvector has a constant weak readout on its admissible chart. -/
theorem readout_of_eigenvector (A : E →L[ℝ] E) (x y : E) (a : ℝ)
    (hx : A x = a • x) (hxy : inner ℝ y x ≠ 0) :
    readout A (to_doubled x y) = a := by
  change inner ℝ y (A x) / inner ℝ y x = a
  rw [hx, real_inner_smul_right]
  field_simp [hxy]

end Doubled

section KreinTransport

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [KreinSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [KreinSpace F]

/-- A separate readout whose pairing is genuinely the Krein pairing. -/
def kreinReadout (A : H →L[ℝ] H) (φ ψ : H) : ℝ :=
  KreinSpace.kreinInner φ (A ψ) / KreinSpace.kreinInner φ ψ

/-- Existing Krein isometries preserve the null locus in both directions. -/
theorem isometry_preserves_null (U : H →L[ℝ] H)
    (hU : KreinSpace.IsKreinIsometry U) (v : H) :
    KreinSpace.kreinInner (U v) (U v) = 0 ↔
      KreinSpace.kreinInner v v = 0 := by
  rw [hU v v]

/-- In particular a globally Krein-isometric evolution cannot create global nullity. -/
theorem isometry_preserves_nonnull (U : H →L[ℝ] H)
    (hU : KreinSpace.IsKreinIsometry U) (v : H)
    (hv : KreinSpace.kreinInner v v ≠ 0) :
    KreinSpace.kreinInner (U v) (U v) ≠ 0 := by
  rwa [hU v v]

/-- The admissible weak-value chart is preserved by the owner morphism. -/
theorem kreinHom_preserves_admissibility (f : KreinHom H F) (φ ψ : H) :
    KreinSpace.kreinInner (f.hom φ) (f.hom ψ) ≠ 0 ↔
      KreinSpace.kreinInner φ ψ ≠ 0 := by
  rw [f.isometric φ ψ]

/-- Weak readouts commute with a pairing-preserving intertwiner.
This is the finite-stage compatibility law needed by existing tower/colimit owners. -/
theorem kreinReadout_intertwiner (f : KreinHom H F)
    (A : H →L[ℝ] H) (B : F →L[ℝ] F)
    (hAB : ∀ x, B (f.hom x) = f.hom (A x)) (φ ψ : H) :
    kreinReadout B (f.hom φ) (f.hom ψ) = kreinReadout A φ ψ := by
  unfold kreinReadout
  rw [hAB ψ, f.isometric φ (A ψ), f.isometric φ ψ]

end KreinTransport

end InfoGeometry.Krein.TransitionWeakValue
