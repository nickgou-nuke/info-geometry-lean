import InfoGeometry.Twistor.TwoTwistorSpacetimeRealityAdjacency
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Incidence-plane isotropy: the unitary matrix consequence

For the repository's `(2,2)` Penrose form, total isotropy of an incidence
frame yields `Xᴴ * X = 1`.  This owner records that algebraic consequence
without identifying a unitary node with a Hermitian spacetime point.
-/

namespace InfoGeometry.Twistor.TwoTwistorIncidenceIsotropy

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwoTwistorSpacetimeNode
open Matrix

theorem incidence_isotropy_implies_unitary
    (X P Ω : ComplexSpacetime)
    (hP : IsUnit P.det)
    (hinc : Ω = (Complex.I • X) * P)
    (hisot : Ωᴴ * Ω = Pᴴ * P) :
    Xᴴ * X = 1 := by
  have hdet : P.det ≠ 0 := isUnit_iff_ne_zero.mp hP
  have hdetStar : (Pᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using hdet
  have hPStar : IsUnit (Pᴴ).det := isUnit_iff_ne_zero.mpr hdetStar
  have hfactor : Pᴴ * (Xᴴ * X) * P = Pᴴ * P := by
    calc
      Pᴴ * (Xᴴ * X) * P = ((Complex.I • X) * P)ᴴ *
          ((Complex.I • X) * P) := by
            simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
              Matrix.mul_assoc, Complex.I_mul_I, smul_smul]
      _ = Ωᴴ * Ω := by rw [← hinc]
      _ = Pᴴ * P := hisot
  have hleft := congrArg
    (fun M : ComplexSpacetime => (Pᴴ)⁻¹ * M) hfactor
  have hleft' : Xᴴ * X * P = P := by
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Pᴴ hPStar,
      Matrix.one_mul] using hleft
  have hright := congrArg
    (fun M : ComplexSpacetime => M * P⁻¹) hleft'
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP] using hright

theorem frameSpacetimeNode_isotropy_implies_unitary
    (P Ω : ComplexSpacetime)
    (hP : IsUnit P.det)
    (hisot : Ωᴴ * Ω = Pᴴ * P) :
    (frameSpacetimeNode P Ω)ᴴ * frameSpacetimeNode P Ω = 1 := by
  apply incidence_isotropy_implies_unitary
    (frameSpacetimeNode P Ω) P Ω hP ?_ hisot
  exact (frameSpacetimeNode_mul_frame P Ω hP).symm

/-- Hermiticity of the reconstructed node is equivalent to the skew-Hermitian
frame coefficient identity in the repository's convention `Ω = i X P`. -/
theorem incidence_hermitian_iff_frame_skew
    (X P Ω : ComplexSpacetime)
    (hP : IsUnit P.det)
    (hinc : Ω = (Complex.I • X) * P) :
    Xᴴ = X ↔ Pᴴ * Ω + Ωᴴ * P = 0 := by
  have hdet : P.det ≠ 0 := isUnit_iff_ne_zero.mp hP
  have hdetStar : (Pᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using hdet
  have hPStar : IsUnit (Pᴴ).det := isUnit_iff_ne_zero.mpr hdetStar
  constructor
  · intro hX
    rw [hinc]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul]
    rw [hX]
    simp [Matrix.mul_assoc, Complex.I_mul_I, smul_smul]
  · intro hframe
    have hscalar : Complex.I •
        (Pᴴ * (X * P) - Pᴴ * (Xᴴ * P)) = 0 := by
      rw [hinc, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] at hframe
      simpa [Matrix.mul_assoc, sub_eq_add_neg, Matrix.smul_mul,
        Matrix.mul_smul, smul_add, smul_neg, smul_smul] using hframe
    have hdiff : Pᴴ * (X * P) - Pᴴ * (Xᴴ * P) = 0 := by
      have hcancel := congrArg
        (fun M : ComplexSpacetime => (-Complex.I) • M) hscalar
      simpa [smul_smul] using hcancel
    have hfactor : Pᴴ * (X - Xᴴ) * P = 0 := by
      calc
        Pᴴ * (X - Xᴴ) * P =
            Pᴴ * (X * P) - Pᴴ * (Xᴴ * P) := by noncomm_ring
        _ = 0 := hdiff
    have hleft := congrArg
      (fun M : ComplexSpacetime => (Pᴴ)⁻¹ * M) hfactor
    have hleft' : (X - Xᴴ) * P = 0 := by
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Pᴴ hPStar,
        Matrix.one_mul, zero_mul, mul_zero] using hleft
    have hright := congrArg
      (fun M : ComplexSpacetime => M * P⁻¹) hleft'
    have hzero : X - Xᴴ = 0 := by
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP] using hright
    exact (sub_eq_zero.mp hzero).symm

theorem frameSpacetimeNode_hermitian_iff_frame_skew
    (P Ω : ComplexSpacetime)
    (hP : IsUnit P.det) :
    (frameSpacetimeNode P Ω)ᴴ = frameSpacetimeNode P Ω ↔
      Pᴴ * Ω + Ωᴴ * P = 0 := by
  apply incidence_hermitian_iff_frame_skew
    (frameSpacetimeNode P Ω) P Ω hP
  exact (frameSpacetimeNode_mul_frame P Ω hP).symm

/-- Isotropy together with the required frame-skew condition yields a
Hermitian reconstructed spacetime node.  Isotropy is retained explicitly
because it is the Penrose incidence hypothesis; Hermiticity itself is
supplied by the frame-skew half of the preceding equivalence. -/
theorem frameSpacetimeNode_isotropy_and_frame_skew_implies_hermitian
    (P Ω : ComplexSpacetime)
    (hP : IsUnit P.det)
    (_hisot : Ωᴴ * Ω = Pᴴ * P)
    (hframe : Pᴴ * Ω + Ωᴴ * P = 0) :
    (frameSpacetimeNode P Ω)ᴴ = frameSpacetimeNode P Ω := by
  exact (frameSpacetimeNode_hermitian_iff_frame_skew P Ω hP).2 hframe

/-- The Penrose Hermitian isotropy equation alone does not imply spacetime
Hermiticity.  The scalar unitary matrix `i I` is an explicit counterexample. -/
theorem isotropy_does_not_imply_hermitian :
    ∃ (X P Ω : ComplexSpacetime),
      IsUnit P.det ∧
      Ω = (Complex.I • X) * P ∧
      Ωᴴ * Ω = Pᴴ * P ∧
      Xᴴ * X = 1 ∧
      Xᴴ ≠ X := by
  let X : ComplexSpacetime := Complex.I • (1 : ComplexSpacetime)
  let P : ComplexSpacetime := 1
  let Ω : ComplexSpacetime := -1
  refine ⟨X, P, Ω, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P]
  · simp [X, P, Ω, smul_smul, Complex.I_mul_I]
  · simp [P, Ω, Matrix.conjTranspose_smul, smul_smul]
  · simp [X, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Complex.I_mul_I]
  · intro h
    have h00 := congrArg (fun M : ComplexSpacetime => M 0 0) h
    have him := congrArg Complex.im h00
    norm_num [X, Matrix.conjTranspose_smul, smul_smul] at him

end InfoGeometry.Twistor.TwoTwistorIncidenceIsotropy
