/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PenroseIncidence

/-!
# Euclidean twistor incidence in the Meier--Viana convention

arXiv:2601.19983v1, (2.2)--(2.5), (4.4). The existing owner uses
(i x pi, pi); the paper uses (lambda, mu) with mu=x lambda. An explicit linear
change of convention connects these without changing the existing owner.
-/
noncomputable section
namespace InfoGeometry.Twistor.MeierViana
open scoped Matrix LinearAlgebra.Projectivization
open PenroseIncidence

def paperIncidence (x : ComplexSpacetime) : Spinor2 →ₗ[ℂ] Twistor4 where
  toFun l := (l,omegaLinearMap x l)
  map_add' _ _ := by simp [Matrix.mulVec_add]
  map_smul' _ _ := by simp

theorem paperIncidence_injective (x : ComplexSpacetime) : Function.Injective (paperIncidence x) := by
  intro a b h
  exact congrArg Prod.fst h

def toPenroseConvention : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun z := (Complex.I • z.2,z.1)
  invFun z := (z.2,(-Complex.I) • z.1)
  left_inv z := by
    apply Prod.ext
    · rfl
    · change (-Complex.I) • (Complex.I • z.2)=z.2
      rw [smul_smul]
      simp
  right_inv z := by
    apply Prod.ext
    · change Complex.I • ((-Complex.I) • z.1)=z.1
      rw [smul_smul]
      simp
    · rfl
  map_add' _ _ := by simp [smul_add]
  map_smul' _ _ := by simp [smul_smul, mul_comm]

theorem paper_to_existing_incidence (x : ComplexSpacetime) (l : Spinor2) :
    toPenroseConvention (paperIncidence x l)=incidenceLinearMap x l := rfl

def projectivePaperIncidence (x : ComplexSpacetime) : ProjectiveSpinorLine → ProjectiveTwistor3 :=
  Projectivization.map (paperIncidence x) (paperIncidence_injective x)

theorem projectivePaperIncidence_injective (x : ComplexSpacetime) :
    Function.Injective (projectivePaperIncidence x) :=
  Projectivization.map_injective _ (paperIncidence_injective x)

/-- Equation (2.4): quaternionic, not involutive, conjugation. -/
def hat (l : Spinor2) : Spinor2 := ![-star (l 1),star (l 0)]

theorem hat_hat (l : Spinor2) : hat (hat l) = -l := by
  ext i
  fin_cases i <;> simp [hat]

theorem hat_add (l m : Spinor2) : hat (l+m)=hat l+hat m := by
  ext i
  fin_cases i <;> simp [hat, add_comm]

theorem hat_smul (c : ℂ) (l : Spinor2) : hat (c • l)=star c • hat l := by
  ext i
  fin_cases i <;> simp [hat]

/-- Columns lambda, hat lambda, with index lowering made explicit by coordinates. -/
def spinorFrame (l : Spinor2) : ComplexSpacetime := !![l 0,-star (l 1);l 1,star (l 0)]

def spinorNormSq (l : Spinor2) : ℝ := Complex.normSq (l 0)+Complex.normSq (l 1)

theorem spinorFrame_det (l : Spinor2) : (spinorFrame l).det = (spinorNormSq l : ℂ) := by
  simp [spinorFrame, Matrix.det_fin_two, spinorNormSq, Complex.normSq_eq_conj_mul_self, mul_comm]

theorem spinorNormSq_pos (l : Spinor2) (hl : l≠0) : 0<spinorNormSq l := by
  have h0 := Complex.normSq_nonneg (l 0)
  have h1 := Complex.normSq_nonneg (l 1)
  by_contra h
  have hz : Complex.normSq (l 0)+Complex.normSq (l 1)=0 := by
    dsimp [spinorNormSq] at h
    linarith
  have hz0 : l 0=0 := Complex.normSq_eq_zero.mp (by linarith)
  have hz1 : l 1=0 := Complex.normSq_eq_zero.mp (by linarith)
  apply hl
  ext i
  fin_cases i <;> assumption

theorem spinorFrame_det_ne_zero (l : Spinor2) (hl : l≠0) : (spinorFrame l).det≠0 := by
  rw [spinorFrame_det]
  exact_mod_cast ne_of_gt (spinorNormSq_pos l hl)

def reconstruct (l m : Spinor2) : ComplexSpacetime := spinorFrame m * (spinorFrame l)⁻¹

theorem reconstruct_frame (l m : Spinor2) (hl : l≠0) :
    reconstruct l m * spinorFrame l=spinorFrame m := by
  rw [reconstruct, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (spinorFrame_det_ne_zero l hl)), Matrix.mul_one]

theorem reconstruct_incidence (l m : Spinor2) (hl : l≠0) : reconstruct l m *ᵥ l=m := by
  have h := reconstruct_frame l m hl
  ext i
  fin_cases i
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, Fin.sum_univ_two] using
      congrFun (congrFun h 0) 0
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, Fin.sum_univ_two] using
      congrFun (congrFun h 1) 0

theorem reconstruct_hat_incidence (l m : Spinor2) (hl : l≠0) : reconstruct l m *ᵥ hat l=hat m := by
  have h := reconstruct_frame l m hl
  ext i
  fin_cases i
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, hat, Fin.sum_univ_two] using
      congrFun (congrFun h 0) 1
  · simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, hat, Fin.sum_univ_two] using
      congrFun (congrFun h 1) 1

theorem reconstruct_unique (x : ComplexSpacetime) (l m : Spinor2) (hl : l≠0)
    (hi : x *ᵥ l=m) (hh : x *ᵥ hat l=hat m) : x=reconstruct l m := by
  have hf : x * spinorFrame l=spinorFrame m := by
    ext i j
    fin_cases j
    · fin_cases i <;>
        simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, Fin.sum_univ_two] using congrFun hi _
    · fin_cases i
      · calc
          (x * spinorFrame l) 0 1 = (x *ᵥ hat l) 0 := by
            simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, hat,
              Fin.sum_univ_two]
          _ = hat m 0 := congrFun hh 0
          _ = spinorFrame m 0 1 := by rfl
      · calc
          (x * spinorFrame l) 1 1 = (x *ᵥ hat l) 1 := by
            simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, spinorFrame, hat,
              Fin.sum_univ_two]
          _ = hat m 1 := congrFun hh 1
          _ = spinorFrame m 1 1 := by rfl
  calc
    x = x * (spinorFrame l * (spinorFrame l)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (spinorFrame_det_ne_zero l hl)), Matrix.mul_one]
    _ = reconstruct l m := by rw [← Matrix.mul_assoc, hf]; rfl

/-- Reconstruction is invariant under simultaneous nonzero projective rescaling. -/
theorem reconstruct_smul (c : ℂ) (hc : c≠0) (l m : Spinor2) (hl : l≠0) :
    reconstruct (c • l) (c • m)=reconstruct l m := by
  apply Eq.symm
  apply reconstruct_unique _ _ _ (smul_ne_zero hc hl)
  · change omegaLinearMap (reconstruct l m) (c • l)=c • m
    rw [map_smul, omegaLinearMap_apply, reconstruct_incidence l m hl]
  · rw [hat_smul, hat_smul]
    change omegaLinearMap (reconstruct l m) (star c • hat l)=star c • hat m
    rw [map_smul, omegaLinearMap_apply, reconstruct_hat_incidence l m hl]

def translate (t : ComplexSpacetime) (z : Twistor4) : Twistor4 := (z.1,z.2+t *ᵥ z.1)

theorem translate_incidence (t x : ComplexSpacetime) (l : Spinor2) :
    translate t (paperIncidence x l)=paperIncidence (x+t) l := by
  simp [translate, paperIncidence, omegaLinearMap_apply, Matrix.add_mulVec]

theorem translate_comp (s t : ComplexSpacetime) (z : Twistor4) :
    translate s (translate t z)=translate (s+t) z := by
  simp [translate, Matrix.add_mulVec, add_comm, add_left_comm]

end InfoGeometry.Twistor.MeierViana
