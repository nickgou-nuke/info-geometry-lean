import Mathlib
import InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
import InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

set_option autoImplicit false

namespace InfoGeometry.Synthesis.SouriauJordanAttentionBridge

open scoped BigOperators
open InfoGeometry.Synthesis.ParaKahlerSouriauMassieuMajoranaSynthesis
open InfoGeometry.Synthesis.HadjiivanovMonodromyChiralLightconeSynthesis

noncomputable section

variable {m : ℕ}

/-- Every row of the Fisher--Souriau Hessian sums to zero, so constant score
    shifts lie in its gauge kernel. -/
theorem fisherSouriauHessian_row_sum_eq_zero
    [Nonempty (Fin m)] [DecidableEq (Fin m)]
    (s : Fin m → ℝ) (j : Fin m) :
    (∑ k : Fin m, fisherSouriauHessian s j k) = 0 := by
  classical
  have hnorm : ∑ k : Fin m, souriauAttentionWeight s k = 1 :=
    (massieu_free_entropy_legendre_identity s j).1
  unfold fisherSouriauHessian
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← Finset.mul_sum, hnorm]
  ring

/-- The Hessian acts by weighting each score coordinate's deviation from the
    attention-weighted mean. -/
theorem fisherSouriauHessian_mulVec_apply
    [Nonempty (Fin m)] [DecidableEq (Fin m)]
    (s v : Fin m → ℝ) (j : Fin m) :
    Matrix.mulVec (fisherSouriauHessian s) v j =
      souriauAttentionWeight s j * (v j - souriauMomentMap s v) := by
  classical
  change (∑ k : Fin m,
      ((if j = k then souriauAttentionWeight s j else 0) -
        souriauAttentionWeight s j * souriauAttentionWeight s k) * v k) =
    souriauAttentionWeight s j *
      (v j - ∑ k : Fin m, souriauAttentionWeight s k * v k)
  have hsplit :
      (∑ k : Fin m,
        ((if j = k then souriauAttentionWeight s j else 0) -
          souriauAttentionWeight s j * souriauAttentionWeight s k) * v k) =
      (∑ k : Fin m, (if j = k then souriauAttentionWeight s j else 0) * v k) -
        (∑ k : Fin m,
          souriauAttentionWeight s j * souriauAttentionWeight s k * v k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsplit]
  have hdiag :
      (∑ k : Fin m,
        (if j = k then souriauAttentionWeight s j else 0) * v k) =
        souriauAttentionWeight s j * v j := by
    simp
  rw [hdiag]
  have hfactor :
      (∑ k : Fin m,
        souriauAttentionWeight s j * souriauAttentionWeight s k * v k) =
      souriauAttentionWeight s j *
        (∑ k : Fin m, souriauAttentionWeight s k * v k) := by
    calc
      (∑ k : Fin m,
          souriauAttentionWeight s j * souriauAttentionWeight s k * v k) =
        ∑ k : Fin m,
          souriauAttentionWeight s j * (souriauAttentionWeight s k * v k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = souriauAttentionWeight s j *
          (∑ k : Fin m, souriauAttentionWeight s k * v k) := by
            rw [Finset.mul_sum]
  rw [hfactor]
  ring

/-- Edge conductance of the complete attention graph. -/
def attentionEdgeConductance (s : Fin m → ℝ) (i j : Fin m) : ℝ :=
  souriauAttentionWeight s i * souriauAttentionWeight s j

/-- Entry formula for the weighted complete-graph Laplacian, with the
    diagonal written using normalization of the attention weights. -/
def attentionCompleteGraphLaplacianEntry
    (s : Fin m → ℝ) (i j : Fin m) : ℝ :=
  if i = j then
    souriauAttentionWeight s i * (1 - souriauAttentionWeight s i)
  else
    -attentionEdgeConductance s i j

/-- The Fisher--Souriau Hessian is exactly the complete-graph Laplacian whose
    off-diagonal edge conductances are `pᵢ pⱼ`. -/
theorem fisherSouriauHessian_eq_attentionCompleteGraphLaplacianEntry
    [Nonempty (Fin m)] [DecidableEq (Fin m)]
    (s : Fin m → ℝ) (i j : Fin m) :
    fisherSouriauHessian s i j = attentionCompleteGraphLaplacianEntry s i j := by
  by_cases hij : i = j
  · subst j
    simp [fisherSouriauHessian, attentionCompleteGraphLaplacianEntry]
    ring
  · simp [fisherSouriauHessian, attentionCompleteGraphLaplacianEntry,
      attentionEdgeConductance, hij]

/-- The Fisher--Souriau Hessian's operator kernel consists exactly of
    constant score directions, i.e. the projective gauge line. -/
theorem fisherSouriauHessian_kernel_iff_constant
    [Nonempty (Fin m)] [DecidableEq (Fin m)]
    (s v : Fin m → ℝ) :
    Matrix.mulVec (fisherSouriauHessian s) v = 0 ↔
      ∃ c : ℝ, ∀ j : Fin m, v j = c := by
  constructor
  · intro hv
    refine ⟨souriauMomentMap s v, ?_⟩
    intro j
    have hzero :
        souriauAttentionWeight s j *
          (v j - souriauMomentMap s v) = 0 := by
      rw [← fisherSouriauHessian_mulVec_apply s v j]
      exact congrFun hv j
    have hweight : souriauAttentionWeight s j ≠ 0 :=
      ne_of_gt (souriauAttentionWeight_pos s j)
    have hcenter : v j - souriauMomentMap s v = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hweight
    linarith
  · rintro ⟨c, hc⟩
    have hnorm : ∑ j : Fin m, souriauAttentionWeight s j = 1 :=
      (massieu_free_entropy_legendre_identity s (Classical.choice ‹Nonempty (Fin m)›)).1
    have hmean : souriauMomentMap s v = c := by
      unfold souriauMomentMap
      calc
        (∑ j : Fin m, souriauAttentionWeight s j * v j) =
            ∑ j : Fin m, souriauAttentionWeight s j * c := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hc j]
        _ = (∑ j : Fin m, souriauAttentionWeight s j) * c := by
              rw [Finset.sum_mul]
        _ = c := by rw [hnorm]; ring
    ext j
    rw [fisherSouriauHessian_mulVec_apply s v j, hc j, hmean]
    simp

/-- Score transport by a linear nilpotent mode. -/
def linearScoreTransport
    (N : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (a : ℝ)
    (s : Fin m → ℝ) : Fin m → ℝ :=
  s + a • N s

/-- If a nilpotent mode changes the scores by a constant vector, its action is
    exactly a projective gauge shift: attention is unchanged and the potential
    changes by that constant. -/
theorem attention_invariant_of_gauge_score_transport
    [Nonempty (Fin m)]
    (N : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a c : ℝ) (s : Fin m → ℝ)
    (hGauge : ∀ j : Fin m, a * N s j = c) :
    souriauMassieuPotential (linearScoreTransport N a s) =
        souriauMassieuPotential s + c ∧
      ∀ j : Fin m,
        souriauAttentionWeight (linearScoreTransport N a s) j =
          souriauAttentionWeight s j := by
  have hshift : linearScoreTransport N a s = fun j => s j + c := by
    funext j
    simp [linearScoreTransport, hGauge j]
  rw [hshift]
  constructor
  · exact
      (souriauMassieu_shift_and_attention_scale_invariance
        s c (Classical.choice ‹Nonempty (Fin m)›)).1
  · intro j
    exact
      (souriauMassieu_shift_and_attention_scale_invariance s c j).2

/-- The Fisher--Souriau Hessian is unchanged by a nilpotent score transport
    whenever that transport acts at the given score by a constant gauge shift. -/
theorem fisherSouriauHessian_invariant_of_gauge_score_transport
    [Nonempty (Fin m)] [DecidableEq (Fin m)]
    (N : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (a c : ℝ) (s : Fin m → ℝ)
    (hGauge : ∀ j : Fin m, a * N s j = c)
    (j k : Fin m) :
    fisherSouriauHessian (linearScoreTransport N a s) j k =
      fisherSouriauHessian s j k := by
  have hshift : linearScoreTransport N a s = fun i => s i + c := by
    funext i
    simp [linearScoreTransport, hGauge i]
  rw [hshift]
  unfold fisherSouriauHessian
  rw [(souriauMassieu_shift_and_attention_scale_invariance s c j).2,
    (souriauMassieu_shift_and_attention_scale_invariance s c k).2]

/-- A square-zero score mode gives an exact inverse pair of finite transports. -/
theorem nilpotentScoreTransport_inverse
    (N : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hN : ∀ s, N (N s) = 0) (a : ℝ) (s : Fin m → ℝ) :
    linearScoreTransport N (-a)
        (linearScoreTransport N a s) = s := by
  unfold linearScoreTransport
  rw [map_add, map_smul, hN]
  simp only [smul_zero, add_zero]
  module

end

end InfoGeometry.Synthesis.SouriauJordanAttentionBridge
