import InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylSymmetrizedMellin

open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant
open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornCartanRootReflections

abbrev Cartan := InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant.Cartan

/-- Weyl-symmetrized Mellin character kernel -/
def weylMellinOrbitSum (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) : ℂ :=
  weylInvariantMellinKernel c x

theorem weylMellinOrbitSum_apply (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
  weylMellinOrbitSum c x = (G2WeylGroupElements.map (fun w => tracelessCartanMellinCharacter (tracelessCartanMellinDualAction w c) x)).sum := rfl

theorem weylMellinOrbitSum_apply_id (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((LinearMap.id : Cartan →ₗ[ℝ] Cartan) x) = weylMellinOrbitSum c x := rfl

theorem weylMellinOrbitSum_apply_s (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c (s x) = weylMellinOrbitSum c x :=
  weylInvariantMellinKernel_shortReflection_covariant c x

theorem weylMellinOrbitSum_apply_l (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c (l x) = weylMellinOrbitSum c x :=
  weylInvariantMellinKernel_longReflection_covariant c x

theorem weylMellinOrbitSum_apply_sl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((s ∘ₗ l) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_s, weylMellinOrbitSum_apply_l]

theorem weylMellinOrbitSum_apply_ls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((l ∘ₗ s) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_l, weylMellinOrbitSum_apply_s]

theorem weylMellinOrbitSum_apply_sls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((s ∘ₗ l ∘ₗ s) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_s, weylMellinOrbitSum_apply_ls]

theorem weylMellinOrbitSum_apply_lsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((l ∘ₗ s ∘ₗ l) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_l, weylMellinOrbitSum_apply_sl]

theorem weylMellinOrbitSum_apply_slsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((s ∘ₗ l ∘ₗ s ∘ₗ l) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_s, weylMellinOrbitSum_apply_lsl]

theorem weylMellinOrbitSum_apply_lsls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((l ∘ₗ s ∘ₗ l ∘ₗ s) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_l, weylMellinOrbitSum_apply_sls]

theorem weylMellinOrbitSum_apply_slsls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_s, weylMellinOrbitSum_apply_lsls]

theorem weylMellinOrbitSum_apply_lslsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_l, weylMellinOrbitSum_apply_slsl]

theorem weylMellinOrbitSum_apply_slslsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum c ((s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) x) = weylMellinOrbitSum c x := by
  rw [LinearMap.comp_apply, weylMellinOrbitSum_apply_s, weylMellinOrbitSum_apply_lslsl]

def CartanInvariantProp (c : Cartan →ₗ[ℝ] ℂ) (w : Cartan →ₗ[ℝ] Cartan) : Prop :=
  ∀ x, weylMellinOrbitSum c (w x) = weylMellinOrbitSum c x

/-- Invariance under any sequence of generators (the full Weyl orbit) on the Cartan coordinate. -/
theorem weylMellinOrbitSum_cartan_invariant (c : Cartan →ₗ[ℝ] ℂ) (w : Cartan →ₗ[ℝ] Cartan) (hw : w ∈ G2WeylGroupElements) (x : Cartan) :
    weylMellinOrbitSum c (w x) = weylMellinOrbitSum c x := by
  have H : ∀ w' ∈ G2WeylGroupElements, CartanInvariantProp c w' := by
    intro w' hw'
    simp only [G2WeylGroupElements, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | hw'
    · exact weylMellinOrbitSum_apply_id c
    · rcases hw' with rfl | hw'
      · exact weylMellinOrbitSum_apply_s c
      · rcases hw' with rfl | hw'
        · exact weylMellinOrbitSum_apply_l c
        · rcases hw' with rfl | hw'
          · exact weylMellinOrbitSum_apply_sl c
          · rcases hw' with rfl | hw'
            · exact weylMellinOrbitSum_apply_ls c
            · rcases hw' with rfl | hw'
              · exact weylMellinOrbitSum_apply_sls c
              · rcases hw' with rfl | hw'
                · exact weylMellinOrbitSum_apply_lsl c
                · rcases hw' with rfl | hw'
                  · exact weylMellinOrbitSum_apply_slsl c
                  · rcases hw' with rfl | hw'
                    · exact weylMellinOrbitSum_apply_lsls c
                    · rcases hw' with rfl | hw'
                      · exact weylMellinOrbitSum_apply_slsls c
                      · rcases hw' with rfl | rfl
                        · exact weylMellinOrbitSum_apply_lslsl c
                        · exact weylMellinOrbitSum_apply_slslsl c
  exact H w hw x

lemma sum_s_spectral (T_0 T_1 T_2 T_3 T_4 T_5 T_6 T_7 T_8 T_9 T_10 T_11 : ℂ) :
  (T_1 + (T_0 + (T_3 + (T_2 + (T_5 + (T_4 + (T_7 + (T_6 + (T_9 + (T_8 + (T_11 + (T_10 + 0)))))))))))) = (T_0 + (T_1 + (T_2 + (T_3 + (T_4 + (T_5 + (T_6 + (T_7 + (T_8 + (T_9 + (T_10 + (T_11 + 0)))))))))))) := by abel

lemma sum_l_spectral (T_0 T_1 T_2 T_3 T_4 T_5 T_6 T_7 T_8 T_9 T_10 T_11 : ℂ) :
  (T_2 + (T_4 + (T_0 + (T_6 + (T_1 + (T_8 + (T_3 + (T_10 + (T_5 + (T_11 + (T_7 + (T_9 + 0)))))))))))) = (T_0 + (T_1 + (T_2 + (T_3 + (T_4 + (T_5 + (T_6 + (T_7 + (T_8 + (T_9 + (T_10 + (T_11 + 0)))))))))))) := by abel


theorem weylMellinOrbitSum_spectral_id (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (LinearMap.id : Cartan →ₗ[ℝ] Cartan) c) x = weylMellinOrbitSum c x := rfl

theorem weylMellinOrbitSum_spectral_s (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction s c) x = weylMellinOrbitSum c x := by
  dsimp [weylMellinOrbitSum, weylInvariantMellinKernel, G2WeylGroupElements, List.map, List.sum, List.foldl]
  simp only [tracelessCartanMellinDualAction]
  have hs_apply (y : Cartan) : s (s y) = y := by
    have h : (s ∘ₗ s) y = (LinearMap.id : Cartan →ₗ[ℝ] Cartan) y := by rw [shortReflectionOnCartan_sq]
    exact h
  have h0 : (c ∘ₗ s) ∘ₗ ((LinearMap.id : Cartan →ₗ[ℝ] Cartan)) = c ∘ₗ (s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h1 : (c ∘ₗ s) ∘ₗ (s) = c ∘ₗ ((LinearMap.id : Cartan →ₗ[ℝ] Cartan)) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  have h2 : (c ∘ₗ s) ∘ₗ (l) = c ∘ₗ (s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h3 : (c ∘ₗ s) ∘ₗ (s ∘ₗ l) = c ∘ₗ (l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  have h4 : (c ∘ₗ s) ∘ₗ (l ∘ₗ s) = c ∘ₗ (s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h5 : (c ∘ₗ s) ∘ₗ (s ∘ₗ l ∘ₗ s) = c ∘ₗ (l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  have h6 : (c ∘ₗ s) ∘ₗ (l ∘ₗ s ∘ₗ l) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h7 : (c ∘ₗ s) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  have h8 : (c ∘ₗ s) ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h9 : (c ∘ₗ s) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) = c ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  have h10 : (c ∘ₗ s) ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h11 : (c ∘ₗ s) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hs_apply]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact Eq.symm (sum_s_spectral _ _ _ _ _ _ _ _ _ _ _ _)

theorem weylMellinOrbitSum_spectral_l (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction l c) x = weylMellinOrbitSum c x := by
  dsimp [weylMellinOrbitSum, weylInvariantMellinKernel, G2WeylGroupElements, List.map, List.sum, List.foldl]
  simp only [tracelessCartanMellinDualAction]
  have hl_apply (y : Cartan) : l (l y) = y := by
    have h : (l ∘ₗ l) y = (LinearMap.id : Cartan →ₗ[ℝ] Cartan) y := by rw [longReflectionOnCartan_sq]
    exact h
  have hlslsls_apply (y : Cartan) : l (s (l (s (l (s y))))) = s (l (s (l (s (l y))))) :=
    LinearMap.ext_iff.mp lslsls_eq_slslsl y
  have hslslsl_apply (y : Cartan) : s (l (s (l (s (l y))))) = l (s (l (s (l (s y))))) :=
    (LinearMap.ext_iff.mp lslsls_eq_slslsl y).symm
  have h0 : (c ∘ₗ l) ∘ₗ ((LinearMap.id : Cartan →ₗ[ℝ] Cartan)) = c ∘ₗ (l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h1 : (c ∘ₗ l) ∘ₗ (s) = c ∘ₗ (l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h2 : (c ∘ₗ l) ∘ₗ (l) = c ∘ₗ ((LinearMap.id : Cartan →ₗ[ℝ] Cartan)) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hl_apply]
  have h3 : (c ∘ₗ l) ∘ₗ (s ∘ₗ l) = c ∘ₗ (l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h4 : (c ∘ₗ l) ∘ₗ (l ∘ₗ s) = c ∘ₗ (s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hl_apply]
  have h5 : (c ∘ₗ l) ∘ₗ (s ∘ₗ l ∘ₗ s) = c ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h6 : (c ∘ₗ l) ∘ₗ (l ∘ₗ s ∘ₗ l) = c ∘ₗ (s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hl_apply]
  have h7 : (c ∘ₗ l) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply]
  have h8 : (c ∘ₗ l) ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s) = c ∘ₗ (s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hl_apply]
  have h9 : (c ∘ₗ l) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hlslsls_apply]
  have h10 : (c ∘ₗ l) ∘ₗ (l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hl_apply]
  have h11 : (c ∘ₗ l) ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) = c ∘ₗ (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) := by ext y; simp only [LinearMap.comp_apply, LinearMap.id_apply, hslslsl_apply, hl_apply]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact Eq.symm (sum_l_spectral _ _ _ _ _ _ _ _ _ _ _ _)

lemma dualAction_comp (w1 w2 : Cartan →ₗ[ℝ] Cartan) (c : Cartan →ₗ[ℝ] ℂ) :
  tracelessCartanMellinDualAction (w1 ∘ₗ w2) c = tracelessCartanMellinDualAction w2 (tracelessCartanMellinDualAction w1 c) := rfl

theorem weylMellinOrbitSum_spectral_sl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (s ∘ₗ l) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_l, weylMellinOrbitSum_spectral_s]

theorem weylMellinOrbitSum_spectral_ls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (l ∘ₗ s) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_s, weylMellinOrbitSum_spectral_l]

theorem weylMellinOrbitSum_spectral_sls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (s ∘ₗ l ∘ₗ s) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_ls, weylMellinOrbitSum_spectral_s]

theorem weylMellinOrbitSum_spectral_lsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (l ∘ₗ s ∘ₗ l) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_sl, weylMellinOrbitSum_spectral_l]

theorem weylMellinOrbitSum_spectral_slsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (s ∘ₗ l ∘ₗ s ∘ₗ l) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_lsl, weylMellinOrbitSum_spectral_s]

theorem weylMellinOrbitSum_spectral_lsls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (l ∘ₗ s ∘ₗ l ∘ₗ s) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_sls, weylMellinOrbitSum_spectral_l]

theorem weylMellinOrbitSum_spectral_slsls (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_lsls, weylMellinOrbitSum_spectral_s]

theorem weylMellinOrbitSum_spectral_lslsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_slsl, weylMellinOrbitSum_spectral_l]

theorem weylMellinOrbitSum_spectral_slslsl (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction (s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l) c) x = weylMellinOrbitSum c x := by
  rw [dualAction_comp, weylMellinOrbitSum_spectral_lslsl, weylMellinOrbitSum_spectral_s]

def SpectralInvariantProp (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) (w : Cartan →ₗ[ℝ] Cartan) : Prop :=
  weylMellinOrbitSum (tracelessCartanMellinDualAction w c) x = weylMellinOrbitSum c x

/-- Invariance under any sequence of generators (the full Weyl orbit) on the spectral parameter. -/
theorem weylMellinOrbitSum_spectral_orbit_invariant (c : Cartan →ₗ[ℝ] ℂ) (w : Cartan →ₗ[ℝ] Cartan) (hw : w ∈ G2WeylGroupElements) (x : Cartan) :
    weylMellinOrbitSum (tracelessCartanMellinDualAction w c) x = weylMellinOrbitSum c x := by
  have H : ∀ w' ∈ G2WeylGroupElements, SpectralInvariantProp c x w' := by
    intro w' hw'
    simp only [G2WeylGroupElements, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | hw'
    · exact weylMellinOrbitSum_spectral_id c x
    · rcases hw' with rfl | hw'
      · exact weylMellinOrbitSum_spectral_s c x
      · rcases hw' with rfl | hw'
        · exact weylMellinOrbitSum_spectral_l c x
        · rcases hw' with rfl | hw'
          · exact weylMellinOrbitSum_spectral_sl c x
          · rcases hw' with rfl | hw'
            · exact weylMellinOrbitSum_spectral_ls c x
            · rcases hw' with rfl | hw'
              · exact weylMellinOrbitSum_spectral_sls c x
              · rcases hw' with rfl | hw'
                · exact weylMellinOrbitSum_spectral_lsl c x
                · rcases hw' with rfl | hw'
                  · exact weylMellinOrbitSum_spectral_slsl c x
                  · rcases hw' with rfl | hw'
                    · exact weylMellinOrbitSum_spectral_lsls c x
                    · rcases hw' with rfl | hw'
                      · exact weylMellinOrbitSum_spectral_slsls c x
                      · rcases hw' with rfl | rfl
                        · exact weylMellinOrbitSum_spectral_lslsl c x
                        · exact weylMellinOrbitSum_spectral_slslsl c x
  exact H w hw

/-- The Souriau orbit partition function defined directly on the Cartan subalgebra using the dual action. -/
def weylSouriauOrbitPartition (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) : ℂ :=
  (G2WeylGroupElements.map (fun w => tracelessCartanMellinCharacter (tracelessCartanMellinDualAction w c) x)).sum

theorem weylSouriauOrbitPartition_eq_weylMellinOrbitSum (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylSouriauOrbitPartition c x = weylMellinOrbitSum c x := rfl

theorem weylSouriauOrbitPartition_invariant (c : Cartan →ₗ[ℝ] ℂ) (w : Cartan →ₗ[ℝ] Cartan) (hw : w ∈ G2WeylGroupElements) (x : Cartan) :
    weylSouriauOrbitPartition c (w x) = weylSouriauOrbitPartition c x := by
  rw [weylSouriauOrbitPartition_eq_weylMellinOrbitSum, weylSouriauOrbitPartition_eq_weylMellinOrbitSum]
  exact weylMellinOrbitSum_cartan_invariant c w hw x

end InfoGeometry.Lie.CanonicalZornG2CartanWeylSymmetrizedMellin
