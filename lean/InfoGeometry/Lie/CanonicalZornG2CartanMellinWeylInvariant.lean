import InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant

open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie.CanonicalZornCartanRootReflections
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

abbrev Cartan := TracelessWeight

abbrev s : Cartan →ₗ[ℝ] Cartan := shortReflectionOnCartan
abbrev l : Cartan →ₗ[ℝ] Cartan := longReflectionOnCartan

abbrev cartanMellinCharacter := tracelessCartanMellinCharacter
abbrev cartanMellinDualAction := tracelessCartanMellinDualAction

def G2WeylGroupElements : List (Cartan →ₗ[ℝ] Cartan) :=
  [ LinearMap.id,
    s,
    l,
    s ∘ₗ l,
    l ∘ₗ s,
    s ∘ₗ l ∘ₗ s,
    l ∘ₗ s ∘ₗ l,
    s ∘ₗ l ∘ₗ s ∘ₗ l,
    l ∘ₗ s ∘ₗ l ∘ₗ s,
    s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s,
    l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l,
    s ∘ₗ l ∘ₗ s ∘ₗ l ∘ₗ s ∘ₗ l ]

def weylInvariantMellinKernel (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) : ℂ :=
  (G2WeylGroupElements.map (fun w => cartanMellinCharacter (cartanMellinDualAction w c) x)).sum

lemma sum_s (T_id T_s T_l T_sl T_ls T_sls T_lsl T_slsl T_lsls T_slsls T_lslsl T_slslsl : ℂ) :
  (T_id + (T_s + (T_l + (T_sl + (T_ls + (T_sls + (T_lsl + (T_slsl + (T_lsls + (T_slsls + (T_lslsl + (T_slslsl + 0)))))))))))) = (T_s + (T_id + (T_ls + (T_sls + (T_l + (T_sl + (T_lsls + (T_slsls + (T_lsl + (T_slsl + (T_slslsl + (T_lslsl + 0)))))))))))) := by abel

lemma sum_l (T_id T_s T_l T_sl T_ls T_sls T_lsl T_slsl T_lsls T_slsls T_lslsl T_slslsl : ℂ) :
  (T_id + (T_s + (T_l + (T_sl + (T_ls + (T_sls + (T_lsl + (T_slsl + (T_lsls + (T_slsls + (T_lslsl + (T_slslsl + 0)))))))))))) = (T_l + (T_sl + (T_id + (T_s + (T_lsl + (T_slsl + (T_ls + (T_sls + (T_lslsl + (T_slslsl + (T_lsls + (T_slsls + 0)))))))))))) := by abel

lemma lslsls_eq_slslsl :
  l ∘ₗ (s ∘ₗ (l ∘ₗ (s ∘ₗ (l ∘ₗ s)))) = s ∘ₗ (l ∘ₗ (s ∘ₗ (l ∘ₗ (s ∘ₗ l)))) := by
  apply LinearMap.ext
  intro x
  exact (LinearMap.ext_iff.mp nativeCartanReflectionsOnCartan_braid x).symm


theorem weylInvariantMellinKernel_shortReflection_covariant (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylInvariantMellinKernel c (s x) = weylInvariantMellinKernel c x := by
  dsimp [weylInvariantMellinKernel, G2WeylGroupElements, List.map, List.sum, List.foldl]
  simp only [tracelessCartanMellinCharacter_covariant, cartanMellinDualAction, tracelessCartanMellinDualAction]
  have hs : s ∘ₗ s = LinearMap.id := shortReflectionOnCartan_sq
  have hl : l ∘ₗ l = LinearMap.id := longReflectionOnCartan_sq
  have hs_comp : ∀ f : Cartan →ₗ[ℝ] ℂ, f ∘ₗ (s ∘ₗ s) = f := fun f => by rw [hs, LinearMap.comp_id]
  have hl_comp : ∀ f : Cartan →ₗ[ℝ] ℂ, f ∘ₗ (l ∘ₗ l) = f := fun f => by rw [hl, LinearMap.comp_id]
  have hs_comp2 : ∀ f : Cartan →ₗ[ℝ] Cartan, s ∘ₗ (s ∘ₗ f) = f := fun f => by rw [←LinearMap.comp_assoc, hs, LinearMap.id_comp]
  have hl_comp2 : ∀ f : Cartan →ₗ[ℝ] Cartan, l ∘ₗ (l ∘ₗ f) = f := fun f => by rw [←LinearMap.comp_assoc, hl, LinearMap.id_comp]
  simp only [LinearMap.comp_assoc]
  simp only [hs, hl, hs_comp, hl_comp, hs_comp2, hl_comp2, LinearMap.comp_id, LinearMap.id_comp, lslsls_eq_slslsl]
  exact (sum_s _ _ _ _ _ _ _ _ _ _ _ _).symm

theorem weylInvariantMellinKernel_longReflection_covariant (c : Cartan →ₗ[ℝ] ℂ) (x : Cartan) :
    weylInvariantMellinKernel c (l x) = weylInvariantMellinKernel c x := by
  dsimp [weylInvariantMellinKernel, G2WeylGroupElements, List.map, List.sum, List.foldl]
  simp only [tracelessCartanMellinCharacter_covariant, cartanMellinDualAction, tracelessCartanMellinDualAction]
  have hs : s ∘ₗ s = LinearMap.id := shortReflectionOnCartan_sq
  have hl : l ∘ₗ l = LinearMap.id := longReflectionOnCartan_sq
  have hs_comp : ∀ f : Cartan →ₗ[ℝ] ℂ, f ∘ₗ (s ∘ₗ s) = f := fun f => by rw [hs, LinearMap.comp_id]
  have hl_comp : ∀ f : Cartan →ₗ[ℝ] ℂ, f ∘ₗ (l ∘ₗ l) = f := fun f => by rw [hl, LinearMap.comp_id]
  have hs_comp2 : ∀ f : Cartan →ₗ[ℝ] Cartan, s ∘ₗ (s ∘ₗ f) = f := fun f => by rw [←LinearMap.comp_assoc, hs, LinearMap.id_comp]
  have hl_comp2 : ∀ f : Cartan →ₗ[ℝ] Cartan, l ∘ₗ (l ∘ₗ f) = f := fun f => by rw [←LinearMap.comp_assoc, hl, LinearMap.id_comp]
  simp only [LinearMap.comp_assoc]
  simp only [hs, hl, hs_comp, hl_comp, hs_comp2, hl_comp2, LinearMap.comp_id, LinearMap.id_comp]
  exact (sum_l _ _ _ _ _ _ _ _ _ _ _ _).symm

end InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylInvariant
