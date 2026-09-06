import InfoGeometry.Canonical.ChiralLorentzianSector

namespace InfoGeometry.Canonical

def tomitaConjugation (x : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion :=
  fun r => if r = .il ∨ r = .jl ∨ r = .kl then -x r else x r

/-! The coordinate involution as a native Mathlib linear endomorphism. -/

def tomitaConjugationLinear :
    StandardIntegralSplitOctonion →ₗ[ℤ] StandardIntegralSplitOctonion :=
  { toFun := tomitaConjugation
    map_add' := by
      intro x y
      funext r
      dsimp [tomitaConjugation]
      split_ifs <;> simp [add_comm]
    map_smul' := by
      intro a x
      funext r
      dsimp [tomitaConjugation]
      split_ifs <;> simp }

theorem tomita_conjugation_involutive (x : StandardIntegralSplitOctonion) :
    tomitaConjugation (tomitaConjugation x) = x := by
  funext r
  dsimp [tomitaConjugation]
  split_ifs <;> ring

theorem tomita_conjugation_linear_involutive :
    tomitaConjugationLinear.comp tomitaConjugationLinear =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact tomita_conjugation_involutive x

theorem tomita_cpt_flips_chiral_null_rays
    (iElem liElem : StandardIntegralSplitOctonion)
    (hI : ∀ r, tomitaConjugation iElem r = iElem r)
    (hLI : ∀ r, tomitaConjugation liElem r = -liElem r) :
    tomitaConjugation (nullRayPlus iElem liElem) =
      nullRayMinus iElem liElem := by
  have hAdd : ∀ a b : StandardIntegralSplitOctonion,
      tomitaConjugation (fun r => a r + b r) =
        fun r => tomitaConjugation a r + tomitaConjugation b r := by
    intro a b
    funext r
    dsimp [tomitaConjugation]
    split_ifs <;> ring
  rw [show nullRayPlus iElem liElem = (fun r => iElem r + liElem r) by rfl]
  rw [hAdd iElem liElem]
  funext r
  rw [hI r, hLI r]
  simp [nullRayMinus, sub_eq_add_neg]

def modularHamiltonianFlow (lAxis x : StandardIntegralSplitOctonion) :
    StandardIntegralSplitOctonion :=
  splitOctonionMul lAxis x

theorem tri_color_shared_modular_flow
    (lAxis : StandardIntegralSplitOctonion)
    (rPlane gPlane bPlane : StandardIntegralSplitOctonion →
      StandardIntegralSplitOctonion)
    (hR : ∀ x, modularHamiltonianFlow lAxis (rPlane x) =
      rPlane (modularHamiltonianFlow lAxis x))
    (hG : ∀ x, modularHamiltonianFlow lAxis (gPlane x) =
      gPlane (modularHamiltonianFlow lAxis x))
    (hB : ∀ x, modularHamiltonianFlow lAxis (bPlane x) =
      bPlane (modularHamiltonianFlow lAxis x)) :
    (∀ x, modularHamiltonianFlow lAxis (rPlane x) =
      rPlane (modularHamiltonianFlow lAxis x)) ∧
    (∀ x, modularHamiltonianFlow lAxis (gPlane x) =
      gPlane (modularHamiltonianFlow lAxis x)) ∧
    (∀ x, modularHamiltonianFlow lAxis (bPlane x) =
      bPlane (modularHamiltonianFlow lAxis x)) :=
  ⟨hR, hG, hB⟩

end InfoGeometry.Canonical
