import proofs.CanonicalSplitOctonionTKK
import proofs.CubicJordanPeirceDecomposition
import proofs.ProjectiveAffineConformalClosure55
import proofs.ZornOPParavector

/-!
# Thesis split-composition algebra family

This file is a thin Lean-facing bundle over the thesis-aligned algebraic spine
already proved elsewhere in the repository.

The point is not to invent new structure. The point is to expose the existing
lemmas as a named chain:

1. split-Clifford / Cayley-Dickson style split algebra core;
2. Zorn matrix identities;
3. D-projective null-cone embedding;
4. Peirce / Albert decomposition skeleton.
-/

noncomputable section

namespace ThesisSplitCompositionAlgebraFamily

open InfoGeometry.Canonical.SplitOctonionTKK

/-- Split-Clifford / Cayley-Dickson style algebra core. -/
theorem splitClifford_core_thm :
    SplitClifford.ePos * SplitClifford.ePos = (1 : SplitClifford.Cl11) ∧
    SplitClifford.eNeg * SplitClifford.eNeg = (-1 : SplitClifford.Cl11) ∧
    SplitClifford.ePos * SplitClifford.eNeg =
      -(SplitClifford.eNeg * SplitClifford.ePos) ∧
    SplitClifford.jordanR SplitClifford.ePos SplitClifford.eNeg +
      SplitClifford.lieR SplitClifford.ePos SplitClifford.eNeg =
        SplitClifford.ePos * SplitClifford.eNeg := by
  exact InfoGeometry.Canonical.SplitOctonionTKK.splitClifford_core

/-- Zorn matrix identities bundled explicitly. -/
theorem zornOpParavector_core_thm :
    ZornOPParavector.Eplus * ZornOPParavector.Eplus = ZornOPParavector.Eplus ∧
    ZornOPParavector.Eminus * ZornOPParavector.Eminus = ZornOPParavector.Eminus ∧
    ZornOPParavector.CubicProjector ZornOPParavector.Eplus ∧
    ZornOPParavector.CubicProjector ZornOPParavector.Eminus ∧
    ZornOPParavector.zornDet ZornOPParavector.Eplus = 0 ∧
    ZornOPParavector.zornDet ZornOPParavector.Eminus = 0 ∧
    (∀ u : Fin 3 → ℂ, ZornOPParavector.SquareZero (ZornOPParavector.Nup u)) ∧
    (∀ v : Fin 3 → ℂ, ZornOPParavector.SquareZero (ZornOPParavector.Ndown v)) ∧
    (∀ u : Fin 3 → ℂ, ZornOPParavector.zornDet (ZornOPParavector.Nup u) = 0) ∧
    (∀ v : Fin 3 → ℂ, ZornOPParavector.zornDet (ZornOPParavector.Ndown v) = 0) ∧
    (∀ u v : Fin 3 → ℂ, ZornOPParavector.Nup u * ZornOPParavector.Ndown v =
      ⟨ZornOPParavector.dot3 u v, 0, 0, 0⟩) ∧
    (∀ u v : Fin 3 → ℂ, ZornOPParavector.Ndown v * ZornOPParavector.Nup u =
      ⟨0, 0, 0, ZornOPParavector.dot3 v u⟩) := by
  exact ZornOPParavector.zorn_op_paravector_synthesis

/-- D-projective null-cone embedding and its reflection invariance. -/
theorem projectiveNullCone_core_thm :
    ∀ (x : ProjectiveAffineConformalClosure55.PACSplit44)
      (X : ProjectiveAffineConformalClosure55.PACSplit55),
      ProjectiveAffineConformalClosure55.Q55 X = 0 →
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.conformalEmbed44to55 x) = 0 ∧
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.reflectU X) = 0 ∧
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.reflectV X) = 0 ∧
      (∀ s : ℂ, ProjectiveAffineConformalClosure55.spectralCPT s = s ↔ s.re = 1 / 2) := by
  intro x X hX
  exact ProjectiveAffineConformalClosure55.projective_affine_conformal_closure_55_synthesis
    x X hX

/-- Peirce / Albert decomposition skeleton. -/
theorem peirceAlbert_core_thm :
    ∀ {A : Type*} [Ring A] (E1 E2 E3 : A),
      CubicJordanPeirceDecomposition.PeirceIdempotents E1 E2 E3 →
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
          CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
            CubicJordanPeirceDecomposition.Pcanonical E1 E2 =
        CubicJordanPeirceDecomposition.Pcanonical E1 E2 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E1 = E1 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E2 = -E2 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E3 = 0 := by
  intro A _ E1 E2 E3 h
  exact tripotent_peirce_core E1 E2 E3 h

/-- The thesis family synthesized as a record of explicit lemmas. -/
structure ThesisSplitCompositionAlgebraFamilyCore where
  splitCliffordCoreProof :
    SplitClifford.ePos * SplitClifford.ePos = (1 : SplitClifford.Cl11) ∧
    SplitClifford.eNeg * SplitClifford.eNeg = (-1 : SplitClifford.Cl11) ∧
    SplitClifford.ePos * SplitClifford.eNeg =
      -(SplitClifford.eNeg * SplitClifford.ePos) ∧
    SplitClifford.jordanR SplitClifford.ePos SplitClifford.eNeg +
      SplitClifford.lieR SplitClifford.ePos SplitClifford.eNeg =
        SplitClifford.ePos * SplitClifford.eNeg
  zornOpParavectorCoreProof :
    ZornOPParavector.Eplus * ZornOPParavector.Eplus = ZornOPParavector.Eplus ∧
    ZornOPParavector.Eminus * ZornOPParavector.Eminus = ZornOPParavector.Eminus ∧
    ZornOPParavector.CubicProjector ZornOPParavector.Eplus ∧
    ZornOPParavector.CubicProjector ZornOPParavector.Eminus ∧
    ZornOPParavector.zornDet ZornOPParavector.Eplus = 0 ∧
    ZornOPParavector.zornDet ZornOPParavector.Eminus = 0 ∧
    (∀ u : Fin 3 → ℂ, ZornOPParavector.SquareZero (ZornOPParavector.Nup u)) ∧
    (∀ v : Fin 3 → ℂ, ZornOPParavector.SquareZero (ZornOPParavector.Ndown v)) ∧
    (∀ u : Fin 3 → ℂ, ZornOPParavector.zornDet (ZornOPParavector.Nup u) = 0) ∧
    (∀ v : Fin 3 → ℂ, ZornOPParavector.zornDet (ZornOPParavector.Ndown v) = 0) ∧
    (∀ u v : Fin 3 → ℂ, ZornOPParavector.Nup u * ZornOPParavector.Ndown v =
      ⟨ZornOPParavector.dot3 u v, 0, 0, 0⟩) ∧
    (∀ u v : Fin 3 → ℂ, ZornOPParavector.Ndown v * ZornOPParavector.Nup u =
      ⟨0, 0, 0, ZornOPParavector.dot3 v u⟩)
  projectiveNullConeCoreProof :
    ∀ (x : ProjectiveAffineConformalClosure55.PACSplit44)
      (X : ProjectiveAffineConformalClosure55.PACSplit55),
      ProjectiveAffineConformalClosure55.Q55 X = 0 →
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.conformalEmbed44to55 x) = 0 ∧
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.reflectU X) = 0 ∧
      ProjectiveAffineConformalClosure55.Q55
          (ProjectiveAffineConformalClosure55.reflectV X) = 0 ∧
      (∀ s : ℂ, ProjectiveAffineConformalClosure55.spectralCPT s = s ↔ s.re = 1 / 2)
  peirceAlbertCoreProof :
    ∀ {A : Type*} [Ring A] (E1 E2 E3 : A),
      CubicJordanPeirceDecomposition.PeirceIdempotents E1 E2 E3 →
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
          CubicJordanPeirceDecomposition.Pcanonical E1 E2 *
            CubicJordanPeirceDecomposition.Pcanonical E1 E2 =
        CubicJordanPeirceDecomposition.Pcanonical E1 E2 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E1 = E1 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E2 = -E2 ∧
      CubicJordanPeirceDecomposition.Pcanonical E1 E2 * E3 = 0

/-- The thesis family instantiated from the explicit lemma chain. -/
def thesisSplitCompositionAlgebraFamilyCore : ThesisSplitCompositionAlgebraFamilyCore := by
  refine
    { splitCliffordCoreProof := splitClifford_core_thm
      zornOpParavectorCoreProof := zornOpParavector_core_thm
      projectiveNullConeCoreProof := projectiveNullCone_core_thm
      peirceAlbertCoreProof := peirceAlbert_core_thm }

end ThesisSplitCompositionAlgebraFamily
