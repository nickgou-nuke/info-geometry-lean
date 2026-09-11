import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralExterior3HodgeDiracBlocks
import InfoGeometry.Canonical.RealKreinChiralHodgeDiracBlocks

/-!
# Four-grade DAG carrier and exterior-algebra comparison

`DAG.TwoComplex` has only degrees `0, 1, 2`.  The split-octonion Peirce
carrier used by the Hestenes/exterior realization has degrees
`0, 1, 2, 3`, of dimensions `1 + 3 + 3 + 1`.  This owner closes only the
finite-dimensional carrier comparison.  It does not invent a degree-three
boundary map or claim a DAG chain-complex intertwiner.
-/

noncomputable section

namespace InfoGeometry.Canonical.DAGThreeGradeExteriorCarrierBridge

abbrev ThreeGradeCell (n0 n1 n2 n3 : ℕ) :=
  Fin n0 ⊕ Fin n1 ⊕ Fin n2 ⊕ Fin n3

abbrev ThreeGradeCellSpace (n0 n1 n2 n3 : ℕ) :=
  ThreeGradeCell n0 n1 n2 n3 → ℝ

theorem threeGradeCell_card (n0 n1 n2 n3 : ℕ) :
    Fintype.card (ThreeGradeCell n0 n1 n2 n3) = n0 + n1 + n2 + n3 := by
  simp [ThreeGradeCell, Nat.add_left_comm, Nat.add_comm]

abbrev ChiralThreeGradeCell := ThreeGradeCell 1 3 3 1

abbrev ChiralThreeGradeCellSpace := ThreeGradeCellSpace 1 3 3 1

theorem chiralThreeGradeCell_card :
    Fintype.card ChiralThreeGradeCell = 8 := by
  simp [ChiralThreeGradeCell]

theorem chiralThreeGradeCellSpace_finrank :
    Module.finrank ℝ ChiralThreeGradeCellSpace = 8 := by
  simp [ChiralThreeGradeCellSpace]

theorem finEightFunctionSpace_finrank :
    Module.finrank ℝ (Fin 8 → ℝ) = 8 := by
  simp

noncomputable def chiralThreeGradeToFinEight :
    ChiralThreeGradeCellSpace ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  LinearEquiv.ofFinrankEq ChiralThreeGradeCellSpace (Fin 8 → ℝ)
    (chiralThreeGradeCellSpace_finrank.trans finEightFunctionSpace_finrank.symm)

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

noncomputable def chiralThreeGradeToExterior3 :
  ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3 :=
  chiralThreeGradeToFinEight.trans
    exterior3SplitOctonionCoordinateEquiv.symm

theorem chiralThreeGradeToExterior3_finrank :
    Module.finrank ℝ ChiralThreeGradeCellSpace =
      Module.finrank ℝ Exterior3 := by
  exact chiralThreeGradeToExterior3.finrank_eq

/-- Transport an endomorphism across the finite carrier equivalence. -/
noncomputable def transportEnd
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (T : Module.End ℝ ChiralThreeGradeCellSpace) : Module.End ℝ Exterior3 :=
  e.toLinearMap.comp (T.comp e.symm.toLinearMap)

theorem transportEnd_apply
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (T : Module.End ℝ ChiralThreeGradeCellSpace) (x : Exterior3) :
    transportEnd e T x = e (T (e.symm x)) := by
  rfl

theorem transportEnd_mul
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (S T : Module.End ℝ ChiralThreeGradeCellSpace) :
    transportEnd e (S * T) = transportEnd e S * transportEnd e T := by
  ext x
  simp [transportEnd, Module.End.mul_apply, LinearMap.comp_apply]

/-! ## Hodge--Dirac transport to the four-grade carrier -/

noncomputable def carrierEnd
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (T : Module.End ℝ Exterior3) : Module.End ℝ ChiralThreeGradeCellSpace :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

theorem carrierEnd_apply
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (T : Module.End ℝ Exterior3) (x : ChiralThreeGradeCellSpace) :
    carrierEnd e T x = e.symm (T (e x)) := by
  rfl

theorem carrierEnd_transport
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (T : Module.End ℝ Exterior3) :
    transportEnd e (carrierEnd e T) = T := by
  ext x
  simp [transportEnd, carrierEnd, LinearMap.comp_apply]

theorem carrierEnd_mul
    (e : ChiralThreeGradeCellSpace ≃ₗ[ℝ] Exterior3)
    (S T : Module.End ℝ Exterior3) :
    carrierEnd e (S * T) = carrierEnd e S * carrierEnd e T := by
  ext x
  simp [carrierEnd, Module.End.mul_apply, LinearMap.comp_apply]

noncomputable def chiralThreeGradeHodgeDirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    Module.End ℝ ChiralThreeGradeCellSpace :=
  carrierEnd chiralThreeGradeToExterior3 (exteriorHodgeDirac3 v φ)

noncomputable def chiralThreeGradeHodgeLaplacian
    (v : V3) (φ : Module.Dual ℝ V3) :
    Module.End ℝ ChiralThreeGradeCellSpace :=
  carrierEnd chiralThreeGradeToExterior3 (exteriorHodgeLaplacian3 v φ)

noncomputable def chiralThreeGradeChirality :
    Module.End ℝ ChiralThreeGradeCellSpace :=
  carrierEnd chiralThreeGradeToExterior3 exteriorGrade3.toLinearMap

theorem chiralThreeGradeChirality_sq :
    chiralThreeGradeChirality * chiralThreeGradeChirality = 1 := by
  apply LinearMap.ext
  intro ψ
  simp [chiralThreeGradeChirality, carrierEnd, Module.End.mul_apply,
    LinearMap.comp_apply, exteriorGrade3_involutive]

theorem chiralThreeGradeHodgeDirac_odd
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralThreeGradeChirality * chiralThreeGradeHodgeDirac v φ =
      -(chiralThreeGradeHodgeDirac v φ * chiralThreeGradeChirality) := by
  apply LinearMap.ext
  intro ψ
  simp only [chiralThreeGradeChirality, chiralThreeGradeHodgeDirac,
    carrierEnd, Module.End.mul_apply, LinearMap.comp_apply,
    LinearMap.neg_apply]
  simp
  change chiralThreeGradeToExterior3.symm
      (exteriorGrade3
        (exteriorHodgeDirac3 v φ (chiralThreeGradeToExterior3 ψ))) =
    -(chiralThreeGradeToExterior3.symm
      (exteriorHodgeDirac3 v φ
        (exteriorGrade3 (chiralThreeGradeToExterior3 ψ))))
  have h := congrArg chiralThreeGradeToExterior3.symm
    (exteriorHodgeDirac3_odd v φ (chiralThreeGradeToExterior3 ψ))
  simpa using h

theorem chiralThreeGradeHodgeDirac_sq
    (v : V3) (φ : Module.Dual ℝ V3) :
    chiralThreeGradeHodgeDirac v φ * chiralThreeGradeHodgeDirac v φ =
      chiralThreeGradeHodgeLaplacian v φ := by
  simp only [chiralThreeGradeHodgeDirac, chiralThreeGradeHodgeLaplacian]
  rw [← carrierEnd_mul]
  exact congrArg (carrierEnd chiralThreeGradeToExterior3)
    (exteriorHodgeDirac3_sq v φ)

/-! ## Hestenes doubling on the transported finite carrier -/

abbrev DoubledChiralThreeGradeCellSpace :=
  ChiralThreeGradeCellSpace × ChiralThreeGradeCellSpace

abbrev DoubledChiralThreeGradeEnd :=
  Module.End ℝ DoubledChiralThreeGradeCellSpace

def doubledChiralDiagonal (T : Module.End ℝ ChiralThreeGradeCellSpace) :
    DoubledChiralThreeGradeEnd :=
  T.prodMap T

def doubledChiralHodgeDirac (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledChiralThreeGradeEnd :=
  doubledChiralDiagonal (chiralThreeGradeHodgeDirac v φ)

def doubledChiralHodgeLaplacian (v : V3) (φ : Module.Dual ℝ V3) :
    DoubledChiralThreeGradeEnd :=
  doubledChiralDiagonal (chiralThreeGradeHodgeLaplacian v φ)

def doubledChiralChirality : DoubledChiralThreeGradeEnd :=
  doubledChiralDiagonal chiralThreeGradeChirality

def doubledChiralHestenesPhase : DoubledChiralThreeGradeEnd where
  toFun x := (-x.2, x.1)
  map_add' x y := by
    ext <;> simp [add_comm]
  map_smul' c x := by
    ext <;> simp

theorem doubledChiralHestenesPhase_sq :
    doubledChiralHestenesPhase * doubledChiralHestenesPhase = -1 := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [doubledChiralHestenesPhase]

theorem doubledChiralHodgeDirac_sq
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledChiralHodgeDirac v φ * doubledChiralHodgeDirac v φ =
      doubledChiralHodgeLaplacian v φ := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  apply Prod.ext
  · simpa [doubledChiralHodgeDirac, doubledChiralHodgeLaplacian,
      doubledChiralDiagonal] using
      congrArg (fun T : Module.End ℝ ChiralThreeGradeCellSpace => T a)
        (chiralThreeGradeHodgeDirac_sq v φ)
  · simpa [doubledChiralHodgeDirac, doubledChiralHodgeLaplacian,
      doubledChiralDiagonal] using
      congrArg (fun T : Module.End ℝ ChiralThreeGradeCellSpace => T b)
        (chiralThreeGradeHodgeDirac_sq v φ)

theorem doubledChiralHestenesPhase_dirac_commutes
    (v : V3) (φ : Module.Dual ℝ V3) :
    doubledChiralHestenesPhase * doubledChiralHodgeDirac v φ =
      doubledChiralHodgeDirac v φ * doubledChiralHestenesPhase := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [doubledChiralHestenesPhase, doubledChiralHodgeDirac,
    doubledChiralDiagonal]

theorem doubledChiralHestenesPhase_chirality_commutes :
    doubledChiralHestenesPhase * doubledChiralChirality =
      doubledChiralChirality * doubledChiralHestenesPhase := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp [doubledChiralHestenesPhase, doubledChiralChirality,
    doubledChiralDiagonal]

theorem doubledChiralHestenesPhase_dirac_sq
    (v : V3) (φ : Module.Dual ℝ V3) :
    (doubledChiralHestenesPhase * doubledChiralHodgeDirac v φ) *
        (doubledChiralHestenesPhase * doubledChiralHodgeDirac v φ) =
      -(doubledChiralHodgeLaplacian v φ) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp only [Module.End.mul_apply, LinearMap.neg_apply]
  simp only [doubledChiralHestenesPhase, doubledChiralHodgeDirac,
    doubledChiralHodgeLaplacian, doubledChiralDiagonal,
    LinearMap.prodMap_apply, Prod.neg_mk]
  have ha := congrArg (fun T : Module.End ℝ ChiralThreeGradeCellSpace => T a)
    (chiralThreeGradeHodgeDirac_sq v φ)
  have hb := congrArg (fun T : Module.End ℝ ChiralThreeGradeCellSpace => T b)
    (chiralThreeGradeHodgeDirac_sq v φ)
  exact Prod.ext (by simpa using ha) (by simpa using hb)

end InfoGeometry.Canonical.DAGThreeGradeExteriorCarrierBridge
