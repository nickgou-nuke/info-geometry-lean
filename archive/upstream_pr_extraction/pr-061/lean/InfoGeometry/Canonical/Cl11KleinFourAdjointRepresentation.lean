import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.KleinFourTagRootNormalization

/-!
# The finite adjoint Klein action in the real `Cl(1,1)` matrix atom

The Pauli generators give the split lift. Conjugation is taken in the
associative matrix algebra and is bundled by Mathlib as an `AlgEquiv`.
-/

namespace InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.KleinFourTagRootNormalization

abbrev Mat2 := InfoGeometry.Clifford.Cl11Matrix.Mat2
abbrev V4 := InfoGeometry.Canonical.KleinFourTagRootNormalization.V4

noncomputable def gammaUnit : Mat2ˣ :=
  Units.mkOfMulEqOne Eplus Eplus Eplus_sq

noncomputable def bivectorUnit : Mat2ˣ :=
  Units.mkOfMulEqOne J1 J1 J1_sq

theorem eminus_mul_neg_eminus : Eminus * (-Eminus) = (1 : Mat2) := by
  rw [mul_neg, Eminus_sq]
  simp

noncomputable def causalUnit : Mat2ˣ :=
  Units.mkOfMulEqOne Eminus (-Eminus) eminus_mul_neg_eminus

noncomputable def adjointAlgEquiv (u : Mat2ˣ) : Mat2 ≃ₐ[ℝ] Mat2 :=
  MulSemiringAction.toAlgEquiv ℝ Mat2 (ConjAct.toConjAct u)

theorem adjointAlgEquiv_apply (u : Mat2ˣ) (A : Mat2) :
    adjointAlgEquiv u A = (u : Mat2) * A * (↑(u⁻¹) : Mat2) := by
  rfl

theorem gammaUnit_value : (gammaUnit : Mat2) = Eplus := by rfl
theorem bivectorUnit_value : (bivectorUnit : Mat2) = J1 := by rfl
theorem causalUnit_value : (causalUnit : Mat2) = Eminus := by rfl

theorem gammaUnit_sq : gammaUnit * gammaUnit = (1 : Mat2ˣ) := by
  apply Units.ext
  simp [gammaUnit, Eplus_sq]

theorem bivectorUnit_sq : bivectorUnit * bivectorUnit = (1 : Mat2ˣ) := by
  apply Units.ext
  simp [bivectorUnit, J1_sq]

theorem causalUnit_eq_gamma_mul_bivector :
    causalUnit = gammaUnit * bivectorUnit := by
  apply Units.ext
  change Eminus = Eplus * J1
  rw [← Eplus_mul_Eminus, ← mul_assoc, Eplus_sq]
  simp

theorem adjoint_comp_apply (u v : Mat2ˣ) (A : Mat2) :
    adjointAlgEquiv u (adjointAlgEquiv v A) =
      adjointAlgEquiv (u * v) A := by
  change ConjAct.toConjAct u • (ConjAct.toConjAct v • A) =
    ConjAct.toConjAct (u * v) • A
  rw [smul_smul, ConjAct.toConjAct_mul]

theorem adjoint_one (A : Mat2) :
    adjointAlgEquiv (1 : Mat2ˣ) A = A := by
  simp [adjointAlgEquiv]

theorem gamma_adjoint_square (A : Mat2) :
    adjointAlgEquiv gammaUnit (adjointAlgEquiv gammaUnit A) = A := by
  rw [adjoint_comp_apply]
  rw [show gammaUnit * gammaUnit = 1 by
    apply Units.ext
    simp [gammaUnit, Eplus_sq]]
  exact adjoint_one A

theorem bivector_adjoint_square (A : Mat2) :
    adjointAlgEquiv bivectorUnit (adjointAlgEquiv bivectorUnit A) = A := by
  rw [adjoint_comp_apply]
  rw [show bivectorUnit * bivectorUnit = 1 by
    apply Units.ext
    simp [bivectorUnit, J1_sq]]
  exact adjoint_one A

theorem gamma_bivector_adjoint_commute (A : Mat2) :
    adjointAlgEquiv gammaUnit (adjointAlgEquiv bivectorUnit A) =
      adjointAlgEquiv bivectorUnit (adjointAlgEquiv gammaUnit A) := by
  have hg : (↑(gammaUnit⁻¹) : Mat2) = Eplus := by rfl
  have hb : (↑(bivectorUnit⁻¹) : Mat2) = J1 := by rfl
  simp only [adjointAlgEquiv_apply, gammaUnit_value, bivectorUnit_value,
    hg, hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, J1, Matrix.mul_apply, Matrix.vecMul,
      Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

noncomputable def adjointAlgHom : Mat2ˣ →* (Mat2 ≃ₐ[ℝ] Mat2) :=
  (MulSemiringAction.toAlgAut (ConjAct Mat2ˣ) ℝ Mat2).comp
    (ConjAct.toConjAct (G := Mat2ˣ))

@[simp] theorem adjointAlgHom_apply (u : Mat2ˣ) (A : Mat2) :
    adjointAlgHom u A = adjointAlgEquiv u A := by rfl

theorem causalUnit_sq : causalUnit * causalUnit = (-1 : Mat2ˣ) := by
  apply Units.ext
  simp [causalUnit, Eminus_sq]

theorem adjoint_neg_one (A : Mat2) :
    adjointAlgEquiv (-1 : Mat2ˣ) A = A := by
  change (-1 : Mat2) * A * (-1 : Mat2) = A
  simp

theorem adjoint_neg_unit (u : Mat2ˣ) (A : Mat2) :
    adjointAlgEquiv (-u) A = adjointAlgEquiv u A := by
  change (-u : Mat2) * A * (↑((-u)⁻¹) : Mat2) =
    (u : Mat2) * A * (↑(u⁻¹) : Mat2)
  simp [inv_neg]

theorem causal_adjoint_square (A : Mat2) :
    adjointAlgEquiv causalUnit (adjointAlgEquiv causalUnit A) = A := by
  rw [adjoint_comp_apply, causalUnit_sq]
  exact adjoint_neg_one A

theorem adjointAlgHom_one :
    adjointAlgHom (1 : Mat2ˣ) = (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  apply AlgEquiv.ext
  intro A
  simpa only [adjointAlgHom_apply] using adjoint_one A

theorem adjointAlgHom_neg_one :
    adjointAlgHom (-1 : Mat2ˣ) = (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  apply AlgEquiv.ext
  intro A
  simpa only [adjointAlgHom_apply] using adjoint_neg_one A

theorem adjointAlgHom_neg_unit (u : Mat2ˣ) :
    adjointAlgHom (-u) = adjointAlgHom u := by
  apply AlgEquiv.ext
  intro A
  simpa only [adjointAlgHom_apply] using adjoint_neg_unit u A

theorem adjointAlgHom_gamma_sq :
    adjointAlgHom gammaUnit * adjointAlgHom gammaUnit =
      (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  rw [← adjointAlgHom.map_mul, gammaUnit_sq]
  exact adjointAlgHom_one

theorem adjointAlgHom_bivector_sq :
    adjointAlgHom bivectorUnit * adjointAlgHom bivectorUnit =
      (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  rw [← adjointAlgHom.map_mul, bivectorUnit_sq]
  exact adjointAlgHom_one

theorem adjointAlgHom_causal_sq :
    adjointAlgHom causalUnit * adjointAlgHom causalUnit =
      (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  rw [← adjointAlgHom.map_mul, causalUnit_sq]
  exact adjointAlgHom_neg_one

theorem adjointAlgHom_gamma_bivector :
    adjointAlgHom gammaUnit * adjointAlgHom bivectorUnit =
      adjointAlgHom causalUnit := by
  rw [← adjointAlgHom.map_mul, causalUnit_eq_gamma_mul_bivector]

theorem adjointAlgHom_bivector_gamma :
    adjointAlgHom bivectorUnit * adjointAlgHom gammaUnit =
      adjointAlgHom causalUnit := by
  rw [← adjointAlgHom.map_mul, causalUnit_eq_gamma_mul_bivector]
  apply AlgEquiv.ext
  intro A
  simp only [adjointAlgHom_apply]
  rw [← adjoint_comp_apply, ← adjoint_comp_apply]
  exact (gamma_bivector_adjoint_commute A).symm

theorem gammaUnit_mul_causalUnit :
    gammaUnit * causalUnit = bivectorUnit := by
  apply Units.ext
  change Eplus * Eminus = J1
  exact Eplus_mul_Eminus

theorem bivectorUnit_mul_causalUnit :
    bivectorUnit * causalUnit = -gammaUnit := by
  apply Units.ext
  change J1 * Eminus = -Eplus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

theorem causalUnit_mul_gammaUnit :
    causalUnit * gammaUnit = -bivectorUnit := by
  apply Units.ext
  change Eminus * Eplus = -J1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eminus, Eplus, J1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply]

theorem causalUnit_mul_bivectorUnit :
    causalUnit * bivectorUnit = gammaUnit := by
  apply Units.ext
  change Eminus * J1 = Eplus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eminus, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply]

theorem adjointAlgHom_gamma_causal :
    adjointAlgHom gammaUnit * adjointAlgHom causalUnit =
      adjointAlgHom bivectorUnit := by
  rw [← adjointAlgHom.map_mul, gammaUnit_mul_causalUnit]

theorem adjointAlgHom_bivector_causal :
    adjointAlgHom bivectorUnit * adjointAlgHom causalUnit =
      adjointAlgHom gammaUnit := by
  rw [← adjointAlgHom.map_mul, bivectorUnit_mul_causalUnit,
    adjointAlgHom_neg_unit]

theorem adjointAlgHom_causal_gamma :
    adjointAlgHom causalUnit * adjointAlgHom gammaUnit =
      adjointAlgHom bivectorUnit := by
  rw [← adjointAlgHom.map_mul, causalUnit_mul_gammaUnit,
    adjointAlgHom_neg_unit]

theorem adjointAlgHom_causal_bivector :
    adjointAlgHom causalUnit * adjointAlgHom bivectorUnit =
      adjointAlgHom gammaUnit := by
  rw [← adjointAlgHom.map_mul, causalUnit_mul_bivectorUnit]

open InfoGeometry.Topology.V4RootSystem

noncomputable def rootUnit : V4Group → Mat2ˣ
  | V4Group.I => 1
  | V4Group.W1 => gammaUnit
  | V4Group.W2 => bivectorUnit
  | V4Group.W12 => causalUnit

theorem rootUnit_adjoint_mul (g h : V4Group) :
    adjointAlgHom (rootUnit (g * h)) =
      adjointAlgHom (rootUnit g) * adjointAlgHom (rootUnit h) := by
  change adjointAlgHom (rootUnit (v4_mul g h)) =
    adjointAlgHom (rootUnit g) * adjointAlgHom (rootUnit h)
  have hrefl : (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) = 1 := by
    apply AlgEquiv.ext
    intro A
    rfl
  cases g <;> cases h <;>
    simp [v4_mul, rootUnit, adjointAlgHom_one,
      adjointAlgHom_gamma_sq, adjointAlgHom_bivector_sq,
      adjointAlgHom_causal_sq, adjointAlgHom_gamma_bivector,
      adjointAlgHom_bivector_gamma, gammaUnit_mul_causalUnit,
      bivectorUnit_mul_causalUnit, causalUnit_mul_gammaUnit,
      causalUnit_mul_bivectorUnit, adjointAlgHom_gamma_causal,
      adjointAlgHom_bivector_causal, adjointAlgHom_causal_gamma,
      adjointAlgHom_causal_bivector, adjointAlgHom_neg_unit, hrefl]

noncomputable def localCl11RootMap :
    V4Group →* (Mat2 ≃ₐ[ℝ] Mat2) where
  toFun g := adjointAlgHom (rootUnit g)
  map_one' := by simpa [rootUnit] using adjointAlgHom_one
  map_mul' := rootUnit_adjoint_mul

noncomputable def localCl11Map : V4 →* (Mat2 ≃ₐ[ℝ] Mat2) :=
  localCl11RootMap.comp v4RootHom

@[simp] theorem localCl11Map_apply (g : V4) :
    localCl11Map g = adjointAlgHom (rootUnit (v4RootHom g)) := rfl

end InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
