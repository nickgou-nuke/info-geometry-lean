import Mathlib.LinearAlgebra.Dual.Basis
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv

namespace InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

noncomputable section

abbrev V5 := SplitClifford55ExteriorSpinor.V5
abbrev NeutralSpace := SplitClifford55ExteriorSpinor.NeutralSpace
abbrev V55 := Clifford55.V55

noncomputable def dualToV5 : Module.Dual ℝ V5 ≃ₗ[ℝ] V5 :=
  (Pi.basisFun ℝ (Fin 5)).toDualEquiv.symm

noncomputable def neutralToV55 : NeutralSpace ≃ₗ[ℝ] V55 where
  toFun x :=
    ((x.1 + dualToV5 x.2) / 2,
      (x.1 - dualToV5 x.2) / 2)
  invFun y :=
    (y.1 + y.2,
      dualToV5.symm (y.1 - y.2))
  left_inv := by
    intro x
    rcases x with ⟨v, φ⟩
    change
      ((v + dualToV5 φ) / 2 + (v - dualToV5 φ) / 2,
        dualToV5.symm ((v + dualToV5 φ) / 2 -
          (v - dualToV5 φ) / 2)) = (v, φ)
    apply Prod.ext
    · funext i
      change ((v i + dualToV5 φ i) / 2 +
        (v i - dualToV5 φ i) / 2) = v i
      ring
    · apply dualToV5.injective
      rw [show (v + dualToV5 φ) / 2 - (v - dualToV5 φ) / 2 =
        dualToV5 φ by
        funext i
        change ((v i + dualToV5 φ i) / 2 -
          (v i - dualToV5 φ i) / 2) = dualToV5 φ i
        ring]
      simp
  right_inv := by
    intro y
    rcases y with ⟨a, b⟩
    change
      ((a + b + dualToV5 (dualToV5.symm (a - b))) / 2,
        (a + b - dualToV5 (dualToV5.symm (a - b))) / 2) = (a, b)
    rw [dualToV5.apply_symm_apply]
    apply Prod.ext <;> funext i
    · dsimp
      change ((a i + b i + (a i - b i)) / 2) = a i
      ring
    · dsimp
      change ((a i + b i - (a i - b i)) / 2) = b i
      ring
  map_add' := by
    intro x y
    rcases x with ⟨v, φ⟩
    rcases y with ⟨u, ψ⟩
    apply Prod.ext <;> funext i
    · dsimp
      rw [dualToV5.map_add]
      simp only [Pi.add_apply]
      ring
    · dsimp
      rw [dualToV5.map_add]
      simp only [Pi.add_apply]
      ring
  map_smul' := by
    intro c x
    rcases x with ⟨v, φ⟩
    apply Prod.ext <;> funext i
    · dsimp
      rw [dualToV5.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · dsimp
      rw [dualToV5.map_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem dualToV5_apply_coord (φ : Module.Dual ℝ V5) (i : Fin 5) :
    dualToV5 φ i = φ (Pi.single i 1) := by
  simpa [dualToV5] using
    (Module.Basis.coord_toDualEquiv_symm_apply
      (Pi.basisFun ℝ (Fin 5)) i φ)

theorem dualToV5_apply_mul_sum (v : V5) (φ : Module.Dual ℝ V5) :
    (∑ i : Fin 5, v i * dualToV5 φ i) = φ v := by
  classical
  calc
    (∑ i : Fin 5, v i * dualToV5 φ i) =
        ∑ i : Fin 5, v i * φ (Pi.single i 1) := by
          congr 1
          funext i
          rw [dualToV5_apply_coord]
    _ = φ (∑ i : Fin 5, v i • Pi.single i 1) := by
          rw [map_sum]
          simp [smul_eq_mul, mul_comm, Pi.single_apply]
    _ = φ v := by
          congr 1
          funext i
          simp [Pi.single_apply]

theorem q55_neutralToV55 (x : NeutralSpace) :
    Clifford55.Q55 (neutralToV55 x) =
      canonicalNeutralFormUnscaled (E := V5) x := by
  rcases x with ⟨v, φ⟩
  rw [Clifford55.Q55_apply,
    canonicalNeutralFormUnscaled_apply]
  have h := dualToV5_apply_mul_sum v φ
  dsimp [neutralToV55]
  calc
    (∑ i : Fin 5, ((v i + dualToV5 φ i) / 2) ^ 2) -
        ∑ i : Fin 5, ((v i - dualToV5 φ i) / 2) ^ 2 =
        ∑ i : Fin 5, v i * dualToV5 φ i := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = φ v := h

noncomputable def neutralToV55Isometry :
    QuadraticMap.IsometryEquiv
      (canonicalNeutralFormUnscaled (E := V5)) Clifford55.Q55 where
  toLinearEquiv := neutralToV55
  map_app' := q55_neutralToV55

@[simp] theorem neutralToV55_apply (v : V5) (φ : Module.Dual ℝ V5) :
    neutralToV55 (v, φ) =
      ((v + dualToV5 φ) / 2, (v - dualToV5 φ) / 2) := by
  rfl

@[simp] theorem neutralToV55_symm_apply (a b : V5) :
    neutralToV55.symm (a, b) =
      (a + b, dualToV5.symm (a - b)) := by
  rfl

theorem q55_neutralToV55_symm (y : V55) :
    canonicalNeutralFormUnscaled (E := V5) (neutralToV55.symm y) =
      Clifford55.Q55 y := by
  rw [← q55_neutralToV55 (neutralToV55.symm y)]
  simp

noncomputable def neutralCliffordAlgEquiv :
    CliffordAlgebra
        (canonicalNeutralFormUnscaled (E := V5)) ≃ₐ[ℝ] Clifford55.Cl55 :=
  CliffordAlgebra.equivOfIsometry neutralToV55Isometry

noncomputable def neutralCliffordMatrixRep :
    CliffordAlgebra
        (canonicalNeutralFormUnscaled (E := V5)) →ₐ[ℝ]
      InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  Clifford55.cl55SpinorRepresentation.comp neutralCliffordAlgEquiv.toAlgHom

noncomputable def neutralCliffordMatrixAlgEquiv :
    CliffordAlgebra
        (canonicalNeutralFormUnscaled (E := V5)) ≃ₐ[ℝ]
      InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  neutralCliffordAlgEquiv.trans Clifford55.cl55SpinorAlgEquiv

theorem neutralCliffordMatrixAlgEquiv_toAlgHom :
    neutralCliffordMatrixAlgEquiv.toAlgHom = neutralCliffordMatrixRep := by
  rfl

theorem neutralCliffordMatrixRep_injective :
    Function.Injective neutralCliffordMatrixRep := by
  exact Clifford55.cl55SpinorAlgEquiv.injective.comp
    neutralCliffordAlgEquiv.injective

@[simp] theorem neutralCliffordMatrixRep_ι (x : NeutralSpace) :
    neutralCliffordMatrixRep
        (CliffordAlgebra.ι
          (canonicalNeutralFormUnscaled (E := V5)) x) =
      Clifford55.cl55SpinorRepresentation
        (Clifford55.ι55 (neutralToV55 x)) := by
  simp [neutralCliffordMatrixRep, neutralCliffordAlgEquiv,
    CliffordAlgebra.equivOfIsometry]
  change Clifford55.cl55SpinorRepresentation
      (Clifford55.ι55 (neutralToV55 x)) = _
  rfl

@[simp] theorem neutralCliffordMatrixAlgEquiv_ι (x : NeutralSpace) :
    neutralCliffordMatrixAlgEquiv
        (CliffordAlgebra.ι
          (canonicalNeutralFormUnscaled (E := V5)) x) =
      Clifford55.cl55SpinorRepresentation
        (Clifford55.ι55 (neutralToV55 x)) := by
  change neutralCliffordMatrixAlgEquiv.toAlgHom
      (CliffordAlgebra.ι
        (canonicalNeutralFormUnscaled (E := V5)) x) = _
  rw [neutralCliffordMatrixAlgEquiv_toAlgHom]
  exact neutralCliffordMatrixRep_ι x

@[simp] theorem neutralCliffordAlgEquiv_ι (x : NeutralSpace) :
    neutralCliffordAlgEquiv
        (CliffordAlgebra.ι
          (canonicalNeutralFormUnscaled (E := V5)) x) =
      Clifford55.ι55 (neutralToV55 x) := by
  exact CliffordAlgebra.map_apply_ι _ _

@[simp] theorem neutralCliffordAlgEquiv_symm_ι55 (y : V55) :
    neutralCliffordAlgEquiv.symm (Clifford55.ι55 y) =
      CliffordAlgebra.ι
        (canonicalNeutralFormUnscaled (E := V5)) (neutralToV55.symm y) := by
  apply neutralCliffordAlgEquiv.injective
  rw [neutralCliffordAlgEquiv.apply_symm_apply]
  rw [neutralCliffordAlgEquiv_ι]
  simp

@[simp] theorem neutralCliffordMatrixAlgEquiv_symm_ι55 (y : V55) :
    neutralCliffordMatrixAlgEquiv.symm
        (Clifford55.cl55SpinorRepresentation (Clifford55.ι55 y)) =
      CliffordAlgebra.ι
        (canonicalNeutralFormUnscaled (E := V5)) (neutralToV55.symm y) := by
  apply neutralCliffordMatrixAlgEquiv.injective
  rw [neutralCliffordMatrixAlgEquiv.apply_symm_apply]
  rw [neutralCliffordMatrixAlgEquiv_ι]
  simp

end
end InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry
