/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge
import InfoGeometry.SuperGrassmannian.MoebiusSuperGrassmannianCPT
import InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY
import InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum
import InfoGeometry.Canonical.Erlangen20Unification

/-!
# Möbius reflection on the OSp even corner and the finite BdG block

This bridge composes the existing Section 87 even-corner map with the
Section 89 reflection law. It proves equivariance of that restriction and
the induced two-level BdG and QPNM conjugations. The full affine QPNM matrix
has a scalar-center term, which may vanish; its correct parameter
transformation is `(Eqp, ω) ↦ (Eqp + ω, -ω)`, which preserves that center.
-/

namespace InfoGeometry.Nuclear.MoebiusBdGEvenCornerBridge

open Matrix
open InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge
open InfoGeometry.SuperGrassmannian.MoebiusReflection

local notation "τ₁" => InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1 ℝ

private theorem tau_matrix :
    tau (R := ℝ) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tau, Gamma,
      InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- The even-corner restriction intertwines the Section 89 reflection with
the existing two-level sheet swap. This is a statement about the specified
corner map, not a claim that the corner is multiplicative on arbitrary
matrices. -/
theorem evenCorner_tau_conjugation (X : M₃) :
    evenCorner (tau (R := ℝ) * X * tau) = τ₁ * evenCorner X * τ₁ := by
  rw [tau_matrix]
  unfold InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [evenCorner, evenIndex, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_two]
    <;> norm_num [evenIndex, Matrix.of_apply]

/-- The Möbius-reflected OSp element restricts to the BdG block with flipped
detuning. This composes the Section 89 conjugation theorem with the Section 87
even-corner identification. -/
theorem evenCorner_reflected_ospPairingElement (ε Δ : ℝ) :
    evenCorner (tau (R := ℝ) * ospPairingElement ε Δ * tau) =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
  rw [InfoGeometry.SuperGrassmannian.MoebiusReflection.tau_intertwines_ospPairingElement,
    evenCorner_ospPairingElement]

/-- The 2×2 BdG block inherits the detuning flip from the Section 89 OSp
reflection by restriction to the even corner. -/
theorem tau1_bdgBlock_flip (ε Δ : ℝ) :
    τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
  calc
    τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
        τ₁ * evenCorner (ospPairingElement ε Δ) * τ₁ := by
          rw [evenCorner_ospPairingElement]
    _ = evenCorner (tau (R := ℝ) * ospPairingElement ε Δ * tau) :=
          (evenCorner_tau_conjugation (ospPairingElement ε Δ)).symm
    _ = InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
          rw [evenCorner_reflected_ospPairingElement]

private theorem tau1_scalar_conjugation (c : ℝ) :
    τ₁ * (c • (1 : M₂)) * τ₁ = c • (1 : M₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The complete two-level QPNM matrix transforms under the same swap when
the scalar center is kept fixed. The energy parameter shift is essential. -/
theorem tau1_qpnmMatrix_reflection (Eqp ω V : ℝ) :
    τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁ =
      InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix
        (Eqp + ω) (-ω) V := by
  rw [qpnmMatrix_eq_center_add_ospCorner Eqp ω V,
    qpnmMatrix_eq_center_add_ospCorner (Eqp + ω) (-ω) V]
  have hcenter :
      InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter Eqp ω =
        InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter
          (Eqp + ω) (-ω) := by
    simp [InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievCenter]
    ring
  have hcoordinate :
      -InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate ω =
        InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate (-ω) := by
    simp [InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.solovievBdGCoordinate]
    ring
  rw [Matrix.mul_add, Matrix.add_mul, tau1_scalar_conjugation,
    ← evenCorner_tau_conjugation,
    InfoGeometry.SuperGrassmannian.MoebiusReflection.tau_intertwines_ospPairingElement,
    hcenter, hcoordinate]

/-- Kernel-checked package of the two reflection consequences added here. -/
theorem compile_moebius_bdg_even_corner_bridge :
    (∀ X : M₃, evenCorner (tau (R := ℝ) * X * tau) =
      τ₁ * evenCorner X * τ₁) ∧
    (∀ ε Δ : ℝ,
      τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
        InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ) ∧
    (∀ Eqp ω V : ℝ,
      τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁ =
        InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix
          (Eqp + ω) (-ω) V) := by
  exact ⟨evenCorner_tau_conjugation, tau1_bdgBlock_flip,
    tau1_qpnmMatrix_reflection⟩

section ErlangenD1b

local instance : LieRing M₂ := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ M₂ := LieAlgebra.ofAssociativeAlgebra

/-- Auxiliary `ℝ`-algebra involution on `M₃` induced by `tau` conjugation. -/
def tauAlgEquivM3 : M₃ ≃ₐ[ℝ] M₃ where
  toFun X := tau (R := ℝ) * X * tau
  invFun X := tau (R := ℝ) * X * tau
  left_inv X := by
    calc
      tau (R := ℝ) * (tau * X * tau) * tau
          = (tau * tau) * X * (tau * tau) := by noncomm_ring
      _ = X := by rw [tau_sq, one_mul, mul_one]
  right_inv X := by
    calc
      tau (R := ℝ) * (tau * X * tau) * tau
          = (tau * tau) * X * (tau * tau) := by noncomm_ring
      _ = X := by rw [tau_sq, one_mul, mul_one]
  map_mul' X Y := tau_conj_mul X Y
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, tau_sq]

/-- Auxiliary `ℝ`-algebra involution on `M₂` induced by `τ₁` conjugation. -/
def tau1AlgEquivM2 : M₂ ≃ₐ[ℝ] M₂ where
  toFun X := τ₁ * X * τ₁
  invFun X := τ₁ * X * τ₁
  left_inv X := by
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    calc
      τ₁ * (τ₁ * X * τ₁) * τ₁ = (τ₁ * τ₁) * X * (τ₁ * τ₁) := by noncomm_ring
      _ = X := by rw [hsq, one_mul, mul_one]
  right_inv X := by
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    calc
      τ₁ * (τ₁ * X * τ₁) * τ₁ = (τ₁ * τ₁) * X * (τ₁ * τ₁) := by noncomm_ring
      _ = X := by rw [hsq, one_mul, mul_one]
  map_mul' X Y := by
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    calc
      τ₁ * (X * Y) * τ₁ = τ₁ * X * 1 * Y * τ₁ := by noncomm_ring
      _ = τ₁ * X * (τ₁ * τ₁) * Y * τ₁ := by rw [hsq]
      _ = (τ₁ * X * τ₁) * (τ₁ * Y * τ₁) := by noncomm_ring
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, mul_one, hsq]

private def z2AlgAction {A : Type*} [Ring A] [Algebra ℝ A]
    (e : A ≃ₐ[ℝ] A) (hsq : ∀ x : A, e (e x) = x) :
    InfoGeometry.OperatorAlgebra.OperatorSymmetryAction (Multiplicative (ZMod 2)) A where
  toFun g := if Multiplicative.toAdd g == 1 then e else AlgEquiv.refl
  map_one' := by
    change (if (0 : ZMod 2) == 1 then e else AlgEquiv.refl) = AlgEquiv.refl
    rfl
  map_mul' g₁ g₂ := by
    ext x
    have hadd : Multiplicative.toAdd (g₁ * g₂) = Multiplicative.toAdd g₁ + Multiplicative.toAdd g₂ :=
      rfl
    rw [hadd]
    have ha : Multiplicative.toAdd g₁ = 0 ∨ Multiplicative.toAdd g₁ = 1 := by
      generalize Multiplicative.toAdd g₁ = k₁
      fin_cases k₁
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hb : Multiplicative.toAdd g₂ = 0 ∨ Multiplicative.toAdd g₂ = 1 := by
      generalize Multiplicative.toAdd g₂ = k₂
      fin_cases k₂
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      simp [ha, hb, hsq, AlgEquiv.trans_apply]

/-- Discrete `ℤ₂` (`Multiplicative (ZMod 2)`) operator symmetry action generated by `tau` on `M₃`. -/
def tauZ2OperatorActionM3 :
    InfoGeometry.OperatorAlgebra.OperatorSymmetryAction (Multiplicative (ZMod 2)) M₃ :=
  z2AlgAction tauAlgEquivM3 (fun X => tauAlgEquivM3.left_inv X)

/-- Discrete `ℤ₂` ring symmetry action generated by `tau` on `M₃`. -/
def tauZ2ActionM3 :
    InfoGeometry.OperatorAlgebra.SymmetryAction (Multiplicative (ZMod 2)) M₃ :=
  InfoGeometry.OperatorAlgebra.toSymmetryAction tauZ2OperatorActionM3

/-- Discrete `ℤ₂` (`Multiplicative (ZMod 2)`) operator symmetry action generated by `τ₁` on `M₂`. -/
def tau1Z2OperatorActionM2 :
    InfoGeometry.OperatorAlgebra.OperatorSymmetryAction (Multiplicative (ZMod 2)) M₂ :=
  z2AlgAction tau1AlgEquivM2 (fun X => tau1AlgEquivM2.left_inv X)

/-- Discrete `ℤ₂` ring symmetry action generated by `τ₁` on `M₂`. -/
def tau1Z2ActionM2 :
    InfoGeometry.OperatorAlgebra.SymmetryAction (Multiplicative (ZMod 2)) M₂ :=
  InfoGeometry.OperatorAlgebra.toSymmetryAction tau1Z2OperatorActionM2

/-- `evenCorner` lifts to a `ℤ₂`-equivariant linear map between `tauZ2OperatorActionM3`
and `tau1Z2OperatorActionM2`. -/
def evenCornerZ2EquivariantMap :
    tauZ2OperatorActionM3.EquivariantLinearMap tau1Z2OperatorActionM2 where
  toLinearMap :=
    { toFun := evenCorner
      map_add' := fun X Y => by ext i j; rfl
      map_smul' := fun c X => by ext i j; rfl }
  equivariant g X := by
    change evenCorner (tauZ2OperatorActionM3.toFun g⁻¹ X) =
      tau1Z2OperatorActionM2.toFun g⁻¹ (evenCorner X)
    have hg : Multiplicative.toAdd g⁻¹ = 0 ∨ Multiplicative.toAdd g⁻¹ = 1 := by
      generalize Multiplicative.toAdd g⁻¹ = k
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hg with hg | hg
    · simp [tauZ2OperatorActionM3, tau1Z2OperatorActionM2, z2AlgAction, hg]
    · simp [tauZ2OperatorActionM3, tau1Z2OperatorActionM2, z2AlgAction, hg,
        tauAlgEquivM3, tau1AlgEquivM2, evenCorner_tau_conjugation]

/-- The OSp supertrace on `M₃(ℝ)` is an `InvariantReadout` for `tauZ2ActionM3`. -/
def ospSupertraceZ2Invariant :
    InfoGeometry.OperatorAlgebra.InvariantReadout tauZ2ActionM3 ℝ :=
  InfoGeometry.OperatorAlgebra.InvariantReadout.mk
    InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace
    (by
      intro g X
      change InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace
          (tauZ2OperatorActionM3.toFun g⁻¹ X) =
        InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair.supertrace X
      have hg : Multiplicative.toAdd g⁻¹ = 0 ∨ Multiplicative.toAdd g⁻¹ = 1 := by
        generalize Multiplicative.toAdd g⁻¹ = k
        fin_cases k
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hg with hg | hg
      · simp [tauZ2OperatorActionM3, z2AlgAction, hg]
      · simp [tauZ2OperatorActionM3, z2AlgAction, hg, tauAlgEquivM3,
          supertrace_tau_invariant])

/-- Conjugation action of `GL(2, ℝ)` on `M₂(ℝ)`. -/
def bdgGL2Action :
    InfoGeometry.OperatorAlgebra.SymmetryAction (Matrix.GeneralLinearGroup (Fin 2) ℝ) M₂ where
  act g :=
    { toFun := fun X => g.1 * X * g⁻¹.1
      invFun := fun X => g⁻¹.1 * X * g.1
      left_inv := fun X => by
        calc
          g⁻¹.1 * (g.1 * X * g⁻¹.1) * g.1
              = (g⁻¹ * g).1 * X * (g⁻¹ * g).1 := by simp [mul_assoc]
          _ = X := by simp
      right_inv := fun X => by
        calc
          g.1 * (g⁻¹.1 * X * g.1) * g⁻¹.1
              = (g * g⁻¹).1 * X * (g * g⁻¹).1 := by simp [mul_assoc]
          _ = X := by simp
      map_mul' := fun X Y => by
        calc
          g.1 * (X * Y) * g⁻¹.1 = g.1 * X * (g⁻¹ * g).1 * Y * g⁻¹.1 := by simp [mul_assoc]
          _ = (g.1 * X * g⁻¹.1) * (g.1 * Y * g⁻¹.1) := by simp [mul_assoc]
      map_add' := fun X Y => by rw [mul_add, add_mul] }
  act_one X := by
    change (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ).1 * X * (1 : Matrix.GeneralLinearGroup (Fin 2) ℝ)⁻¹.1 = X
    simp
  act_mul g h X := by
    change (g * h).1 * X * (g * h)⁻¹.1 = g.1 * (h.1 * X * h⁻¹.1) * g⁻¹.1
    rw [_root_.mul_inv_rev]
    simp [mul_assoc]

/-- Erlangen 2.0 datum on the `M₂(ℝ)` BdG–Soloviev carrier under `GL(2, ℝ)` symmetry. -/
noncomputable def bdgGL2Erlangen20Datum :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.Erlangen20Datum
      ℝ (Fin 2 → ℝ) M₂
      (InfoGeometry.OperatorAlgebra.SymmetryAction (Matrix.GeneralLinearGroup (Fin 2) ℝ) M₂)
      (Subring M₂) :=
  InfoGeometry.Canonical.Erlangen20Unification.erlangen20DatumOfSymmetryActionOnModule
    bdgGL2Action Matrix.toLinAlgEquiv'.toAlgHom LinearMap.id (fun _ _ => rfl)

/-- Determinant `InvariantReadout` for `bdgGL2Action` on `M₂(ℝ)`. -/
def bdgDetInvariantReadout :
    InfoGeometry.OperatorAlgebra.InvariantReadout bdgGL2Action ℝ :=
  InfoGeometry.OperatorAlgebra.InvariantReadout.mk Matrix.det
    (by
      intro g X
      change Matrix.det (g.1 * X * g⁻¹.1) = Matrix.det X
      rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul])

/-- Trace `InvariantReadout` for `bdgGL2Action` on `M₂(ℝ)`. -/
def bdgTraceInvariantReadout :
    InfoGeometry.OperatorAlgebra.InvariantReadout bdgGL2Action ℝ :=
  InfoGeometry.OperatorAlgebra.InvariantReadout.mk Matrix.trace
    (by
      intro g X
      change Matrix.trace (g.1 * X * g⁻¹.1) = Matrix.trace X
      rw [Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul])

/-- The 2-level BdG block in `NuclearBdGTwoLevelExact` agrees definitionally with
`NuclearQuasiphononKreinSUSY.bdgBlock`. -/
theorem bdgBlock_twoLevel_eq_kreinSUSY (ε Δ : ℝ) :
    InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ =
      InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.bdgBlock ε Δ := by
  dsimp [InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock,
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.bdgBlock]

/-- Exact Casimir determinant invariant of `bdgBlock ε Δ` under the entire `GL(2, ℝ)` action:
`det (g · bdgBlock ε Δ · g⁻¹) = -(ε² + Δ²)`. -/
theorem bdgBlock_casimir_det_invariant
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ) (ε Δ : ℝ) :
    Matrix.det (bdgGL2Action.act g (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)) =
      -(ε ^ 2 + Δ ^ 2) := by
  have hinv :
      Matrix.det (bdgGL2Action.act g (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)) =
        Matrix.det (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) :=
    bdgDetInvariantReadout.invariant g (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)
  rw [hinv, bdgBlock_twoLevel_eq_kreinSUSY]
  exact InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.bdgBlock_det ε Δ

/-- Exact Casimir quadratic dispersion invariant of `bdgBlock ε Δ` under `GL(2, ℝ)`:
`(g · bdgBlock ε Δ · g⁻¹)² = (ε² + Δ²) • 1`. -/
theorem bdgBlock_casimir_sq_invariant
    (g : Matrix.GeneralLinearGroup (Fin 2) ℝ) (ε Δ : ℝ) :
    (bdgGL2Action.act g (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)) ^ 2 =
      (ε ^ 2 + Δ ^ 2) • (1 : M₂) := by
  rw [sq, ← (bdgGL2Action.act g).map_mul, bdgBlock_twoLevel_eq_kreinSUSY,
    InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.bdgBlock_sq ε Δ]
  change g.1 * ((ε ^ 2 + Δ ^ 2) • (1 : M₂)) * g⁻¹.1 = (ε ^ 2 + Δ ^ 2) • (1 : M₂)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

/-- The 2×2 Krein metric `diag(1, -1)` on `M₂(ℝ)`. -/
def krein2 : M₂ := !![1, 0; 0, -1]

/-- `τ₁` as an element of `GL(2, ℝ)`. -/
def tau1GL : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := τ₁
  inv := τ₁
  val_inv := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
  inv_val := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ

/-- `krein2` as an element of `GL(2, ℝ)`. -/
def krein2GL : Matrix.GeneralLinearGroup (Fin 2) ℝ where
  val := krein2
  inv := krein2
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [krein2, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [krein2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Linear equivalence on `Fin 2 → ℝ` induced by `τ₁`. -/
noncomputable def tau1LinearEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toLinearMap := Matrix.toLin' τ₁
  invFun := Matrix.toLin' τ₁
  left_inv v := by
    have hsq := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    change (Matrix.toLin' τ₁).comp (Matrix.toLin' τ₁) v = v
    rw [← Matrix.toLin'_mul, hsq, Matrix.toLin'_one]
    rfl
  right_inv v := by
    have hsq := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    change (Matrix.toLin' τ₁).comp (Matrix.toLin' τ₁) v = v
    rw [← Matrix.toLin'_mul, hsq, Matrix.toLin'_one]
    rfl

/-- Linear equivalence on `Fin 2 → ℝ` induced by `krein2`. -/
noncomputable def krein2LinearEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toLinearMap := Matrix.toLin' krein2
  invFun := Matrix.toLin' krein2
  left_inv v := by
    change (Matrix.toLin' krein2).comp (Matrix.toLin' krein2) v = v
    rw [← Matrix.toLin'_mul, show krein2 * krein2 = 1 from krein2GL.val_inv, Matrix.toLin'_one]
    rfl
  right_inv v := by
    change (Matrix.toLin' krein2).comp (Matrix.toLin' krein2) v = v
    rw [← Matrix.toLin'_mul, show krein2 * krein2 = 1 from krein2GL.val_inv, Matrix.toLin'_one]
    rfl

/-- Canonical index equivalence `(Unit ⊕ Unit) ≃ Fin 2`. -/
def unitSumEquivFin2 : (Unit ⊕ Unit) ≃ Fin 2 where
  toFun
    | .inl () => 0
    | .inr () => 1
  invFun i := if i = 0 then .inl () else .inr ()
  left_inv x := by cases x <;> simp
  right_inv i := by fin_cases i <;> rfl

/-- Canonical linear equivalence `(Unit ⊕ Unit → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)`. -/
def unitSumLinearEquivFin2 : (Unit ⊕ Unit → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ unitSumEquivFin2.symm

/-- Conjugation by `krein2` flips the pairing off-diagonal sign `Δ ↦ -Δ` on `bdgBlock`. -/
theorem krein2_bdgBlock_sign (ε Δ : ℝ) :
    bdgGL2Action.act krein2GL (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε (-Δ) := by
  change krein2 * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * krein2 =
    InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε (-Δ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [krein2, InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by `tau1GL` flips the detuning sign `ε ↦ -ε` on `bdgBlock`. -/
theorem tau1GL_bdgBlock_flip (ε Δ : ℝ) :
    bdgGL2Action.act tau1GL (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ := by
  change τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
    InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ
  exact tau1_bdgBlock_flip ε Δ

/-- Exact detuning sign-defect of `τ₁` conjugation on `bdgBlock`:
`τ₁ H_BdG(ε, Δ) τ₁ - H_BdG(ε, Δ) = (-2 ε) • krein2` (vanishes iff `ε = 0`). -/
theorem bdgBlock_tau1_sign_defect (ε Δ : ℝ) :
    bdgGL2Action.act tau1GL (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) -
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ =
      (-2 * ε) • krein2 := by
  rw [tau1GL_bdgBlock_flip]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock, krein2] <;>
    ring

/-- Exact pairing sign-defect of `krein2` conjugation on `bdgBlock`:
`J_2 H_BdG(ε, Δ) J_2 - H_BdG(ε, Δ) = (-2 Δ) • τ₁` (vanishes iff `Δ = 0`). -/
theorem bdgBlock_krein2_sign_defect (ε Δ : ℝ) :
    bdgGL2Action.act krein2GL (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) -
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ =
      (-2 * Δ) • τ₁ := by
  rw [krein2_bdgBlock_sign]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock,
      InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1] <;>
    ring

/-- Conjugation by `tau1GL` induces `(Eqp, ω) ↦ (Eqp + ω, -ω)` on `qpnmMatrix`. -/
theorem tau1GL_qpnmMatrix_reflection (Eqp ω V : ℝ) :
    bdgGL2Action.act tau1GL (InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V) =
      InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix (Eqp + ω) (-ω) V := by
  change τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁ =
    InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix (Eqp + ω) (-ω) V
  exact tau1_qpnmMatrix_reflection Eqp ω V

/-- Explicit `OperatorIntertwiner` witnessing `τ₁` conjugation from `bdgBlock ε Δ` to
`bdgBlock (-ε) Δ`. -/
noncomputable def tau1_bdg_operatorIntertwiner (ε Δ : ℝ) :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner
      ℝ (Fin 2 → ℝ) (Fin 2 → ℝ) where
  carrierEquiv := tau1LinearEquiv
  source := Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)
  target := Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ)
  intertwines v := by
    have h := tau1_bdgBlock_flip ε Δ
    have hmul := congrArg (fun M : M₂ => Matrix.toLin' M v) h
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    have hid : τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ =
        τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁ := rfl
    calc
      Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock (-ε) Δ)
          (tau1LinearEquiv v)
          = Matrix.toLin'
              ((τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * τ₁) * τ₁) v := by
                rw [h, Matrix.toLin'_mul_apply]
                rfl
      _ = Matrix.toLin'
            (τ₁ * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) v := by
              rw [mul_assoc, hsq, mul_one]
      _ = tau1LinearEquiv
            (Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) v) := by
              rw [Matrix.toLin'_mul_apply]
              rfl

/-- Explicit `OperatorIntertwiner` witnessing `krein2` conjugation from `bdgBlock ε Δ` to
`bdgBlock ε (-Δ)`. -/
noncomputable def krein2_bdg_operatorIntertwiner (ε Δ : ℝ) :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner
      ℝ (Fin 2 → ℝ) (Fin 2 → ℝ) where
  carrierEquiv := krein2LinearEquiv
  source := Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ)
  target := Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε (-Δ))
  intertwines v := by
    have h := krein2_bdgBlock_sign ε Δ
    change krein2 * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * krein2 =
      InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε (-Δ) at h
    calc
      Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε (-Δ))
          (krein2LinearEquiv v)
          = Matrix.toLin'
              ((krein2 * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ * krein2) *
                krein2) v := by
                rw [h, Matrix.toLin'_mul_apply]
                rfl
      _ = Matrix.toLin'
            (krein2 * InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) v := by
              have hsq : krein2 * krein2 = 1 := krein2GL.val_inv
              rw [mul_assoc, hsq, mul_one]
      _ = krein2LinearEquiv
            (Matrix.toLin' (InfoGeometry.Physics.NuclearBdGTwoLevelExact.bdgBlock ε Δ) v) := by
              rw [Matrix.toLin'_mul_apply]
              rfl

/-- Explicit `OperatorIntertwiner` witnessing `τ₁` reflection on `qpnmMatrix Eqp ω V`. -/
noncomputable def tau1_qpnm_operatorIntertwiner (Eqp ω V : ℝ) :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner
      ℝ (Fin 2 → ℝ) (Fin 2 → ℝ) where
  carrierEquiv := tau1LinearEquiv
  source := Matrix.toLin' (InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V)
  target := Matrix.toLin'
    (InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix (Eqp + ω) (-ω) V)
  intertwines v := by
    have h := tau1_qpnmMatrix_reflection Eqp ω V
    have hsq : τ₁ * τ₁ = 1 := InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1_sq ℝ
    calc
      Matrix.toLin' (InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix (Eqp + ω) (-ω) V)
          (tau1LinearEquiv v)
          = Matrix.toLin'
              ((τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V * τ₁) *
                τ₁) v := by
                rw [h, Matrix.toLin'_mul_apply]
                rfl
      _ = Matrix.toLin'
            (τ₁ * InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V) v := by
              rw [mul_assoc, hsq, mul_one]
      _ = tau1LinearEquiv
            (Matrix.toLin' (InfoGeometry.Physics.SolovievQPNMEigenproblem.qpnmMatrix Eqp ω V) v) := by
              rw [Matrix.toLin'_mul_apply]
              rfl

/-- Explicit `OperatorIntertwiner` identifying `NuclearQuasiphononKreinSUSY.kreinMetric Unit Unit ℝ`
on `Unit ⊕ Unit → ℝ` with `krein2` on `Fin 2 → ℝ`. -/
noncomputable def kreinMetric_to_krein2_operatorIntertwiner :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner
      ℝ (Unit ⊕ Unit → ℝ) (Fin 2 → ℝ) where
  carrierEquiv := unitSumLinearEquivFin2
  source := Matrix.toLin' (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.kreinMetric Unit Unit ℝ)
  target := Matrix.toLin' krein2
  intertwines v := by
    ext i
    fin_cases i <;>
      simp [unitSumLinearEquivFin2, unitSumEquivFin2, krein2,
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.kreinMetric,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]

/-- Explicit `OperatorIntertwiner` identifying `NuclearQuasiphononKreinSUSY.sheetSwap Unit ℝ`
on `Unit ⊕ Unit → ℝ` with `τ₁` on `Fin 2 → ℝ`. -/
noncomputable def sheetSwap_to_tau1_operatorIntertwiner :
    InfoGeometry.Canonical.Erlangen20OperatorGeometryDatum.OperatorIntertwiner
      ℝ (Unit ⊕ Unit → ℝ) (Fin 2 → ℝ) where
  carrierEquiv := unitSumLinearEquivFin2
  source := Matrix.toLin' (InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sheetSwap Unit ℝ)
  target := Matrix.toLin' τ₁
  intertwines v := by
    ext i
    fin_cases i <;>
      simp [unitSumLinearEquivFin2, unitSumEquivFin2,
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.tau1,
        InfoGeometry.Nuclear.NuclearQuasiphononKreinSUSY.sheetSwap,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]

end ErlangenD1b

end InfoGeometry.Nuclear.MoebiusBdGEvenCornerBridge
