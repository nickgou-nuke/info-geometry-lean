/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11GradedMorita
import InfoGeometry.Clifford.Cl11CliffordMapIsometryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.OperatorAlgebra.SymmetryInvariants

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

/-- The Clifford lift of the negative-coordinate reflection is the matrix
adjoint action of the positive Clifford generator in the canonical
`Cl(1,1) ≃ M₂(ℝ)` representation. The identification with the Klein glide
derivative is supplied separately by the topology-to-Clifford owner. -/
theorem cl11EquivMat_splitReflectionCliffordAuto (a : CliffordAlgebra q11) :
    cl11EquivMat (splitReflectionCliffordAuto a) =
      adjointAlgEquiv gammaUnit (cl11EquivMat a) := by
  have hmaps :
      cl11EquivMat.toAlgHom.comp splitReflectionCliffordAuto.toAlgHom =
        (adjointAlgEquiv gammaUnit).toAlgHom.comp cl11EquivMat.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    have hginv : (↑(gammaUnit⁻¹) : Mat2) = Eplus := by rfl
    dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      AlgHom.comp_apply]
    change cl11EquivMat (splitReflectionCliffordAuto
        (CliffordAlgebra.ι q11 (x, y))) =
      adjointAlgEquiv gammaUnit
        (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
    rw [splitReflectionCliffordAuto_ι, adjointAlgEquiv_apply,
      gammaUnit_value, hginv]
    simp only [cl11EquivMat, cl11ToMat, gen, splitReflection]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]
  exact DFunLike.congr_fun hmaps a

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
  change adjointAlgEquiv (1 : Mat2ˣ) A = A
  exact adjoint_one A

theorem adjointAlgHom_neg_one :
    adjointAlgHom (-1 : Mat2ˣ) = (AlgEquiv.refl : Mat2 ≃ₐ[ℝ] Mat2) := by
  apply AlgEquiv.ext
  intro A
  change adjointAlgEquiv (-1 : Mat2ˣ) A = A
  exact adjoint_neg_one A

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
    simp [Eminus, J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]

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
      adjointAlgHom_bivector_gamma, adjointAlgHom_gamma_causal,
      adjointAlgHom_bivector_causal, adjointAlgHom_causal_gamma,
      adjointAlgHom_causal_bivector, hrefl]

noncomputable def localCl11RootMap :
    V4Group →* (Mat2 ≃ₐ[ℝ] Mat2) where
  toFun g := adjointAlgHom (rootUnit g)
  map_one' := by change adjointAlgHom 1 = 1; rw [adjointAlgHom_one]; exact AlgEquiv.ext fun _ => rfl
  map_mul' := rootUnit_adjoint_mul

noncomputable def localCl11Map : V4 →* (Mat2 ≃ₐ[ℝ] Mat2) :=
  localCl11RootMap.comp v4RootHom

@[simp] theorem localCl11Map_apply (g : V4) :
    localCl11Map g = adjointAlgHom (rootUnit (v4RootHom g)) := rfl

section CliffordAtomV4Symmetry

open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.OperatorAlgebra

/-- Central inversion `(x, y) ↦ (-x, -y)` on the split plane `ℝ × ℝ`. -/
def centralInversion : Vec11 ≃ₗ[ℝ] Vec11 where
  toFun v := (-v.1, -v.2)
  invFun v := (-v.1, -v.2)
  left_inv v := by rcases v with ⟨x, y⟩; simp
  right_inv v := by rcases v with ⟨x, y⟩; simp
  map_add' u v := by
    rcases u with ⟨u₁, u₂⟩
    rcases v with ⟨v₁, v₂⟩
    ext <;> simp <;> ring
  map_smul' c v := by rcases v with ⟨x, y⟩; ext <;> simp

@[simp] theorem centralInversion_apply (v : Vec11) :
    centralInversion v = (-v.1, -v.2) := rfl

@[simp] theorem q11_centralInversion (v : Vec11) :
    q11 (centralInversion v) = q11 v := by
  rcases v with ⟨x, y⟩
  simp [centralInversion, q11_apply]

/-- Central inversion as a quadratic-form isometry equivalence on `q11`. -/
noncomputable def centralInversionIsometryEquiv : q11.IsometryEquiv q11 where
  toLinearEquiv := centralInversion
  map_app' := q11_centralInversion

/-- The Clifford algebra lift of central inversion is `CliffordAlgebra.involuteEquiv`. -/
theorem clifford_equivOfIsometry_centralInversion :
    CliffordAlgebra.equivOfIsometry centralInversionIsometryEquiv =
      CliffordAlgebra.involuteEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change CliffordAlgebra.map centralInversionIsometryEquiv.toIsometry
      (CliffordAlgebra.ι q11 v) =
    CliffordAlgebra.involute (CliffordAlgebra.ι q11 v)
  rw [CliffordAlgebra.map_apply_ι, CliffordAlgebra.involute_ι, ← map_neg]
  rfl

private noncomputable def v4RootAutoFun :
    V4Group → (CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11)
  | V4Group.I => AlgEquiv.refl
  | V4Group.W1 => splitReflectionCliffordAuto
  | V4Group.W2 => CliffordAlgebra.involuteEquiv
  | V4Group.W12 => splitReflectionFirstCoordinateCliffordAuto

private noncomputable def v4RootVecFun : V4Group → Vec11 → Vec11
  | V4Group.I, v => v
  | V4Group.W1, v => (v.1, -v.2)
  | V4Group.W2, v => (-v.1, -v.2)
  | V4Group.W12, v => (-v.1, v.2)

private theorem v4RootAutoFun_ι (g : V4Group) (v : Vec11) :
    v4RootAutoFun g (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι q11 (v4RootVecFun g v) := by
  cases g
  · rfl
  · exact splitReflectionCliffordAuto_ι v
  · change CliffordAlgebra.involute (CliffordAlgebra.ι q11 v) = _
    rw [CliffordAlgebra.involute_ι, ← map_neg]
    rfl
  · exact splitReflectionFirstCoordinateCliffordAuto_ι v

private theorem v4RootAutoFun_mul (g h : V4Group) :
    v4RootAutoFun (g * h) = v4RootAutoFun g * v4RootAutoFun h := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  rcases v with ⟨x, y⟩
  change v4RootAutoFun (v4_mul g h) (CliffordAlgebra.ι q11 (x, y)) =
    v4RootAutoFun g (v4RootAutoFun h (CliffordAlgebra.ι q11 (x, y)))
  rw [v4RootAutoFun_ι, v4RootAutoFun_ι, v4RootAutoFun_ι]
  apply congrArg (CliffordAlgebra.ι q11)
  cases g <;> cases h <;> simp [v4_mul, v4RootVecFun]

/-- Native `V4Group` action by `CliffordAlgebra.equivOfIsometry` automorphisms on `Cl(1,1)`. -/
noncomputable def cl11V4RootAuto :
    V4Group →* (CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11) where
  toFun := v4RootAutoFun
  map_one' := rfl
  map_mul' := v4RootAutoFun_mul

/-- Native `V4` Klein-four action on `CliffordAlgebra q11` via `v4RootHom`. -/
noncomputable def cl11V4Auto :
    V4 →* (CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11) :=
  cl11V4RootAuto.comp v4RootHom

@[simp] theorem cl11V4Auto_one : cl11V4Auto (1 : V4) = AlgEquiv.refl := by
  rfl

@[simp] theorem cl11V4Auto_P :
    cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
      splitReflectionCliffordAuto := rfl

@[simp] theorem cl11V4Auto_T :
    cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
      CliffordAlgebra.involuteEquiv := rfl

@[simp] theorem cl11V4Auto_PT :
    cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
      splitReflectionFirstCoordinateCliffordAuto := rfl

/-- Exact equivariance of `cl11EquivMat` between `cl11V4Auto` and `localCl11Map`. -/
theorem cl11EquivMat_v4Auto (g : V4) (a : CliffordAlgebra q11) :
    cl11EquivMat (cl11V4Auto g a) = localCl11Map g (cl11EquivMat a) := by
  have hhom :
      cl11EquivMat.toAlgHom.comp (cl11V4Auto g).toAlgHom =
        (localCl11Map g).toAlgHom.comp cl11EquivMat.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
      revert g; decide
    rcases hcases with rfl | rfl | rfl | rfl
    · change cl11EquivMat (cl11V4Auto 1 (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map 1 (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      rw [map_one, map_one]
      rfl
    · change cl11EquivMat (splitReflectionCliffordAuto (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
          (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      exact cl11EquivMat_splitReflectionCliffordAuto (CliffordAlgebra.ι q11 (x, y))
    · change cl11EquivMat (CliffordAlgebra.involute (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
          (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      have hT : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
          V4Group.W2 := rfl
      have hbinv : (↑(bivectorUnit⁻¹) : Mat2) = J1 := rfl
      rw [CliffordAlgebra.involute_ι, map_neg, localCl11Map_apply, hT]
      simp only [rootUnit, adjointAlgHom_apply, adjointAlgEquiv_apply, bivectorUnit_value,
        hbinv, cl11EquivMat, cl11ToMat, gen]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]
    · change cl11EquivMat
          (splitReflectionFirstCoordinateCliffordAuto (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)
          (cl11EquivMat (CliffordAlgebra.ι q11 (x, y)))
      have hPT : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
          V4Group.W12 := rfl
      have hcinv : (↑(causalUnit⁻¹) : Mat2) = -Eminus := rfl
      rw [splitReflectionFirstCoordinateCliffordAuto_ι, localCl11Map_apply, hPT]
      simp only [rootUnit, adjointAlgHom_apply, adjointAlgEquiv_apply, causalUnit_value, hcinv,
        splitReflectionFirstCoordinate, LinearEquiv.coe_mk, cl11EquivMat, cl11ToMat, gen]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]
  exact AlgHom.congr_fun hhom a

/-- The Walsh-conjugation swap `P ↔ T` on `V4` (fixing `1` and `PT`). -/
def walshV4Swap : V4 →* V4 where
  toFun g :=
    if g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P then
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T
    else if g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T then
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P
    else g
  map_one' := by decide
  map_mul' g h := by
    revert g h
    decide

@[simp] theorem walshV4Swap_one : walshV4Swap 1 = 1 := by simp

@[simp] theorem walshV4Swap_P :
    walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T := by decide

@[simp] theorem walshV4Swap_T :
    walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P := by decide

@[simp] theorem walshV4Swap_PT :
    walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
      Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by decide

@[simp] theorem walshV4Swap_involutive (g : V4) :
    walshV4Swap (walshV4Swap g) = g := by
  revert g
  decide

/-- Under `cl11StandardEquiv = cl11EquivMat.trans walshConjugation`, the `V4` atom
symmetry intertwines with `localCl11Map` twisted by the Walsh `P ↔ T` swap. -/
theorem cl11StandardEquiv_v4Auto (g : V4) (a : CliffordAlgebra q11) :
    cl11StandardEquiv (cl11V4Auto g a) =
      localCl11Map (walshV4Swap g) (cl11StandardEquiv a) := by
  have hhom :
      cl11StandardEquiv.toAlgHom.comp (cl11V4Auto g).toAlgHom =
        (localCl11Map (walshV4Swap g)).toAlgHom.comp cl11StandardEquiv.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
        g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
      revert g; decide
    rcases hcases with rfl | rfl | rfl | rfl
    · change cl11StandardEquiv (cl11V4Auto 1 (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (walshV4Swap 1) (cl11StandardEquiv (CliffordAlgebra.ι q11 (x, y)))
      rw [walshV4Swap_one, map_one, map_one]
      rfl
    · change cl11StandardEquiv (splitReflectionCliffordAuto (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P))
          (cl11StandardEquiv (CliffordAlgebra.ι q11 (x, y)))
      rw [splitReflectionCliffordAuto_ι, cl11StandardEquiv_ι, cl11StandardEquiv_ι,
        walshV4Swap_P, localCl11Map_apply]
      have hT : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
          V4Group.W2 := rfl
      have hbinv : (↑(bivectorUnit⁻¹) : Mat2) = J1 := rfl
      rw [hT]
      simp only [rootUnit, adjointAlgHom_apply, adjointAlgEquiv_apply,
        bivectorUnit_value, hbinv, splitReflection]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]
    · change cl11StandardEquiv (CliffordAlgebra.involute (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T))
          (cl11StandardEquiv (CliffordAlgebra.ι q11 (x, y)))
      rw [cl11StandardEquiv_involute, walshV4Swap_T, localCl11Map_apply]
      have hP : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
          V4Group.W1 := rfl
      have hginv : (↑(gammaUnit⁻¹) : Mat2) = Eplus := rfl
      rw [hP]
      simp [rootUnit, adjointAlgEquiv_apply, gammaUnit_value, hginv]
    · change cl11StandardEquiv
          (splitReflectionFirstCoordinateCliffordAuto (CliffordAlgebra.ι q11 (x, y))) =
        localCl11Map (walshV4Swap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT))
          (cl11StandardEquiv (CliffordAlgebra.ι q11 (x, y)))
      rw [splitReflectionFirstCoordinateCliffordAuto_ι, cl11StandardEquiv_ι,
        cl11StandardEquiv_ι, walshV4Swap_PT, localCl11Map_apply]
      have hPT : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
          V4Group.W12 := rfl
      have hcinv : (↑(causalUnit⁻¹) : Mat2) = -Eminus := rfl
      rw [hPT]
      simp only [rootUnit, adjointAlgHom_apply, adjointAlgEquiv_apply,
        causalUnit_value, hcinv, splitReflectionFirstCoordinate]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  exact AlgHom.congr_fun hhom a

/-- `V4` symmetry action on `Mat2` induced by `localCl11Map`. -/
noncomputable def mat2V4SymmetryAction : SymmetryAction V4 Mat2 where
  act g := (localCl11Map g).toRingEquiv
  act_one x := by
    change localCl11Map 1 x = x
    rw [map_one]
    rfl
  act_mul g h x := by simp [map_mul]

/-- `V4` symmetry action on `CliffordAlgebra q11` induced by `cl11V4Auto`. -/
noncomputable def cl11V4SymmetryAction :
    SymmetryAction V4 (CliffordAlgebra q11) where
  act g := (cl11V4Auto g).toRingEquiv
  act_one x := by
    change cl11V4Auto 1 x = x
    rw [cl11V4Auto_one]
    rfl
  act_mul g h x := by simp [map_mul]

/-- Every element of `cl11V4Auto` commutes with `CliffordAlgebra.involute`. -/
theorem cl11V4_involute_comm (g : V4) (a : CliffordAlgebra q11) :
    cl11V4Auto g (CliffordAlgebra.involute a) =
      CliffordAlgebra.involute (cl11V4Auto g a) := by
  have hcases : g = 1 ∨ g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T ∨
      g = Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT := by
    revert g; decide
  rcases hcases with rfl | rfl | rfl | rfl
  · simp
  · have hhom :
        (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)).toAlgHom.comp
          (CliffordAlgebra.involute (Q := q11)) =
        (CliffordAlgebra.involute (Q := q11)).comp
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)).toAlgHom := by
      apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
      simp [CliffordAlgebra.involute_ι, splitReflectionCliffordAuto_ι]
    exact AlgHom.congr_fun hhom a
  · rfl
  · have hhom :
        (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)).toAlgHom.comp
          (CliffordAlgebra.involute (Q := q11)) =
        (CliffordAlgebra.involute (Q := q11)).comp
          (cl11V4Auto (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT)).toAlgHom := by
      apply CliffordAlgebra.hom_ext; apply LinearMap.ext; intro v
      simp [CliffordAlgebra.involute_ι, splitReflectionFirstCoordinateCliffordAuto_ι]
    exact AlgHom.congr_fun hhom a

/-- In `M₂(ℝ)`, the `V4`-invariant matrices are precisely the real scalars. -/
theorem mat2V4_invariant_iff_scalar (M : Mat2) :
    IsInvariant mat2V4SymmetryAction M ↔ ∃ r : ℝ, M = r • (1 : Mat2) := by
  constructor
  · intro hinv
    have hP := hinv (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P)
    have hT := hinv (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T)
    change localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) M = M at hP
    change localCl11Map (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) M = M at hT
    have hP' : Eplus * M * Eplus = M := by
      have h1 : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
          V4Group.W1 := rfl
      have h2 : (↑(gammaUnit⁻¹) : Mat2) = Eplus := rfl
      simpa [localCl11Map_apply, h1, localCl11RootMap, rootUnit,
        adjointAlgHom_apply, adjointAlgEquiv_apply, gammaUnit_value, h2] using hP
    have hT' : J1 * M * J1 = M := by
      have h1 : v4RootHom (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
          V4Group.W2 := rfl
      have h2 : (↑(bivectorUnit⁻¹) : Mat2) = J1 := rfl
      simpa [localCl11Map_apply, h1, localCl11RootMap, rootUnit,
        adjointAlgHom_apply, adjointAlgEquiv_apply, bivectorUnit_value, h2] using hT
    have h01 : M 0 1 = 0 := by
      have h := congrArg (fun N : Mat2 => N 0 1) hP'
      simp [Eplus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] at h
      linarith
    have h10 : M 1 0 = 0 := by
      have h := congrArg (fun N : Mat2 => N 1 0) hP'
      simp [Eplus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] at h
      linarith
    have h11 : M 1 1 = M 0 0 := by
      have h := congrArg (fun N : Mat2 => N 0 0) hT'
      simp [J1, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] at h
      exact h
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]
  · rintro ⟨r, rfl⟩ g
    change localCl11Map g (r • (1 : Mat2)) = r • (1 : Mat2)
    rw [map_smul, map_one]

/-- In `Cl(1,1)`, the `V4`-invariant elements are precisely the real scalars. -/
theorem cl11V4_invariant_iff_scalar (a : CliffordAlgebra q11) :
    IsInvariant cl11V4SymmetryAction a ↔
      ∃ r : ℝ, a = algebraMap ℝ (CliffordAlgebra q11) r := by
  constructor
  · intro hinv
    have hMat : IsInvariant mat2V4SymmetryAction (cl11EquivMat a) := by
      intro g
      change localCl11Map g (cl11EquivMat a) = cl11EquivMat a
      rw [← cl11EquivMat_v4Auto]
      exact congrArg cl11EquivMat (hinv g)
    obtain ⟨r, hr⟩ := (mat2V4_invariant_iff_scalar (cl11EquivMat a)).mp hMat
    refine ⟨r, cl11EquivMat.injective ?_⟩
    rw [hr, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
  · rintro ⟨r, rfl⟩ g
    change cl11V4Auto g (algebraMap ℝ (CliffordAlgebra q11) r) =
      algebraMap ℝ (CliffordAlgebra q11) r
    exact (cl11V4Auto g).commutes r

end CliffordAtomV4Symmetry

end InfoGeometry.Canonical.Cl11KleinFourAdjointRepresentation
