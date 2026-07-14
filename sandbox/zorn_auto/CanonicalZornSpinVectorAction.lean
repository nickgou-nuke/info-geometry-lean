import CanonicalZornSpinChirality

/-!
# Vector action induced by canonical Zorn spin conjugation

This module begins the missing vector/half-spin compatibility layer.  The
canonical gamma representation is faithful on the vector generators: this is
proved intrinsically by evaluating a gamma operator on the positive Zorn
identity spinor.  Consequently the universal Clifford inclusion is injective
on the vector carrier, allowing spin conjugation to be transported back to a
well-defined vector action.
-/

noncomputable section

namespace CanonicalZornSpinVectorAction

open SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornSpinChirality
open CanonicalZornSpinRelatedFiber
open CanonicalZornOuterTrialityGroup
open CanonicalZornFiveGradedClosure

/-- The positive semispinor represented by the Zorn multiplicative identity. -/
def identitySpinorPlus : SpinorPlus8 := ⟨I_zorn⟩

@[simp] theorem cliffordPlus_identitySpinor (V : Vector8) :
    cliffordPlus V identitySpinorPlus = ⟨V.val⟩ := by
  apply ZornCopy.ext
  exact zornMul_I_zorn V.val

/-- A vector is recovered from its gamma operator by applying it to the
positive identity spinor and reading the negative component. -/
theorem diracGamma_identitySpinor (V : Vector8) :
    (diracGamma V (identitySpinorPlus, 0)).2 = ⟨V.val⟩ := by
  exact cliffordPlus_identitySpinor V

/-- Faithfulness of the canonical gamma map on vector generators. -/
theorem diracGammaLinear_injective :
    Function.Injective diracGammaLinear := by
  intro V W h
  have happ := LinearMap.congr_fun h (identitySpinorPlus, 0)
  have hsnd := congrArg Prod.snd happ
  have hcopy : (⟨V.val⟩ : SpinorMinus8) = ⟨W.val⟩ := by
    change (diracGamma V (identitySpinorPlus, 0)).2 =
      (diracGamma W (identitySpinorPlus, 0)).2 at hsnd
    simpa only [diracGamma_identitySpinor] using hsnd
  have hval : V.val = W.val :=
    congrArg (fun C : SpinorMinus8 => C.val) hcopy
  apply ZornCopy.ext
  exact hval

/-- The universal Clifford generator inclusion is faithful on the canonical
eight-dimensional vector carrier. -/
theorem cliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι vectorQuadratic) := by
  intro V W h
  apply diracGammaLinear_injective
  change diracGamma V = diracGamma W
  simpa only [zornCliffordRepresentation_ι] using
    congrArg zornCliffordRepresentation h

/-- The vector carrier identified linearly with the range of the Clifford
generator inclusion. -/
def vectorIotaEquivRange :
    Vector8 ≃ₗ[ℂ] LinearMap.range (CliffordAlgebra.ι vectorQuadratic) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι vectorQuadratic)
    cliffordIota_injective

@[simp] theorem vectorIotaEquivRange_coe (V : Vector8) :
    ((vectorIotaEquivRange V :
      LinearMap.range (CliffordAlgebra.ι vectorQuadratic)) :
        CliffordAlgebra vectorQuadratic) =
      CliffordAlgebra.ι vectorQuadratic V := rfl

/-! ## Transport of spin conjugation to the vector carrier -/

def spinConjugateIotaLinear (g : ComplexSpin44) :
    Vector8 →ₗ[ℂ] LinearMap.range (CliffordAlgebra.ι vectorQuadratic) where
  toFun V :=
    ⟨ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι vectorQuadratic V,
      spinGroup.conjAct_smul_ι_mem_range_ι g.2 V⟩
  map_add' V W := by
    apply Subtype.ext
    simp
  map_smul' c V := by
    apply Subtype.ext
    change ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι vectorQuadratic (c • V) =
      c • (ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι vectorQuadratic V)
    rw [map_smul]
    exact smul_comm (ConjAct.toConjAct (spinGroup.toUnits g)) c
      (CliffordAlgebra.ι vectorQuadratic V)

/-- Linear vector action induced by conjugation inside the Clifford algebra. -/
def spinVectorLinear (g : ComplexSpin44) : Module.End ℂ Vector8 :=
  vectorIotaEquivRange.symm.toLinearMap.comp (spinConjugateIotaLinear g)

/-- Characterizing equation for the transported vector action. -/
theorem cliffordIota_spinVectorLinear (g : ComplexSpin44) (V : Vector8) :
    CliffordAlgebra.ι vectorQuadratic (spinVectorLinear g V) =
      ConjAct.toConjAct (spinGroup.toUnits g) •
        CliffordAlgebra.ι vectorQuadratic V := by
  change CliffordAlgebra.ι vectorQuadratic
      (vectorIotaEquivRange.symm (spinConjugateIotaLinear g V)) = _
  exact LinearEquiv.ofInjective_symm_apply
    (CliffordAlgebra.ι vectorQuadratic) (spinConjugateIotaLinear g V)

theorem spinVectorLinear_one : spinVectorLinear 1 = 1 := by
  apply LinearMap.ext
  intro V
  apply cliffordIota_injective
  rw [cliffordIota_spinVectorLinear]
  simp

theorem spinVectorLinear_mul (g h : ComplexSpin44) :
    spinVectorLinear (g * h) = spinVectorLinear g * spinVectorLinear h := by
  apply LinearMap.ext
  intro V
  apply cliffordIota_injective
  change CliffordAlgebra.ι vectorQuadratic (spinVectorLinear (g * h) V) =
    CliffordAlgebra.ι vectorQuadratic
      (spinVectorLinear g (spinVectorLinear h V))
  rw [cliffordIota_spinVectorLinear,
    cliffordIota_spinVectorLinear, cliffordIota_spinVectorLinear]
  simp only [map_mul]
  exact mul_smul _ _ _

/-- The canonical vector representation of the complex spin group. -/
def complexSpinVectorRepresentation :
    ComplexSpin44 →* LinearMap.GeneralLinearGroup ℂ Vector8 where
  toFun g :=
    { val := spinVectorLinear g
      inv := spinVectorLinear g⁻¹
      val_inv := by
        rw [← spinVectorLinear_mul, mul_inv_cancel, spinVectorLinear_one]
      inv_val := by
        rw [← spinVectorLinear_mul, inv_mul_cancel, spinVectorLinear_one] }
  map_one' := by
    apply Units.ext
    exact spinVectorLinear_one
  map_mul' g h := by
    apply Units.ext
    exact spinVectorLinear_mul g h

@[simp] theorem complexSpinVectorRepresentation_apply
    (g : ComplexSpin44) (V : Vector8) :
    (((complexSpinVectorRepresentation g :
      LinearMap.GeneralLinearGroup ℂ Vector8) : Module.End ℂ Vector8) V) =
      spinVectorLinear g V := rfl

/-! ## Gamma covariance and orthogonality -/

/-- Spin conjugation of Clifford generators, written without the `ConjAct`
type alias. -/
theorem cliffordIota_spinVector_conjugate
    (g : ComplexSpin44) (V : Vector8) :
    CliffordAlgebra.ι vectorQuadratic (spinVectorLinear g V) =
      (g : CliffordAlgebra vectorQuadratic) *
        CliffordAlgebra.ι vectorQuadratic V *
        (↑((spinGroup.toUnits g)⁻¹) :
          CliffordAlgebra vectorQuadratic) := by
  rw [cliffordIota_spinVectorLinear]
  rfl

/-- The Dirac gamma operators transform by the same inner conjugation as the
Clifford generators. -/
theorem diracGamma_spinVector_conjugate
    (g : ComplexSpin44) (V : Vector8) :
    diracGamma (spinVectorLinear g V) =
      (((complexSpinDiracRepresentation g : DiracGL) :
          Module.End ℂ DiracSpinor16) *
        diracGamma V *
        (((complexSpinDiracRepresentation g : DiracGL)⁻¹ : DiracGL) :
          Module.End ℂ DiracSpinor16)) := by
  have h := congrArg zornCliffordRepresentation
    (cliffordIota_spinVector_conjugate g V)
  simpa only [zornCliffordRepresentation_ι, map_mul,
    complexSpinDiracRepresentation_val] using h

/-- Intertwining form of gamma covariance. -/
theorem complexSpinDirac_gamma_intertwines
    (g : ComplexSpin44) (V : Vector8) (Ψ : DiracSpinor16) :
    (((complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) (diracGamma V Ψ)) =
      diracGamma (spinVectorLinear g V)
        (((complexSpinDiracRepresentation g : DiracGL) :
          Module.End ℂ DiracSpinor16) Ψ) := by
  have h := LinearMap.congr_fun (diracGamma_spinVector_conjugate g V)
    (((complexSpinDiracRepresentation g : DiracGL) :
      Module.End ℂ DiracSpinor16) Ψ)
  let U : DiracGL := complexSpinDiracRepresentation g
  have hinv : ((U⁻¹ : DiracGL) : Module.End ℂ DiracSpinor16)
      (((U : DiracGL) : Module.End ℂ DiracSpinor16) Ψ) = Ψ := by
    have hm : (((U⁻¹ : DiracGL) : Module.End ℂ DiracSpinor16) *
        ((U : DiracGL) : Module.End ℂ DiracSpinor16)) = 1 := U.inv_val
    exact LinearMap.congr_fun hm Ψ
  change ((U : DiracGL) : Module.End ℂ DiracSpinor16)
      (diracGamma V Ψ) =
    diracGamma (spinVectorLinear g V)
      (((U : DiracGL) : Module.End ℂ DiracSpinor16) Ψ)
  change diracGamma (spinVectorLinear g V)
      (((U : DiracGL) : Module.End ℂ DiracSpinor16) Ψ) =
    ((U : DiracGL) : Module.End ℂ DiracSpinor16)
      (diracGamma V
        (((U⁻¹ : DiracGL) : Module.End ℂ DiracSpinor16)
          (((U : DiracGL) : Module.End ℂ DiracSpinor16) Ψ))) at h
  rw [hinv] at h
  simpa only [] using h.symm

/-- Scalar endomorphisms on the nonzero Dirac carrier detect their scalar. -/
theorem algebraMap_end_injective :
    Function.Injective
      (algebraMap ℂ (Module.End ℂ DiracSpinor16)) := by
  intro c d h
  have happ := LinearMap.congr_fun h (identitySpinorPlus, 0)
  have hfst := congrArg Prod.fst happ
  change c • identitySpinorPlus = d • identitySpinorPlus at hfst
  have hval := congrArg (fun S : SpinorPlus8 => S.val.a) hfst
  simpa [identitySpinorPlus, I_zorn, copy_smul_val, zornSmul] using hval

/-- The spin-induced vector action preserves the canonical Zorn quadratic
form, so its image lies in the complex orthogonal group of the split form. -/
theorem vectorQuadratic_spinVectorLinear
    (g : ComplexSpin44) (V : Vector8) :
    vectorQuadratic (spinVectorLinear g V) = vectorQuadratic V := by
  apply algebraMap_end_injective
  rw [← diracGamma_sq, ← diracGamma_sq]
  rw [diracGamma_spinVector_conjugate]
  let A := ((complexSpinDiracRepresentation g : DiracGL) :
    Module.End ℂ DiracSpinor16)
  let Ainv := ((complexSpinDiracRepresentation g⁻¹ : DiracGL) :
    Module.End ℂ DiracSpinor16)
  change (A * diracGamma V * Ainv) * (A * diracGamma V * Ainv) =
    diracGamma V * diracGamma V
  have hright : Ainv * A = 1 := by
    change (((complexSpinDiracRepresentation g⁻¹ : DiracGL) *
      complexSpinDiracRepresentation g : DiracGL) :
        Module.End ℂ DiracSpinor16) = 1
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hleft : A * Ainv = 1 := by
    change (((complexSpinDiracRepresentation g : DiracGL) *
      complexSpinDiracRepresentation g⁻¹ : DiracGL) :
        Module.End ℂ DiracSpinor16) = 1
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    (A * diracGamma V * Ainv) * (A * diracGamma V * Ainv) =
        A * diracGamma V * (Ainv * A) * diracGamma V * Ainv := by
          noncomm_ring
    _ = A * (diracGamma V * diracGamma V) * Ainv := by
          rw [hright]
          simp [mul_assoc]
    _ = A * algebraMap ℂ (Module.End ℂ DiracSpinor16)
          (vectorQuadratic V) * Ainv := by
          rw [diracGamma_sq]
    _ = algebraMap ℂ (Module.End ℂ DiracSpinor16)
          (vectorQuadratic V) * (A * Ainv) := by
          simp [Algebra.commutes, mul_assoc]
    _ = diracGamma V * diracGamma V := by
          rw [hleft, mul_one, diracGamma_sq]

/-! ## Compatibility with the two half-spin blocks -/

/-- Positive-to-negative Clifford multiplication is equivariant for the
vector and two half-spin representations extracted from the same spin
element. -/
theorem complexSpin_cliffordPlus_equivariant
    (g : ComplexSpin44) (V : Vector8) (S : SpinorPlus8) :
    spinorMinusAct (complexSpinMinusRepresentation g)
        (cliffordPlus V S) =
      cliffordPlus (spinVectorLinear g V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S) := by
  have h := complexSpinDirac_gamma_intertwines g V (S, 0)
  rw [complexSpinDirac_blocks, complexSpinDirac_blocks] at h
  exact congrArg Prod.snd h

/-- Negative-to-positive Clifford multiplication is equivariant for the
same three representations. -/
theorem complexSpin_cliffordMinus_equivariant
    (g : ComplexSpin44) (V : Vector8) (C : SpinorMinus8) :
    spinorPlusAct (complexSpinPlusRepresentation g)
        (cliffordMinus V C) =
      cliffordMinus (spinVectorLinear g V)
        (spinorMinusAct (complexSpinMinusRepresentation g) C) := by
  have h := complexSpinDirac_gamma_intertwines g V (0, C)
  rw [complexSpinDirac_blocks, complexSpinDirac_blocks] at h
  exact congrArg Prod.fst h

/-- The three canonical representations satisfy the defining pair of
Clifford/triality covariance equations. -/
theorem complexSpin_vector_halfSpin_triality_bridge
    (g : ComplexSpin44) (V : Vector8)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    vectorQuadratic (spinVectorLinear g V) = vectorQuadratic V ∧
    spinorMinusAct (complexSpinMinusRepresentation g)
        (cliffordPlus V S) =
      cliffordPlus (spinVectorLinear g V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S) ∧
    spinorPlusAct (complexSpinPlusRepresentation g)
        (cliffordMinus V C) =
      cliffordMinus (spinVectorLinear g V)
        (spinorMinusAct (complexSpinMinusRepresentation g) C) := by
  exact ⟨vectorQuadratic_spinVectorLinear g V,
    complexSpin_cliffordPlus_equivariant g V S,
    complexSpin_cliffordMinus_equivariant g V C⟩

/-! ## The invariant chiral bilinear form -/

/-- Polar pairing on any typed Zorn copy. -/
def copyPolar {s : TrialitySector} (X Y : ZornCopy s) : ℂ :=
  zornPolar X.val Y.val

/-- The split Dirac pairing: positive polar form minus negative polar form. -/
def diracPolar (Ψ Φ : DiracSpinor16) : ℂ :=
  copyPolar Ψ.1 Φ.1 - copyPolar Ψ.2 Φ.2

theorem copyPolar_smul_left {s : TrialitySector}
    (c : ℂ) (X Y : ZornCopy s) :
    copyPolar (c • X) Y = c * copyPolar X Y := by
  simp [copyPolar, copy_smul_val, zornPolar, zornNorm, zornAdd,
    zornSmul, dot3]
  ring

theorem copyPolar_smul_right {s : TrialitySector}
    (c : ℂ) (X Y : ZornCopy s) :
    copyPolar X (c • Y) = c * copyPolar X Y := by
  simp [copyPolar, copy_smul_val, zornPolar, zornNorm, zornAdd,
    zornSmul, dot3]
  ring

theorem copyPolar_add_left {s : TrialitySector}
    (X Y Z : ZornCopy s) :
    copyPolar (X + Y) Z = copyPolar X Z + copyPolar Y Z := by
  simp [copyPolar, copy_add_val, zornPolar, zornNorm, zornAdd, dot3]
  ring

theorem copyPolar_add_right {s : TrialitySector}
    (X Y Z : ZornCopy s) :
    copyPolar X (Y + Z) = copyPolar X Y + copyPolar X Z := by
  simp [copyPolar, copy_add_val, zornPolar, zornNorm, zornAdd, dot3]
  ring

theorem copyPolar_neg_left {s : TrialitySector} (X Y : ZornCopy s) :
    copyPolar (-X) Y = -copyPolar X Y := by
  rw [show -X = (-1 : ℂ) • X by simp, copyPolar_smul_left]
  simp

theorem copyPolar_neg_right {s : TrialitySector} (X Y : ZornCopy s) :
    copyPolar X (-Y) = -copyPolar X Y := by
  rw [show -Y = (-1 : ℂ) • Y by simp, copyPolar_smul_right]
  simp

@[simp] theorem copyPolar_zero_left {s : TrialitySector} (Y : ZornCopy s) :
    copyPolar 0 Y = 0 := by
  have h := copyPolar_smul_left (0 : ℂ) Y Y
  simpa using h

@[simp] theorem copyPolar_zero_right {s : TrialitySector} (X : ZornCopy s) :
    copyPolar X 0 = 0 := by
  have h := copyPolar_smul_right (0 : ℂ) X X
  simpa using h

/-- The two chiral Clifford actions are adjoint for the polar Zorn forms. -/
theorem cliffordPlus_cliffordMinus_adjoint
    (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) :
    copyPolar (cliffordPlus V S) C =
      copyPolar S (cliffordMinus V C) := by
  simp [copyPolar, cliffordPlus, cliffordMinus, zornPolar, zornNorm,
    zornAdd, zornMul, zornConj, dot3, cross3]
  ring

theorem cliffordMinus_cliffordPlus_adjoint
    (V : Vector8) (C : SpinorMinus8) (S : SpinorPlus8) :
    copyPolar (cliffordMinus V C) S =
      copyPolar C (cliffordPlus V S) := by
  simp [copyPolar, cliffordPlus, cliffordMinus, zornPolar, zornNorm,
    zornAdd, zornMul, zornConj, dot3, cross3]
  ring

/-- Gamma generators are skew-adjoint for the split Dirac polar form. -/
theorem diracPolar_gamma_skew
    (V : Vector8) (Ψ Φ : DiracSpinor16) :
    diracPolar (diracGamma V Ψ) Φ =
      -diracPolar Ψ (diracGamma V Φ) := by
  rcases Ψ with ⟨S, C⟩
  rcases Φ with ⟨T, D⟩
  change copyPolar (cliffordMinus V C) T -
      copyPolar (cliffordPlus V S) D =
    -(copyPolar S (cliffordMinus V D) -
      copyPolar C (cliffordPlus V T))
  rw [cliffordMinus_cliffordPlus_adjoint,
    cliffordPlus_cliffordMinus_adjoint]
  ring

theorem diracPolar_smul_left (c : ℂ)
    (Ψ Φ : DiracSpinor16) :
    diracPolar (c • Ψ) Φ = c * diracPolar Ψ Φ := by
  rcases Ψ with ⟨S, C⟩
  rcases Φ with ⟨T, D⟩
  simp [diracPolar, copyPolar_smul_left, mul_sub]

theorem diracPolar_smul_right (c : ℂ)
    (Ψ Φ : DiracSpinor16) :
    diracPolar Ψ (c • Φ) = c * diracPolar Ψ Φ := by
  rcases Ψ with ⟨S, C⟩
  rcases Φ with ⟨T, D⟩
  simp [diracPolar, copyPolar_smul_right, mul_sub]

theorem diracPolar_add_left (Ψ Χ Φ : DiracSpinor16) :
    diracPolar (Ψ + Χ) Φ = diracPolar Ψ Φ + diracPolar Χ Φ := by
  rcases Ψ with ⟨S, C⟩
  rcases Χ with ⟨T, D⟩
  rcases Φ with ⟨U, E⟩
  simp [diracPolar, copyPolar_add_left]
  ring

theorem diracPolar_add_right (Ψ Φ Χ : DiracSpinor16) :
    diracPolar Ψ (Φ + Χ) = diracPolar Ψ Φ + diracPolar Ψ Χ := by
  rcases Ψ with ⟨S, C⟩
  rcases Φ with ⟨T, D⟩
  rcases Χ with ⟨U, E⟩
  simp [diracPolar, copyPolar_add_right]
  ring

theorem diracPolar_neg_right (Ψ Φ : DiracSpinor16) :
    diracPolar Ψ (-Φ) = -diracPolar Ψ Φ := by
  rw [show -Φ = (-1 : ℂ) • Φ by simp, diracPolar_smul_right]
  simp

/-- Clifford conjugation is represented by adjunction for the split Dirac
polar form.  This is the invariant-form theorem needed to promote the three
spin actions to a related triple. -/
theorem diracPolar_clifford_star
    (a : CliffordAlgebra vectorQuadratic) (Ψ Φ : DiracSpinor16) :
    diracPolar (zornCliffordRepresentation a Ψ) Φ =
      diracPolar Ψ (zornCliffordRepresentation (star a) Φ) := by
  induction a using CliffordAlgebra.induction generalizing Ψ Φ with
  | algebraMap r =>
      rw [AlgHom.commutes, CliffordAlgebra.star_algebraMap,
        AlgHom.commutes]
      change diracPolar (r • Ψ) Φ = diracPolar Ψ (r • Φ)
      rw [diracPolar_smul_left, diracPolar_smul_right]
  | ι V =>
      rw [zornCliffordRepresentation_ι, CliffordAlgebra.star_ι,
        map_neg, zornCliffordRepresentation_ι]
      rw [diracPolar_gamma_skew]
      exact (diracPolar_neg_right Ψ (diracGamma V Φ)).symm
  | mul a b ha hb =>
      rw [map_mul, star_mul, map_mul]
      change diracPolar
          (zornCliffordRepresentation a
            (zornCliffordRepresentation b Ψ)) Φ = _
      rw [ha, hb]
      rfl
  | add a b ha hb =>
      rw [map_add, star_add, map_add]
      change diracPolar
          (zornCliffordRepresentation a Ψ +
            zornCliffordRepresentation b Ψ) Φ = _
      rw [diracPolar_add_left, ha, hb, LinearMap.add_apply,
        diracPolar_add_right]

/-- Spin operators preserve the split Dirac polar form because their Clifford
inverse is their Clifford conjugate. -/
theorem diracPolar_complexSpin_invariant
    (g : ComplexSpin44) (Ψ Φ : DiracSpinor16) :
    diracPolar
        (((complexSpinDiracRepresentation g : DiracGL) :
          Module.End ℂ DiracSpinor16) Ψ)
        (((complexSpinDiracRepresentation g : DiracGL) :
          Module.End ℂ DiracSpinor16) Φ) =
      diracPolar Ψ Φ := by
  rw [complexSpinDiracRepresentation_val]
  rw [diracPolar_clifford_star]
  have hstar : star (g : CliffordAlgebra vectorQuadratic) =
      (↑(g⁻¹) : CliffordAlgebra vectorQuadratic) := rfl
  rw [hstar]
  have hinv :
      zornCliffordRepresentation
          (↑(g⁻¹) : CliffordAlgebra vectorQuadratic)
          (zornCliffordRepresentation
            (g : CliffordAlgebra vectorQuadratic) Φ) = Φ := by
    have hm :
        zornCliffordRepresentation
            (↑(g⁻¹) : CliffordAlgebra vectorQuadratic) *
      zornCliffordRepresentation
            (g : CliffordAlgebra vectorQuadratic) = 1 := by
      rw [← map_mul]
      have hg :
          (↑(g⁻¹) : CliffordAlgebra vectorQuadratic) *
            (g : CliffordAlgebra vectorQuadratic) = 1 :=
        spinGroup.coe_star_mul_self g
      rw [hg, map_one]
    exact LinearMap.congr_fun hm Φ
  rw [hinv]

theorem copyPolar_self {s : TrialitySector} (X : ZornCopy s) :
    copyPolar X X = 2 * zornNorm X.val := by
  simp [copyPolar, zornPolar, zornNorm, zornAdd, dot3]
  ring

/-- The positive half-spin block preserves its canonical Zorn norm. -/
theorem spinorPlusNorm_complexSpinPlus
    (g : ComplexSpin44) (S : SpinorPlus8) :
    spinorPlusNorm
        (spinorPlusAct (complexSpinPlusRepresentation g) S) =
      spinorPlusNorm S := by
  have h := diracPolar_complexSpin_invariant g (S, 0) (S, 0)
  rw [complexSpinDirac_blocks] at h
  simp [spinorMinusAct] at h
  simp only [diracPolar, copyPolar_zero_left, sub_zero] at h
  change copyPolar
      (spinorPlusAct (complexSpinPlusRepresentation g) S)
      (spinorPlusAct (complexSpinPlusRepresentation g) S) =
    copyPolar S S at h
  rw [copyPolar_self, copyPolar_self] at h
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)) h

/-- The negative half-spin block preserves its canonical Zorn norm. -/
theorem spinorMinusNorm_complexSpinMinus
    (g : ComplexSpin44) (C : SpinorMinus8) :
    spinorMinusNorm
        (spinorMinusAct (complexSpinMinusRepresentation g) C) =
      spinorMinusNorm C := by
  have h := diracPolar_complexSpin_invariant g (0, C) (0, C)
  rw [complexSpinDirac_blocks] at h
  simp [spinorPlusAct] at h
  simp only [diracPolar, copyPolar_zero_left, zero_sub] at h
  change -copyPolar
      (spinorMinusAct (complexSpinMinusRepresentation g) C)
      (spinorMinusAct (complexSpinMinusRepresentation g) C) =
    -copyPolar C C at h
  have hp : copyPolar
      (spinorMinusAct (complexSpinMinusRepresentation g) C)
      (spinorMinusAct (complexSpinMinusRepresentation g) C) =
      copyPolar C C := neg_injective h
  rw [copyPolar_self, copyPolar_self] at hp
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)) hp

theorem spinorMinusPolar_complexSpinMinus
    (g : ComplexSpin44) (C D : SpinorMinus8) :
    copyPolar (spinorMinusAct (complexSpinMinusRepresentation g) C)
        (spinorMinusAct (complexSpinMinusRepresentation g) D) =
      copyPolar C D := by
  have h := diracPolar_complexSpin_invariant g (0, C) (0, D)
  rw [complexSpinDirac_blocks] at h
  simp [spinorPlusAct] at h
  simp only [diracPolar, copyPolar_zero_left, zero_sub] at h
  exact neg_injective h

/-! ## Conjugate-dual negative action for Cartan's trilinear form -/

/-- Zorn conjugation on a typed copy, as a linear involution. -/
def copyConjLinearEquiv (s : TrialitySector) :
    ZornCopy s ≃ₗ[ℂ] ZornCopy s where
  toFun X := ⟨zornConj X.val⟩
  invFun X := ⟨zornConj X.val⟩
  left_inv X := by
    apply ZornCopy.ext
    exact zornConj_conj X.val
  right_inv X := by
    apply ZornCopy.ext
    exact zornConj_conj X.val
  map_add' X Y := by
    apply ZornCopy.ext
    change zornConj (X + Y).val =
      (⟨zornConj X.val⟩ + ⟨zornConj Y.val⟩ : ZornCopy s).val
    rw [copy_add_val, copy_add_val, zornConj_add]
  map_smul' c X := by
    apply ZornCopy.ext
    change zornConj (c • X).val =
      (c • (⟨zornConj X.val⟩ : ZornCopy s)).val
    rw [copy_smul_val, copy_smul_val, zornConj_smul]

@[simp] theorem copyConjLinearEquiv_apply {s : TrialitySector}
    (X : ZornCopy s) :
    (copyConjLinearEquiv s X).val = zornConj X.val := rfl

@[simp] theorem copyConjLinearEquiv_sq {s : TrialitySector}
    (X : ZornCopy s) :
    copyConjLinearEquiv s (copyConjLinearEquiv s X) = X := by
  apply ZornCopy.ext
  exact zornConj_conj X.val

/-- Zorn conjugation packaged as an invertible negative-semispinor map. -/
def spinorMinusConjUnit : SpinorMinusGL :=
  { val := (copyConjLinearEquiv .spinorMinus).toLinearMap
    inv := (copyConjLinearEquiv .spinorMinus).toLinearMap
    val_inv := by
      apply LinearMap.ext
      exact copyConjLinearEquiv_sq
    inv_val := by
      apply LinearMap.ext
      exact copyConjLinearEquiv_sq }

@[simp] theorem spinorMinusConjUnit_apply (C : SpinorMinus8) :
    spinorMinusAct spinorMinusConjUnit C =
      copyConjLinearEquiv .spinorMinus C := rfl

/-- The third Cartan-triality action is the conjugate-dual of the raw negative
half-spin block. -/
def complexSpinTrialityMinusRepresentation :
    ComplexSpin44 →* SpinorMinusGL where
  toFun g := spinorMinusConjUnit *
    complexSpinMinusRepresentation g * spinorMinusConjUnit⁻¹
  map_one' := by
    rw [map_one, mul_one, mul_inv_cancel]
  map_mul' g h := by
    simp only [map_mul]
    group

theorem complexSpinTrialityMinusRepresentation_apply
    (g : ComplexSpin44) (C : SpinorMinus8) :
    spinorMinusAct (complexSpinTrialityMinusRepresentation g) C =
      copyConjLinearEquiv .spinorMinus
        (spinorMinusAct (complexSpinMinusRepresentation g)
          (copyConjLinearEquiv .spinorMinus C)) := by
  rfl

/-- The trace-product pairing used by `trialityForm`. -/
def traceProductPair (C D : SpinorMinus8) : ℂ :=
  zornTrace (zornMul C.val D.val)

theorem traceProductPair_eq_copyPolar_conj (C D : SpinorMinus8) :
    traceProductPair C D =
      copyPolar C (copyConjLinearEquiv .spinorMinus D) := by
  simp [traceProductPair, copyPolar, zornTrace, zornMul, zornPolar,
    zornNorm, zornAdd, zornConj, dot3, cross3]
  ring

theorem traceProductPair_spin_invariant
    (g : ComplexSpin44) (C D : SpinorMinus8) :
    traceProductPair
        (spinorMinusAct (complexSpinMinusRepresentation g) C)
        (spinorMinusAct (complexSpinTrialityMinusRepresentation g) D) =
      traceProductPair C D := by
  rw [traceProductPair_eq_copyPolar_conj,
    complexSpinTrialityMinusRepresentation_apply,
    copyConjLinearEquiv_sq,
    spinorMinusPolar_complexSpinMinus,
    traceProductPair_eq_copyPolar_conj]

/-- The conjugate-dual negative action still preserves the Zorn norm. -/
theorem spinorMinusNorm_complexSpinTrialityMinus
    (g : ComplexSpin44) (C : SpinorMinus8) :
    spinorMinusNorm
        (spinorMinusAct (complexSpinTrialityMinusRepresentation g) C) =
      spinorMinusNorm C := by
  rw [complexSpinTrialityMinusRepresentation_apply]
  change zornNorm (zornConj
      (spinorMinusAct (complexSpinMinusRepresentation g)
        (copyConjLinearEquiv .spinorMinus C)).val) = zornNorm C.val
  rw [zornNorm_conj]
  change spinorMinusNorm
      (spinorMinusAct (complexSpinMinusRepresentation g)
        (copyConjLinearEquiv .spinorMinus C)) = spinorMinusNorm C
  rw [spinorMinusNorm_complexSpinMinus]
  exact zornNorm_conj C.val

/-! ## Promotion to the canonical related-triples group -/

theorem vectorNorm_complexSpinVector
    (g : ComplexSpin44) (V : Vector8) :
    vectorNorm (vectorAct (complexSpinVectorRepresentation g) V) =
      vectorNorm V := by
  change vectorNorm (spinVectorLinear g V) = vectorNorm V
  rw [← vectorQuadratic_apply, vectorQuadratic_spinVectorLinear,
    vectorQuadratic_apply]

theorem trialityForm_eq_traceProductPair
    (V : Vector8) (S : SpinorPlus8) (C : SpinorMinus8) :
    trialityForm V S C = traceProductPair (cliffordPlus V S) C := rfl

/-- The spin actions preserve Cartan's Zorn trilinear form when the third
component is taken in its conjugate-dual realization. -/
theorem trialityForm_complexSpin_invariant
    (g : ComplexSpin44) (V : Vector8)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    trialityForm
        (vectorAct (complexSpinVectorRepresentation g) V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S)
        (spinorMinusAct (complexSpinTrialityMinusRepresentation g) C) =
      trialityForm V S C := by
  rw [trialityForm_eq_traceProductPair,
    trialityForm_eq_traceProductPair]
  change traceProductPair
      (cliffordPlus (spinVectorLinear g V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S))
      (spinorMinusAct (complexSpinTrialityMinusRepresentation g) C) =
    traceProductPair (cliffordPlus V S) C
  rw [← complexSpin_cliffordPlus_equivariant]
  exact traceProductPair_spin_invariant g (cliffordPlus V S) C

/-- Ambient triple consisting of the vector, positive-half-spin, and
conjugate-dual negative-half-spin actions of one spin element. -/
def complexSpinRelatedAmbient (g : ComplexSpin44) : TrialityGL :=
  (complexSpinVectorRepresentation g,
    complexSpinPlusRepresentation g,
    complexSpinTrialityMinusRepresentation g)

theorem complexSpinRelatedAmbient_isRelated (g : ComplexSpin44) :
    IsRelatedTriple (complexSpinRelatedAmbient g) := by
  refine ⟨vectorNorm_complexSpinVector g,
    spinorPlusNorm_complexSpinPlus g,
    spinorMinusNorm_complexSpinTrialityMinus g, ?_⟩
  exact trialityForm_complexSpin_invariant g

/-- The canonical spin group maps into Cartan's related-triples group. -/
def complexSpinRelatedRepresentation :
    ComplexSpin44 →* CartanTrialityGroup where
  toFun g := ⟨complexSpinRelatedAmbient g,
    complexSpinRelatedAmbient_isRelated g⟩
  map_one' := by
    apply Subtype.ext
    simp [complexSpinRelatedAmbient]
  map_mul' g h := by
    apply Subtype.ext
    simp [complexSpinRelatedAmbient]

theorem complexSpinRelatedRepresentation_components
    (g : ComplexSpin44) :
    (complexSpinRelatedRepresentation g).1.1 =
        complexSpinVectorRepresentation g ∧
      (complexSpinRelatedRepresentation g).1.2.1 =
        complexSpinPlusRepresentation g ∧
      (complexSpinRelatedRepresentation g).1.2.2 =
        complexSpinTrialityMinusRepresentation g := by
  exact ⟨rfl, rfl, rfl⟩

/-- Capstone: one spin element now simultaneously supplies an orthogonal
vector action, both chiral actions, Clifford covariance, and a certified
Cartan related triple on the canonical Zorn carriers. -/
theorem canonical_spin_related_triality_closure
    (g : ComplexSpin44) (V : Vector8)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    IsRelatedTriple (complexSpinRelatedRepresentation g).1 ∧
    vectorQuadratic (spinVectorLinear g V) = vectorQuadratic V ∧
    spinorMinusAct (complexSpinMinusRepresentation g)
        (cliffordPlus V S) =
      cliffordPlus (spinVectorLinear g V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S) ∧
    trialityForm
        (vectorAct (complexSpinVectorRepresentation g) V)
        (spinorPlusAct (complexSpinPlusRepresentation g) S)
        (spinorMinusAct (complexSpinTrialityMinusRepresentation g) C) =
      trialityForm V S C := by
  exact ⟨(complexSpinRelatedRepresentation g).2,
    vectorQuadratic_spinVectorLinear g V,
    complexSpin_cliffordPlus_equivariant g V S,
    trialityForm_complexSpin_invariant g V S C⟩

/-! ## Five-graded affine conformal projective closure -/

/-- Whenever a complex spin element carries one point of the chosen real
split locus to another, its newly constructed related triple enters the
existing affine conformal and five-graded closure theorem. -/
theorem complexSpin_affine_projective_five_grade
    (g : ComplexSpin44) (x y : CanonicalZornRealSpin44.RealSplit44)
    (hxy : vectorAct (complexSpinVectorRepresentation g)
        (CanonicalZornRealSpin44.realSplit44ToVector8 x) =
      CanonicalZornRealSpin44.realSplit44ToVector8 y) :
    CanonicalZornRealSpin44.realQuadratic44 y =
        CanonicalZornRealSpin44.realQuadratic44 x ∧
    ProjectiveAffineConformalClosure55.Q55
        (ProjectiveAffineConformalClosure55.conformalEmbed44to55
          (CanonicalZornRealSpin44.realSplit44ToPAC44 y)) = 0 ∧
    relatedVectorGradePlus (complexSpinRelatedRepresentation g)
        (CanonicalZornRealSpin44.realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 := by
  exact relatedTriple_affine_projective_five_grade
    (complexSpinRelatedRepresentation g) x y hxy

/-- Full internal capstone joining spin triality, the order-three outer
triality operation, all three grade lanes, and the projective null lift. -/
theorem complexSpin_outer_triality_five_grade_projective_closure
    (g : ComplexSpin44) (x y : CanonicalZornRealSpin44.RealSplit44)
    (hxy : vectorAct (complexSpinVectorRepresentation g)
        (CanonicalZornRealSpin44.realSplit44ToVector8 x) =
      CanonicalZornRealSpin44.realSplit44ToVector8 y)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv (complexSpinRelatedRepresentation g))) =
      complexSpinRelatedRepresentation g ∧
    relatedVectorGradePlus (complexSpinRelatedRepresentation g)
        (CanonicalZornRealSpin44.realSplit44ToVector8 x) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus (complexSpinRelatedRepresentation g) S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus (complexSpinRelatedRepresentation g) C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    CanonicalZornRealSpin44.realQuadratic44 y =
      CanonicalZornRealSpin44.realQuadratic44 x ∧
    ProjectiveAffineConformalClosure55.Q55
        (ProjectiveAffineConformalClosure55.conformalEmbed44to55
          (CanonicalZornRealSpin44.realSplit44ToPAC44 y)) = 0 := by
  exact outer_triality_five_grade_projective_closure
    (complexSpinRelatedRepresentation g) x y hxy S C

end CanonicalZornSpinVectorAction

end noncomputable section
