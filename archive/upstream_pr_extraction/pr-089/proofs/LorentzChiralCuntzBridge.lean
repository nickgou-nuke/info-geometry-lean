import Mathlib
import proofs.ChiralCausalCone
import proofs.ChiralPoincareSouriauBridge
import proofs.CuntzDeformedSuperPoincare
import proofs.FierzIdentities

/-!
# Lorentz action on the chiral algebra and Cuntz-deformed super-Poincaré layer

This file keeps the Lorentz/Poincaré lift finite and algebraic:

* the chiral Lorentz spin group is the concrete matrix group `SL(2,ℂ)`;
* it acts on the chiral algebra `M₂(ℂ)` by conjugation;
* Pauli soldering turns that conjugation into an action on complexified
  four-momenta, preserving the determinant/Minkowski quadratic form;
* the chiral Fierz identity is imported as the completeness/swap theorem;
* the Cuntz-deformed super-Poincaré bracket layer is reused through its native API.

No global analytic covering theorem is claimed here.  The global group law is the
existing Lean group structure on `Matrix.SpecialLinearGroup (Fin 2) ℂ`.
-/

noncomputable section

namespace LorentzChiralCuntzBridge

open Matrix
open ChiralPoincareSouriauBridge

/-- The finite chiral Lorentz spin group used here: concrete `SL(2,ℂ)`. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- Coerce an `SL(2,ℂ)` element to its concrete `2×2` matrix. -/
def spinMatrix (g : SL2C) : M2C := (g : M2C)

@[simp] theorem spinMatrix_det (g : SL2C) : (spinMatrix g).det = 1 := by
  exact Matrix.SpecialLinearGroup.det_coe g

@[simp] theorem spinMatrix_mul (g h : SL2C) :
    spinMatrix (g * h) = spinMatrix g * spinMatrix h := rfl

@[simp] theorem spinMatrix_one : spinMatrix (1 : SL2C) = (1 : M2C) := rfl

/-- A concrete diagonal `SL(2,ℂ)` element.  The nonzero parameter is explicit. -/
def diagSL2 (a : ℂ) (ha : a ≠ 0) : SL2C :=
  ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two, ha]⟩

/-- Exponential diagonal `SL(2,ℂ)` element. -/
def expDiagSL2 (η : ℂ) : SL2C := diagSL2 (Complex.exp η) (Complex.exp_ne_zero η)

@[simp] theorem expDiagSL2_matrix (η : ℂ) :
    spinMatrix (expDiagSL2 η) = !![Complex.exp η, 0; 0, (Complex.exp η)⁻¹] := rfl

/-- Multiplication law for the explicit diagonal one-parameter subgroup. -/
theorem expDiagSL2_mul (η ξ : ℂ) :
    expDiagSL2 η * expDiagSL2 ξ = expDiagSL2 (η + ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expDiagSL2, diagSL2, Complex.exp_add, mul_comm]

/-- The identity member of the explicit diagonal subgroup. -/
theorem expDiagSL2_zero : expDiagSL2 0 = (1 : SL2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [expDiagSL2, diagSL2]

/-- Chiral Lorentz action on the matrix/chiral algebra by conjugation. -/
def chiralConjAct (g : SL2C) (X : M2C) : M2C :=
  spinMatrix g * X * spinMatrix g⁻¹

@[simp] theorem chiralConjAct_one (X : M2C) :
    chiralConjAct (1 : SL2C) X = X := by
  simp [chiralConjAct]

/-- The concrete `SL(2,ℂ)` action law on the chiral algebra. -/
theorem chiralConjAct_mul (g h : SL2C) (X : M2C) :
    chiralConjAct (g * h) X = chiralConjAct g (chiralConjAct h X) := by
  simp [chiralConjAct, mul_assoc]

/-- Conjugation is additive on the chiral algebra. -/
theorem chiralConjAct_add (g : SL2C) (X Y : M2C) :
    chiralConjAct g (X + Y) = chiralConjAct g X + chiralConjAct g Y := by
  simp [chiralConjAct, mul_add, add_mul]

/-- Conjugation is multiplicative on the chiral algebra. -/
theorem chiralConjAct_mul_matrix (g : SL2C) (X Y : M2C) :
    chiralConjAct g (X * Y) = chiralConjAct g X * chiralConjAct g Y := by
  calc
    chiralConjAct g (X * Y) = spinMatrix g * X * Y * spinMatrix g⁻¹ := by
      simp [chiralConjAct, mul_assoc]
    _ = spinMatrix g * X * (spinMatrix g⁻¹ * spinMatrix g) * Y * spinMatrix g⁻¹ := by
      rw [← spinMatrix_mul (g⁻¹) g, inv_mul_cancel, spinMatrix_one]
      simp [mul_assoc]
    _ = chiralConjAct g X * chiralConjAct g Y := by
      simp [chiralConjAct, mul_assoc]

/-- The chiral conjugation action preserves the matrix determinant. -/
theorem det_chiralConjAct (g : SL2C) (X : M2C) :
    (chiralConjAct g X).det = X.det := by
  simp [chiralConjAct, Matrix.det_mul]

/-- Recover a complexified four-momentum from an arbitrary `2×2` matrix by Pauli traces. -/
def fourMomentumOfMatrix (X : M2C) : FourMomentum where
  E := recoverE X
  px := recoverPx X
  py := recoverPy X
  pz := recoverPz X

/-- Pauli soldering and trace recovery round-trip for every `2×2` complex matrix. -/
theorem pauliMomentum_fourMomentumOfMatrix (X : M2C) :
    pauliMomentum (fourMomentumOfMatrix X) = X := by
  have hI_sq : (Complex.I : ℂ) ^ 2 = -1 := by
    rw [sq, Complex.I_mul_I]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourMomentumOfMatrix, pauliMomentum, recoverE, recoverPx, recoverPy, recoverPz,
      σ1, σ2, σ3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf
  all_goals rw [hI_sq]
  all_goals ring_nf

/-- Equality of Pauli-soldered matrices detects equality of complexified four-momenta. -/
theorem fourMomentum_ext_of_pauliMomentum_eq {P Q : FourMomentum}
    (h : pauliMomentum P = pauliMomentum Q) : P = Q := by
  cases P with
  | mk E px py pz =>
  cases Q with
  | mk E' px' py' pz' =>
    have hE : E = E' := by simpa using congrArg recoverE h
    have hpx : px = px' := by simpa using congrArg recoverPx h
    have hpy : py = py' := by simpa using congrArg recoverPy h
    have hpz : pz = pz' := by simpa using congrArg recoverPz h
    subst hE
    subst hpx
    subst hpy
    subst hpz
    rfl

/-- Addition of complexified four-momenta, kept local to avoid typeclass commitments. -/
def addFourMomentum (P Q : FourMomentum) : FourMomentum where
  E := P.E + Q.E
  px := P.px + Q.px
  py := P.py + Q.py
  pz := P.pz + Q.pz

/-- Zero complexified four-momentum, kept local to avoid typeclass commitments. -/
def zeroFourMomentum : FourMomentum where
  E := 0
  px := 0
  py := 0
  pz := 0

/-- Pauli soldering is additive for the local four-momentum addition. -/
theorem pauliMomentum_add (P Q : FourMomentum) :
    pauliMomentum (addFourMomentum P Q) = pauliMomentum P + pauliMomentum Q := by
  cases P
  cases Q
  ext i j
  fin_cases i <;> fin_cases j <;> simp [addFourMomentum, pauliMomentum] <;> ring

/-- Pauli soldering sends the local zero four-momentum to the zero matrix. -/
theorem pauliMomentum_zero : pauliMomentum zeroFourMomentum = (0 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zeroFourMomentum, pauliMomentum]

/-- The induced Lorentz action on complexified soldered four-momenta. -/
def spinLorentzAction (g : SL2C) (P : FourMomentum) : FourMomentum :=
  fourMomentumOfMatrix (chiralConjAct g (pauliMomentum P))

/-- Soldering intertwines the induced four-vector action with chiral conjugation. -/
theorem pauliMomentum_spinLorentzAction (g : SL2C) (P : FourMomentum) :
    pauliMomentum (spinLorentzAction g P) = chiralConjAct g (pauliMomentum P) := by
  exact pauliMomentum_fourMomentumOfMatrix _

/-- Identity acts as the identity on soldered complexified four-momenta. -/
theorem spinLorentzAction_one (P : FourMomentum) :
    spinLorentzAction (1 : SL2C) P = P := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  rw [pauliMomentum_spinLorentzAction]
  simp [chiralConjAct]

/-- The soldered Lorentz action obeys the group law. -/
theorem spinLorentzAction_mul (g h : SL2C) (P : FourMomentum) :
    spinLorentzAction (g * h) P = spinLorentzAction g (spinLorentzAction h P) := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  rw [pauliMomentum_spinLorentzAction, pauliMomentum_spinLorentzAction,
    pauliMomentum_spinLorentzAction]
  exact chiralConjAct_mul g h (pauliMomentum P)

/-- The soldered Lorentz action is additive on complexified four-momenta. -/
theorem spinLorentzAction_add (g : SL2C) (P Q : FourMomentum) :
    spinLorentzAction g (addFourMomentum P Q) =
      addFourMomentum (spinLorentzAction g P) (spinLorentzAction g Q) := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  rw [pauliMomentum_spinLorentzAction, pauliMomentum_add, chiralConjAct_add,
    ← pauliMomentum_spinLorentzAction, ← pauliMomentum_spinLorentzAction,
    ← pauliMomentum_add]

/-- The induced soldered action preserves the complexified Minkowski quadratic form. -/
theorem spinLorentzAction_preserves_minkowskiSq (g : SL2C) (P : FourMomentum) :
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P := by
  have hdet := det_chiralConjAct g (pauliMomentum P)
  rw [← det_pauliMomentum, pauliMomentum_spinLorentzAction, hdet, det_pauliMomentum]

/-! ## Complexified Poincaré action built over the chiral Lorentz action -/

/-- A finite complexified Poincaré element: chiral Lorentz spin element plus translation. -/
structure ChiralPoincareElement where
  Λ : SL2C
  a : FourMomentum

/-- Affine action on complexified soldered vectors: `P ↦ ΛP + a`. -/
def chiralPoincareAct (g : ChiralPoincareElement) (P : FourMomentum) : FourMomentum :=
  addFourMomentum (spinLorentzAction g.Λ P) g.a

/-- Identity complexified Poincaré element. -/
def chiralPoincareId : ChiralPoincareElement where
  Λ := 1
  a := zeroFourMomentum

/-- Semidirect-product composition: `(Λ,a)(Μ,b)=(ΛΜ, a + Λb)`. -/
def chiralPoincareComp (g h : ChiralPoincareElement) : ChiralPoincareElement where
  Λ := g.Λ * h.Λ
  a := addFourMomentum g.a (spinLorentzAction g.Λ h.a)

/-- The identity complexified Poincaré element acts as the identity. -/
theorem chiralPoincareAct_id (P : FourMomentum) :
    chiralPoincareAct chiralPoincareId P = P := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  simp [chiralPoincareAct, chiralPoincareId, addFourMomentum, zeroFourMomentum,
    spinLorentzAction_one]

/-- The affine Poincaré action obeys the semidirect-product group law. -/
theorem chiralPoincareAct_comp (g h : ChiralPoincareElement) (P : FourMomentum) :
    chiralPoincareAct (chiralPoincareComp g h) P =
      chiralPoincareAct g (chiralPoincareAct h P) := by
  apply fourMomentum_ext_of_pauliMomentum_eq
  simp only [chiralPoincareAct, chiralPoincareComp]
  rw [spinLorentzAction_mul, spinLorentzAction_add]
  repeat rw [pauliMomentum_add]
  simp [add_comm, add_left_comm]

/-- The Lorentz part of a complexified Poincaré element preserves the mass Casimir. -/
theorem chiralPoincare_lorentzPart_preserves_minkowskiSq
    (g : ChiralPoincareElement) (P : FourMomentum) :
    minkowskiSq (spinLorentzAction g.Λ P) = minkowskiSq P :=
  spinLorentzAction_preserves_minkowskiSq g.Λ P

/-! ## Cuntz-deformed transport over the same chiral Lorentz matrices -/

/-- Cuntz super-Poincaré spin transport by an `SL(2,ℂ)` chiral matrix. -/
def sl2cSpinTransport (g : SL2C) (X : M2C) : M2C :=
  CuntzDeformedSuperPoincare.spinTransport (spinMatrix g) (spinMatrix g⁻¹) X

/-- The Cuntz spin transport is exactly the chiral conjugation action. -/
theorem sl2cSpinTransport_eq_chiralConjAct (g : SL2C) (X : M2C) :
    sl2cSpinTransport g X = chiralConjAct g X := rfl

/-- The transported operator-valued super-Poincaré relation over `SL(2,ℂ)`. -/
theorem sl2c_transportedRelation_holds
    (g : SL2C) (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation) :
    CuntzDeformedSuperPoincare.transportedRelation
      (spinMatrix g) (spinMatrix g⁻¹) S :=
  CuntzDeformedSuperPoincare.transportedRelation_holds (spinMatrix g) (spinMatrix g⁻¹) S

/-! ## Weyl/chiral Lorentz generators in the `2×2` representation -/

/-- Rotations in the left Weyl/chiral spin representation. -/
def Jx : M2C := (1 / 2 : ℂ) • σ1
def Jy : M2C := (1 / 2 : ℂ) • σ2
def Jz : M2C := (1 / 2 : ℂ) • σ3

/-- Boosts in the left Weyl/chiral spin representation. -/
def Kx : M2C := Complex.I • Jx
def Ky : M2C := Complex.I • Jy
def Kz : M2C := Complex.I • Jz

def commM (A B : M2C) : M2C := A * B - B * A

theorem comm_Jx_Jy : commM Jx Jy = Complex.I • Jz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commM, Jx, Jy, Jz, σ1, σ2, σ3, Matrix.smul_apply, Matrix.sub_apply] <;>
    ring_nf

theorem comm_Jx_Ky : commM Jx Ky = Complex.I • Kz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commM, Jx, Ky, Kz, Jy, Jz, σ1, σ2, σ3, Matrix.smul_apply,
      Matrix.sub_apply] <;>
    ring_nf

theorem comm_Kx_Ky : commM Kx Ky = -Complex.I • Jz := by
  have hI_sq : (Complex.I : ℂ) ^ 2 = -1 := by
    rw [sq, Complex.I_mul_I]
  have hI_cube : (Complex.I : ℂ) ^ 3 = -Complex.I := by
    calc
      (Complex.I : ℂ) ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = (-1) * Complex.I := by rw [hI_sq]
      _ = -Complex.I := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commM, Kx, Ky, Jx, Jy, Jz, σ1, σ2, σ3, Matrix.smul_apply,
      Matrix.sub_apply] <;>
    ring_nf
  all_goals rw [hI_cube]
  all_goals ring_nf

/-- Proposition form of the imported Fierz completeness theorem. -/
def chiralFierzStatement : Prop :=
    (1/2 : ℂ) • (Matrix.kroneckerMap (fun (a b : ℂ) => a * b)
        (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      Matrix.kroneckerMap (fun (a b : ℂ) => a * b)
        ChiralCausalCone.σ3c ChiralCausalCone.σ3c) +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b)
      ChiralCausalCone.σPlus ChiralCausalCone.σMinus +
    Matrix.kroneckerMap (fun (a b : ℂ) => a * b)
      ChiralCausalCone.σMinus ChiralCausalCone.σPlus = FierzIdentities.Swap

/-- The finite Lorentz/chiral/Cuntz synthesis theorem. -/
theorem lorentz_chiral_cuntz_synthesis (g h : SL2C) (P : FourMomentum)
    (β : ℂ) (x y : M2C) :
    chiralConjAct (g * h) (pauliMomentum P) =
      chiralConjAct g (chiralConjAct h (pauliMomentum P)) ∧
    spinLorentzAction (g * h) P = spinLorentzAction g (spinLorentzAction h P) ∧
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P ∧
    commM Jx Jy = Complex.I • Jz ∧
    commM Jx Ky = Complex.I • Kz ∧
    commM Kx Ky = -Complex.I • Jz ∧
    chiralFierzStatement ∧
    SupergradedCuntzBdG.affineSuperBracket β SupergradedCuntzBdG.Z2Parity.odd
        SupergradedCuntzBdG.Z2Parity.odd x y =
      (1 - β) • SupergradedCuntzBdG.lieBracket x y +
        β • SupergradedCuntzBdG.jordanProduct x y := by
  constructor
  · simpa using chiralConjAct_mul g h (pauliMomentum P)
  constructor
  · simpa using spinLorentzAction_mul g h P
  constructor
  · simpa using spinLorentzAction_preserves_minkowskiSq g P
  constructor
  · simpa using comm_Jx_Jy
  constructor
  · simpa using comm_Jx_Ky
  constructor
  · simpa using comm_Kx_Ky
  constructor
  · exact FierzIdentities.chiral_fierz_identity
  · simpa using CuntzDeformedSuperPoincare.cuntzDeformed_odd_odd_lie_jordan_split β x y

/-- Full finite synthesis: Lorentz action on chiral matrices, soldered vector action,
Fierz completeness, complexified Poincaré semidirect product, and Cuntz-deformed
operator super-Poincaré transport. -/
theorem lorentz_chiral_poincare_cuntz_synthesis
    (g h : SL2C) (G H : ChiralPoincareElement) (P : FourMomentum)
    (S : CuntzDeformedSuperPoincare.ChiralOperatorPresentation)
    (β : ℂ) (x y : M2C) :
    chiralConjAct (g * h) (pauliMomentum P) =
      chiralConjAct g (chiralConjAct h (pauliMomentum P)) ∧
    spinLorentzAction (g * h) P = spinLorentzAction g (spinLorentzAction h P) ∧
    chiralPoincareAct (chiralPoincareComp G H) P =
      chiralPoincareAct G (chiralPoincareAct H P) ∧
    minkowskiSq (spinLorentzAction g P) = minkowskiSq P ∧
    chiralFierzStatement ∧
    CuntzDeformedSuperPoincare.transportedRelation
      (spinMatrix g) (spinMatrix g⁻¹) S ∧
    SupergradedCuntzBdG.affineSuperBracket β SupergradedCuntzBdG.Z2Parity.odd
        SupergradedCuntzBdG.Z2Parity.odd x y =
      (1 - β) • SupergradedCuntzBdG.lieBracket x y +
        β • SupergradedCuntzBdG.jordanProduct x y := by
  constructor
  · simpa using chiralConjAct_mul g h (pauliMomentum P)
  constructor
  · simpa using spinLorentzAction_mul g h P
  constructor
  · simpa using chiralPoincareAct_comp G H P
  constructor
  · simpa using spinLorentzAction_preserves_minkowskiSq g P
  constructor
  · exact FierzIdentities.chiral_fierz_identity
  constructor
  · simpa using sl2c_transportedRelation_holds g S
  · simpa using CuntzDeformedSuperPoincare.cuntzDeformed_odd_odd_lie_jordan_split β x y

end LorentzChiralCuntzBridge

end noncomputable section
