/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.OperatorAlgebra.PeirceBdGOperatorBridge
import InfoGeometry.Algebra.SupergradedBracket

/-!
# Split-Clifford realization of the Peirce Möbius group

The normalized Witt pair in the native real `Cl(1,1)` matrix carrier is a
Peirce pair for `Pminus`.  Consequently the Bruhat operator built from that
pair has the explicit two-sided group inverse supplied by the Peirce
unipotent calculus.  Its conjugation action is therefore an actual operator
group action, without introducing a fractional expression with an
uncontrolled operator denominator.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordSplitMobiusBridge

open InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine

abbrev M2R := InfoGeometry.Clifford.Cl11ProjectiveMobiusBridge.M2R

/-- The Clifford upper Witt generator as an upper Peirce corner. -/
theorem wittUpper_is_peirce_cone :
    conePlus Pminus b = b := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conePlus, b, e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Clifford lower Witt generator as a lower Peirce corner. -/
theorem wittLower_is_peirce_cone :
    coneMinus Pminus bdag = bdag := by
  rw [Pminus_eq_first_coordinate_projector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneMinus, bdag, e0, e1, Matrix.mul_apply, Fin.sum_univ_two]

/-- In this normalized split-Clifford representation, the Tetraktys vectors
are the two generating Clifford vectors, its quadratic element is the unit,
and its bivector is the Peirce grading. -/
theorem witt_tetraktys_identification :
    genPhi Pminus b bdag = e0 ∧
    genJ Pminus b bdag = e1 ∧
    genV Pminus b bdag = 1 ∧
    genSig Pminus b bdag = invS Pminus := by
  have hUp := wittUpper_is_peirce_cone
  have hDown := wittLower_is_peirce_cone
  have hsum : b + bdag = e0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, bdag, e0, e1] <;> norm_num
  have hdiff : b - bdag = e1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, bdag, e0, e1] <;> norm_num
  have hV : b * bdag + bdag * b = 1 := b_bdag_add_bdag_b
  have hSig : b * bdag - bdag * b = invS Pminus := by
    rw [Pminus_eq_first_coordinate_projector]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, bdag, e0, e1, invS, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  constructor
  · change conePlus Pminus b + coneMinus Pminus bdag = e0
    rw [hUp, hDown, hsum]
  constructor
  · change conePlus Pminus b - coneMinus Pminus bdag = e1
    rw [hUp, hDown, hdiff]
  constructor
  · unfold genV anticomm
    rw [hUp, hDown]
    exact hV
  · unfold InfoGeometry.OperatorAlgebra.PeirceSpine.genSig
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    rw [hUp, hDown]
    exact hSig

/-- The split-Clifford Bruhat element and its explicit group inverse. -/
noncomputable def wittBruhat : M2R := (1 + b) * (1 - bdag)
noncomputable def wittBruhatInv : M2R := (1 + bdag) * (1 - b)

/-- The Clifford Bruhat element is a unit in the full noncommutative matrix
operator ring; both inverse equations are proved from Peirce nilpotence. -/
theorem wittBruhat_group_inverse :
    wittBruhat * wittBruhatInv = 1 ∧
    wittBruhatInv * wittBruhat = 1 := by
  have h := chart_bruhat_factor_mul_inv (P := Pminus) Pminus_sq b bdag
  simpa [wittBruhat, wittBruhatInv, wittUpper_is_peirce_cone,
    wittLower_is_peirce_cone] using h

/-- Möbius transport on operators is the conjugation action of the split
Clifford Bruhat unit. -/
noncomputable def wittMobiusAction (X : M2R) : M2R := wittBruhat * X * wittBruhatInv

/-- The inverse Möbius transport uses the group inverse in reverse order. -/
noncomputable def wittMobiusActionInv (X : M2R) : M2R := wittBruhatInv * X * wittBruhat

/-- The Clifford Möbius transport is an actual ring automorphism of the
operator carrier. This packages the two-sided group inverse together with
the multiplicative law needed to transport the Tetraktys and its derived
superoperators. -/
theorem wittMobiusAction_mul (X Y : M2R) :
    wittMobiusAction (X * Y) = wittMobiusAction X * wittMobiusAction Y := by
  rcases wittBruhat_group_inverse with ⟨_, h₂⟩
  unfold wittMobiusAction
  calc
    wittBruhat * (X * Y) * wittBruhatInv =
        wittBruhat * X * (wittBruhatInv * wittBruhat) * Y * wittBruhatInv := by
          rw [h₂]
          noncomm_ring
    _ = (wittBruhat * X * wittBruhatInv) *
          (wittBruhat * Y * wittBruhatInv) := by noncomm_ring

/-- Inner transport is additive on the operator carrier. -/
theorem wittMobiusAction_add (X Y : M2R) :
    wittMobiusAction (X + Y) = wittMobiusAction X + wittMobiusAction Y := by
  unfold wittMobiusAction
  simp only [add_mul, mul_add]

/-- Forward and inverse operator Möbius transports cancel on every operator,
with no commutation assumption on the operator being transported. -/
theorem wittMobiusAction_inverse (X : M2R) :
    wittMobiusActionInv (wittMobiusAction X) = X ∧
    wittMobiusAction (wittMobiusActionInv X) = X := by
  rcases wittBruhat_group_inverse with ⟨h₁, h₂⟩
  constructor
  · unfold wittMobiusAction wittMobiusActionInv
    calc
      wittBruhatInv * (wittBruhat * X * wittBruhatInv) * wittBruhat =
          (wittBruhatInv * wittBruhat) * X *
            (wittBruhatInv * wittBruhat) := by noncomm_ring
      _ = X := by rw [h₂]; noncomm_ring
  · unfold wittMobiusAction wittMobiusActionInv
    calc
      wittBruhat * (wittBruhatInv * X * wittBruhat) * wittBruhatInv =
          (wittBruhat * wittBruhatInv) * X *
            (wittBruhat * wittBruhatInv) := by noncomm_ring
      _ = X := by rw [h₁]; noncomm_ring

noncomputable def wittMobiusRingEquiv : M2R ≃+* M2R where
  toFun := wittMobiusAction
  invFun := wittMobiusActionInv
  left_inv := fun X => (wittMobiusAction_inverse X).1
  right_inv := fun X => (wittMobiusAction_inverse X).2
  map_add' := wittMobiusAction_add
  map_mul' := wittMobiusAction_mul

/-- The Tetraktys generators are covariant under the Clifford-derived
Möbius automorphism. This is the explicit carrier bridge from the split
Clifford group element to the existing Peirce operator basis. -/
theorem wittMobiusRingEquiv_tetraktys (P A C : M2R) :
    wittMobiusRingEquiv (genPhi P A C) =
        genPhi (wittMobiusRingEquiv P) (wittMobiusRingEquiv A)
          (wittMobiusRingEquiv C) ∧
    wittMobiusRingEquiv (genJ P A C) =
        genJ (wittMobiusRingEquiv P) (wittMobiusRingEquiv A)
          (wittMobiusRingEquiv C) ∧
    wittMobiusRingEquiv (genV P A C) =
        genV (wittMobiusRingEquiv P) (wittMobiusRingEquiv A)
          (wittMobiusRingEquiv C) ∧
    wittMobiusRingEquiv (genSig P A C) =
        genSig (wittMobiusRingEquiv P) (wittMobiusRingEquiv A)
          (wittMobiusRingEquiv C) := by
  exact ⟨map_genPhi (wittMobiusRingEquiv : M2R →+* M2R) P A C,
    map_genJ (wittMobiusRingEquiv : M2R →+* M2R) P A C,
    map_genV (wittMobiusRingEquiv : M2R →+* M2R) P A C,
    map_genSig (wittMobiusRingEquiv : M2R →+* M2R) P A C⟩

/-- The operator Möbius automorphism transports the Peirce even/odd
decomposition together with its moving idempotent. This keeps the grading
attached to the transformed cut instead of treating parity as an unrelated
matrix label. -/
theorem wittMobiusRingEquiv_supergrading (P X : M2R) :
    wittMobiusRingEquiv (evenGrade P X) =
        evenGrade (wittMobiusRingEquiv P) (wittMobiusRingEquiv X) ∧
    wittMobiusRingEquiv (oddGrade P X) =
        oddGrade (wittMobiusRingEquiv P) (wittMobiusRingEquiv X) := by
  exact ⟨map_evenGrade (wittMobiusRingEquiv : M2R →+* M2R) P X,
    map_oddGrade (wittMobiusRingEquiv : M2R →+* M2R) P X⟩

/-- Homogeneous odd operators remain odd under operator Möbius transport,
with respect to the transported Peirce cut. -/
theorem wittMobiusRingEquiv_preserves_odd_homogeneous
    (P X : M2R) (hX : oddGrade P X = X) :
    oddGrade (wittMobiusRingEquiv P) (wittMobiusRingEquiv X) =
      wittMobiusRingEquiv X := by
  calc
    oddGrade (wittMobiusRingEquiv P) (wittMobiusRingEquiv X) =
        wittMobiusRingEquiv (oddGrade P X) := by
          symm
          exact map_oddGrade (wittMobiusRingEquiv : M2R →+* M2R) P X
    _ = wittMobiusRingEquiv X := congrArg wittMobiusRingEquiv hX

/-- The same Möbius automorphism preserves the explicit parity-controlled
superbracket. Combined with `wittMobiusRingEquiv_supergrading`, this gives
both transport of the actual Peirce grading and transport of its signed
bracket operation. -/
theorem wittMobiusRingEquiv_superBracket
    (p q : Bool) (X Y : M2R) :
    wittMobiusRingEquiv
        (InfoGeometry.Algebra.SupergradedBracket.superBracket p q X Y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
        (wittMobiusRingEquiv X) (wittMobiusRingEquiv Y) := by
  exact InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    (wittMobiusRingEquiv : M2R →+* M2R) p q X Y

/-- The noncommutative Tetraktys double-commutator superoperator is carried
to the same superoperator on transported generators and input. -/
theorem wittMobiusRingEquiv_derivSqPhi (P A C X : M2R) :
    wittMobiusRingEquiv (derivSqPhi P A C X) =
      derivSqPhi (wittMobiusRingEquiv P) (wittMobiusRingEquiv A)
        (wittMobiusRingEquiv C) (wittMobiusRingEquiv X) :=
  map_derivSqPhi (wittMobiusRingEquiv : M2R →+* M2R) P A C X

/-- The full Peirce-BdG mass interaction transforms covariantly under the
same inner automorphism; the mass and kinetic inputs remain arbitrary
noncommuting operators. -/
theorem wittMobiusRingEquiv_peirceBdGHamiltonian
    (P D A C : M2R) :
    wittMobiusRingEquiv
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceBdGHamiltonian
          P D A C) =
      InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceBdGHamiltonian
        (wittMobiusRingEquiv P) (wittMobiusRingEquiv D)
        (wittMobiusRingEquiv A) (wittMobiusRingEquiv C) :=
  (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.map_peirceBdGHamiltonian
    (wittMobiusRingEquiv : M2R →+* M2R) P D A C).2.2

/-- The operator cyclotomic Higgs polynomial `H⁴ - H² + 1` is invariant as
a polynomial construction under Clifford Möbius transport. This connects
the Clifford projective lane to the existing BdG/cyclotomic Higgs owner. -/
theorem wittMobiusRingEquiv_operatorCyclotomicHiggs
    (H : InfoGeometry.Physics.BdGBlock ℝ) :
    wittMobiusRingEquiv
        (InfoGeometry.Physics.operatorCyclotomicHiggs H) =
      InfoGeometry.Physics.operatorCyclotomicHiggs (wittMobiusRingEquiv H) := by
  change wittMobiusRingEquiv (H ^ 4 - H ^ 2 + 1) =
    (wittMobiusRingEquiv H) ^ 4 - (wittMobiusRingEquiv H) ^ 2 + 1
  simp only [map_add, map_sub, map_one, map_pow]

/-- The native Peirce chart conjugation and the split-Clifford Möbius action
are the same operator map on this carrier. -/
theorem wittMobiusAction_eq_peirceChart (X : M2R) :
    wittMobiusAction X = chartBruhatConj Pminus b bdag X := by
  have hUp := wittUpper_is_peirce_cone
  have hDown := wittLower_is_peirce_cone
  unfold wittMobiusAction chartBruhatConj wittBruhat wittBruhatInv
  rw [hUp, hDown]
  noncomm_ring

/-! ### The same Clifford unit on operator-valued projective pairs -/

abbrev OperatorPair2 := InfoGeometry.OperatorAlgebra.OperatorPair M2R
abbrev OperatorMatrix2 := InfoGeometry.OperatorAlgebra.OperatorMatrix M2R

/-- Upper unipotent projective-pair transport with the Clifford Bruhat
operator as its noncommutative coefficient. -/
noncomputable def wittProjectivePairMatrix : OperatorMatrix2 :=
  !![1, wittBruhat; 0, 1]

/-- The inverse projective-pair transport reverses the Clifford shear. -/
noncomputable def wittProjectivePairMatrixInv : OperatorMatrix2 :=
  !![1, -wittBruhat; 0, 1]

/-- The operator-valued projective matrix has an explicit two-sided group
inverse. -/
theorem wittProjectivePairMatrix_inverse :
    wittProjectivePairMatrix * wittProjectivePairMatrixInv = 1 ∧
    wittProjectivePairMatrixInv * wittProjectivePairMatrix = 1 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [wittProjectivePairMatrix, wittProjectivePairMatrixInv,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Package the Clifford-derived projective transport as a genuine unit in
the full matrix ring over operators. -/
noncomputable def wittProjectivePairUnit : OperatorMatrix2ˣ :=
  { val := wittProjectivePairMatrix
    inv := wittProjectivePairMatrixInv
    val_inv := wittProjectivePairMatrix_inverse.1
    inv_val := wittProjectivePairMatrix_inverse.2 }

/-- The repository's generic operator-Möbius action therefore transports
projective pairs invertibly by this split-Clifford element. -/
theorem wittProjectivePairAction_inverse (v : OperatorPair2) :
    InfoGeometry.OperatorAlgebra.operatorMobiusAction
        (↑(wittProjectivePairUnit⁻¹) : OperatorMatrix2)
        (InfoGeometry.OperatorAlgebra.operatorMobiusAction
          (↑wittProjectivePairUnit : OperatorMatrix2) v) = v ∧
    InfoGeometry.OperatorAlgebra.operatorMobiusAction
        (↑wittProjectivePairUnit : OperatorMatrix2)
        (InfoGeometry.OperatorAlgebra.operatorMobiusAction
          (↑(wittProjectivePairUnit⁻¹) : OperatorMatrix2) v) = v := by
  exact ⟨InfoGeometry.OperatorAlgebra.operatorMobiusAction_unit_inverse_left
      wittProjectivePairUnit v,
    InfoGeometry.OperatorAlgebra.operatorMobiusAction_unit_inverse_right
      wittProjectivePairUnit v⟩

/-- In the pair representation, the Clifford-derived projective transformation
is the upper unipotent shear `(x,y) ↦ (x + g*y,y)`. -/
theorem wittProjectivePairAction_shear (x y : M2R) :
    InfoGeometry.OperatorAlgebra.operatorMobiusAction
        (↑wittProjectivePairUnit : OperatorMatrix2) ![x, y] =
      ![x + wittBruhat * y, y] := by
  change InfoGeometry.OperatorAlgebra.operatorMobiusAction
      wittProjectivePairMatrix ![x, y] = ![x + wittBruhat * y, y]
  funext i
  fin_cases i <;>
    simp [InfoGeometry.OperatorAlgebra.operatorMobiusAction_apply,
      wittProjectivePairMatrix, Fin.sum_univ_two]

/-- A right affine chart is defined only when its denominator is a unit.
This records the multiplication order needed for a noncommutative fraction. -/
noncomputable def operatorRightProjectiveChart (x : M2R) (y : M2Rˣ) : M2R :=
  x * (y⁻¹ : M2R)

/-- On that unit chart, the split-Clifford projective-pair shear induces the
corresponding operator translation. No commutation between the chart value
and the Clifford Bruhat operator is required. -/
theorem wittProjectivePairAction_chart (x : M2R) (y : M2Rˣ) :
    operatorRightProjectiveChart
        (x + wittBruhat * (y : M2R)) y =
      operatorRightProjectiveChart x y + wittBruhat := by
  unfold operatorRightProjectiveChart
  calc
    (x + wittBruhat * (y : M2R)) * (y⁻¹ : M2R) =
        x * (y⁻¹ : M2R) + (wittBruhat * (y : M2R)) * (y⁻¹ : M2R) := by
          rw [add_mul]
    _ = x * (y⁻¹ : M2R) +
        wittBruhat * ((y : M2R) * (y⁻¹ : M2R)) := by
          rw [mul_assoc]
    _ = x * (y⁻¹ : M2R) + wittBruhat := by
          simp

/-! ### Operator-valued twistor coordinates -/

/-- A two-twistor frame with four coordinates in the noncommutative operator
ring. Every coordinate is transported by the Clifford-derived operator
automorphism; no scalar coordinate carrier is introduced. -/
abbrev OperatorTwistorFrame := Matrix (Fin 2) (Fin 4) M2R

/-- Entrywise lift of Clifford Möbius transport to any finite rectangular
operator matrix. -/
noncomputable def wittLiftMatrix {m n : Type*} (X : Matrix m n M2R) : Matrix m n M2R :=
  fun i j => wittMobiusRingEquiv (X i j)

/-- The full matrix lift preserves composition of operator-valued linear
maps. This is the key compatibility needed to transport incidence equations,
not merely individual twistor coordinates. -/
theorem wittLiftMatrix_mul {l m n : Type*} [Fintype m]
    (X : Matrix l m M2R) (Y : Matrix m n M2R) :
    wittLiftMatrix (X * Y) = wittLiftMatrix X * wittLiftMatrix Y := by
  ext i j
  simp only [wittLiftMatrix, Matrix.mul_apply, map_sum, map_mul]

/-- Operator-valued Plücker incidence is preserved by the full matrix lift.
The coefficient carrier is the native noncommutative `M2R` ring. -/
theorem wittLiftMatrix_incidence {k n : Type*} [Fintype n]
    (C : Matrix k n M2R) (Z : Matrix n (Fin 4) M2R)
    (hCZ : C * Z = 0) :
    wittLiftMatrix C * wittLiftMatrix Z = 0 := by
  rw [← wittLiftMatrix_mul, hCZ]
  ext i j
  simp [wittLiftMatrix]

end InfoGeometry.OperatorAlgebra.CliffordSplitMobiusBridge
