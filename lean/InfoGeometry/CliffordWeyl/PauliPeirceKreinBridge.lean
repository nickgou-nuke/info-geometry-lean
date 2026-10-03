import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution
import InfoGeometry.CliffordWeyl.ChiralIdeals
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Krein.RealPlaneMatrixBridge
import InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge

/-!
# InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

Genuine closure of the join between three previously disconnected lanes:

1. **Split Clifford / DeWitt-split lane.** `InfoGeometry.Clifford.Cl11Matrix` realizes
   `Cl(1,1)` as `Mat₂(ℝ)` by the real Pauli matrices
   `Eplus = σ₃` (squares to `+1`), `Eminus = ε` (the real elliptic generator,
   squares to `-1`),
   `J1 = σ₁ = Eplus * Eminus`.

2. **Peirce / projector lane.** `InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution`
   builds `P± = (1 ± χ)/2` constructively from an involution `χ² = 1`, and
   `InfoGeometry.CliffordWeyl.ChiralIdeals` derives the full corner calculus
   (off-diagonal decomposition, diagonal corner vanishing, Peirce swaps)
   from that involution. This module was previously only instantiated on
   abstract operators, never on the concrete split Clifford carrier.

3. **Double real Krein lane.** `InfoGeometry.Krein.RealPlaneMatrixBridge` identifies the
   Krein fundamental symmetry `J` of the real plane `HilbertDoubled ℝ` with the
   matrix `Eplus`, and the Krein grading (modular swap) with `J1`.

The bridge establishes that **these are the same involution**: the Pauli generator
`Eplus`, the chiral grading `χ` feeding the Peirce projectors, and the Krein
fundamental symmetry `J` coincide. Consequently the Krein `±1`-spectral sheets,
the Peirce corner projectors, and the split-Clifford parity decomposition are
literally the same algebraic object, and `Eminus` / `J1` are exactly the
off-diagonal (odd) part of the algebra.

No certificates, no `sorry`, no extra structure fields: every statement below is a
native Lean derivation from `Cl11Matrix` and `ChiralProjectorFromInvolution` roots.
-/

namespace InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra
open InfoGeometry.CliffordWeyl
open InfoGeometry.Canonical.Cl11SplitQuaternionMobiusBridge

/-! ## 1. The Pauli generator is a chiral involution -/

/--
The real Pauli generator `Eplus = σ₃` as a constructive chiral involution of the
split Clifford algebra carrier `Mat₂(ℝ) = Cl(1,1)`.

The involution law is not assumed: it is exactly the proved Pauli law `Eplus_sq`.
-/
noncomputable def pauliChiral : ChiralInvolution Mat2 where
  chi := Eplus
  chi_sq := Eplus_sq

@[simp] lemma pauliChiral_chi : pauliChiral.chi = Eplus := rfl

/-! ## 2. The Peirce projectors are the explicit diagonal projections -/

/-- The constructive chiral projector is the diagonal projection onto the `+1` sheet. -/
theorem pauliChiral_Pleft :
    pauliChiral.Pleft = !![(1 : ℝ), 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ChiralInvolution.Pleft, pauliChiral, Eplus, Matrix.smul_apply,
      Matrix.add_apply]; ring

/-- The complementary chiral projector is the diagonal projection onto the `-1` sheet. -/
theorem pauliChiral_Pright :
    pauliChiral.Pright = !![(0 : ℝ), 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ChiralInvolution.Pright, pauliChiral, Eplus, Matrix.smul_apply,
      Matrix.sub_apply]; ring

/-! ## 2a. The split product blade is the existing Peirce involution -/

/-- The real split product `splitIL = splitI * splitL` is the Pauli involution
`Eplus`.  This transports the product of the elliptic and hyperbolic matrix roots
to the already-owned Peirce grading; it does not introduce a scalar imaginary
unit or a second projector construction. -/
theorem splitIL_eq_Eplus : splitIL = Eplus := by
  rw [splitIL_eq_sigma3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, BottPeriodicityReconciliation.sigma3,
      BottPeriodicityReconciliation.sigma3R]

/-- The product blade's involution is literally the chiral operator already
feeding the Peirce projectors. -/
theorem splitIL_eq_pauliChiral_chi : splitIL = pauliChiral.chi := by
  rw [splitIL_eq_Eplus, pauliChiral_chi]

/-- The normalized `+` operator root of `splitIL` is the existing left Peirce
projector.  Both terms are real `2 × 2` matrices; the identity is the matrix
identity and multiplication is matrix multiplication. -/
theorem splitIL_leftPeirce_eq_pauliChiral_Pleft :
    (1 / 2 : ℝ) • ((1 : Mat2) + splitIL) = pauliChiral.Pleft := by
  rw [splitIL_eq_pauliChiral_chi]
  rfl

/-- The normalized `−` operator root of `splitIL` is the existing right Peirce
projector. -/
theorem splitIL_rightPeirce_eq_pauliChiral_Pright :
    (1 / 2 : ℝ) • ((1 : Mat2) - splitIL) = pauliChiral.Pright := by
  rw [splitIL_eq_pauliChiral_chi]
  rfl

/-- Reading off the two projections: the `+1` sheet projector keeps the top row. -/
@[simp] theorem pauliChiral_Pleft_apply (M : Mat2) :
    pauliChiral.Pleft * M = !![M 0 0, M 0 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliChiral_Pleft, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `-1` sheet projector keeps the bottom row. -/
@[simp] theorem pauliChiral_Pright_apply (M : Mat2) :
    pauliChiral.Pright * M = !![0, 0; M 1 0, M 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliChiral_Pright, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 3. Oddness of the two remaining Pauli generators -/

/-- The real elliptic generator `Eminus` anticommutes with the chiral involution. -/
theorem Eminus_anticommutes_chi :
    Eminus * pauliChiral.chi = -(pauliChiral.chi * Eminus) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliChiral_chi, Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.neg_apply]

/-- The Krein modular swap `J1 = σ₁` anticommutes with the chiral involution. -/
theorem J1_anticommutes_chi :
    J1 * pauliChiral.chi = -(pauliChiral.chi * J1) := by
  rw [pauliChiral_chi]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-! ## 4. Peirce corner calculus on the split Clifford carrier -/

/--
`Eminus` lies purely in the off-diagonal Peirce corners: it is a sum of the
`(+,-)` and `(-,+)` components and nothing else.

This is the concrete split-Clifford instance of `off_diagonal_decomposition`.
-/
theorem Eminus_off_diagonal :
    Eminus = pauliChiral.Pleft * Eminus * pauliChiral.Pright
      + pauliChiral.Pright * Eminus * pauliChiral.Pleft :=
  off_diagonal_decomposition pauliChiral Eminus (Eminus_anticommutes_chi)

/-- The two off-diagonal Peirce corners of `Eminus` vanish. -/
theorem Eminus_diagonal_corners_zero :
    pauliChiral.Pleft * Eminus * pauliChiral.Pleft = 0 ∧
      pauliChiral.Pright * Eminus * pauliChiral.Pright = 0 :=
  diagonal_corners_zero pauliChiral Eminus (Eminus_anticommutes_chi)

/--
The Krein modular swap `J1` lies purely in the off-diagonal Peirce corners.

This is the statement that the Krein grading operator is *odd* with respect to the
fundamental symmetry, i.e. that the grading exchanges the two Krein spectral sheets.
-/
theorem J1_off_diagonal :
    J1 = pauliChiral.Pleft * J1 * pauliChiral.Pright
      + pauliChiral.Pright * J1 * pauliChiral.Pleft :=
  off_diagonal_decomposition pauliChiral J1 (J1_anticommutes_chi)

/-- Both diagonal Peirce corners of the Krein modular swap vanish. -/
theorem J1_diagonal_corners_zero :
    pauliChiral.Pleft * J1 * pauliChiral.Pleft = 0 ∧
      pauliChiral.Pright * J1 * pauliChiral.Pright = 0 :=
  diagonal_corners_zero pauliChiral J1 (J1_anticommutes_chi)

/--
Left multiplication by the Krein modular swap exchanges the two principal chiral
ideals: it maps `+1`-supported elements to `-1`-supported elements.

This is the concrete Peirce-swap law `P₊ M = M P₋` for an odd operator.
-/
theorem J1_swap_corners :
    pauliChiral.Pleft * J1 = J1 * pauliChiral.Pright :=
  Pleft_mul_swap pauliChiral J1 (J1_anticommutes_chi)

/-! ## 5. The Krein fundamental symmetry *is* the Pauli chiral involution -/

section RealPlane

open InfoGeometry.Krein.RealPlaneMatrixBridge

variable (P : Type := InfoGeometry.Krein.RealPlaneMatrixBridge.Plane)

/-- The Krein fundamental symmetry, as an endomorphism of the real plane. -/
noncomputable def jLin : Module.End ℝ InfoGeometry.Krein.RealPlaneMatrixBridge.Plane :=
  (InfoGeometry.Krein.KreinSpace.jCLM
    (H := InfoGeometry.Krein.RealPlaneMatrixBridge.Plane)).toLinearMap

/-- The Krein `+1` spectral projector `(Id + J)/2`, as an endomorphism of the real plane. -/
noncomputable def kreinPlus : Module.End ℝ InfoGeometry.Krein.RealPlaneMatrixBridge.Plane :=
  (1 / 2 : ℝ) • (jLin + LinearMap.id)

/-- The Krein `-1` spectral projector `(Id - J)/2`, as an endomorphism of the real plane. -/
noncomputable def kreinMinus : Module.End ℝ InfoGeometry.Krein.RealPlaneMatrixBridge.Plane :=
  (1 / 2 : ℝ) • (LinearMap.id - jLin)

/--
Owner-level identification: the Krein fundamental symmetry `J` on the real plane
`HilbertDoubled ℝ`, read out in the Pauli basis, is exactly the chiral involution
`χ` that generates the Peirce projectors.

This is the join of the double-real-Krein lane with the Peirce/projector lane:
there is a single object, not two parallel descriptions. It is what makes the
Krein `±1`-spectral sheets and the Peirce corners of `Cl(1,1)` literally the same
decomposition.
-/
theorem e2m_jLin_eq_pauliChiral_chi :
    InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix jLin
      = pauliChiral.chi := by
  unfold jLin
  rw [InfoGeometry.Krein.RealPlaneMatrixBridge.fundamental_matrix]
  rfl

/--
Consequently the Krein `+1` spectral projector and the constructive Peirce `+1`
projector are the same endomorphism of the real plane, and hence the same matrix
in the Pauli basis: `endToMatrix (Id + J)/2 = diag(1, 0) = Pleft`.

The fundamental symmetry's `+1` spectral sheet *is* the Peirce `+1` corner.
-/
theorem e2m_kreinPlus_eq_pauliChiral_Pleft :
    InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix kreinPlus
      = pauliChiral.Pleft := by
  rw [pauliChiral_Pleft]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [kreinPlus, endToMatrix, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conjAlgEquiv_apply, coordinates, jLin,
      LinearMap.id_apply]; ring

/-- Dually, `endToMatrix (Id - J)/2 = diag(0, 1) = Pright`. -/
theorem e2m_kreinMinus_eq_pauliChiral_Pright :
    InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix kreinMinus
      = pauliChiral.Pright := by
  rw [pauliChiral_Pright]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [kreinMinus, endToMatrix, LinearMap.toMatrixAlgEquiv'_apply,
      LinearEquiv.conjAlgEquiv_apply, coordinates, jLin,
      LinearMap.id_apply]; ring

/--
The two Krein spectral projectors are complementary: in the Pauli basis their sum
is the identity matrix.

The proof is one line once the identification is available: `endToMatrix` is an
`AlgEquiv`, so it distributes over `+`, and `ChiralInvolution.Pleft_add_Pright`
gives `Pleft + Pright = 1` on the split Clifford carrier. This is the precise sense
in which the Krein `±1`-spectral splitting of the real plane *is* the constructive
Peirce splitting — not merely analogous.

Note the statement is deliberately at the `endToMatrix` (Pauli-matrix) level: the
`Plane` carrier is a `ULift` of `DoubledSpace ℝ`, so `LinearMap.ext`/`abel` cannot
see through the wrapper, whereas the `AlgEquiv` route is both shorter and is the
mathematically meaningful one.
-/
theorem e2m_kreinPlus_add_kreinMinus :
    InfoGeometry.Krein.RealPlaneMatrixBridge.endToMatrix
        (kreinPlus + kreinMinus) = 1 := by
  rw [map_add, e2m_kreinPlus_eq_pauliChiral_Pleft,
    e2m_kreinMinus_eq_pauliChiral_Pright]
  exact ChiralInvolution.Pleft_add_Pright pauliChiral

end RealPlane

end InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
