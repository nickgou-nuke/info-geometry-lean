import Mathlib
import InfoGeometry.Clifford.Cl55DyadicMoritaBridge

namespace InfoGeometry.Physics.EmergentSpacetime

open InfoGeometry.Clifford.DyadicMorita
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep

/-- Coordinate-wise sign for the fixed (16, 16) Krein splitting. -/
def kreinSign (i : Fin 32) : ℝ :=
  if (i : ℕ) < 16 then 1 else -1

/-- The fundamental Krein metric $\eta = \operatorname{diag}(+1_{16}, -1_{16})$. -/
def kreinEta : Mat32 :=
  Matrix.diagonal kreinSign

theorem kreinEta_mul_self : kreinEta * kreinEta = 1 := by
  classical
  rw [kreinEta, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, kreinSign]
    split_ifs <;> ring
  · simp only [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem kreinEta_transpose : kreinEta.transpose = kreinEta := by
  dsimp [kreinEta]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- The real Krein-dual co-spinor $\langle \psi|_\eta$. -/
def kreinBra (psi : Spinor32) : Spinor32 :=
  fun i => kreinSign i * psi i

/-- The Krein density matrix dyad $\rho_\eta(\psi) = |\psi\rangle \langle \psi|_\eta$. -/
def kreinDensity (psi : Spinor32) : Mat32 :=
  ketBra psi (kreinBra psi)

theorem kreinDensity_apply (psi : Spinor32) (i j : Fin 32) :
    kreinDensity psi i j = psi i * (kreinSign j * psi j) := rfl

/-- Scalar expectation value / coordinate readback $X_A(\psi) = \operatorname{Tr}(\rho_\eta(\psi) A)$. -/
def spacetimeCoordinate (psi : Spinor32) (A : Mat32) : ℝ :=
  Matrix.trace (kreinDensity psi * A)

theorem spacetimeCoordinate_eq_trace (psi : Spinor32) (A : Mat32) :
    spacetimeCoordinate psi A = Matrix.trace (kreinDensity psi * A) := rfl

/-- Krein-adjoint of an operator $A^\dagger_\eta = \eta A^\top \eta$. -/
def kreinAdj (A : Mat32) : Mat32 :=
  kreinEta * A.transpose * kreinEta

theorem kreinAdj_mul (A B : Mat32) :
    kreinAdj (A * B) = kreinAdj B * kreinAdj A := by
  dsimp [kreinAdj]
  rw [Matrix.transpose_mul]
  simp only [mul_assoc]
  have h : B.transpose * (kreinEta * (kreinEta * (A.transpose * kreinEta))) =
      B.transpose * (A.transpose * kreinEta) := by
    rw [← mul_assoc kreinEta, kreinEta_mul_self, one_mul]
  rw [h]

theorem kreinAdj_sub (A B : Mat32) :
    kreinAdj (A - B) = kreinAdj A - kreinAdj B := by
  dsimp [kreinAdj]
  rw [Matrix.transpose_sub]
  simp only [mul_sub, sub_mul]

/-- The modular derivation / quantum commutator generator $\operatorname{ad}_K(A) = [K, A]$. -/
def modularFlowGenerator (K A : Mat32) : Mat32 :=
  K * A - A * K

theorem modularFlowGenerator_trace (K A : Mat32) :
    Matrix.trace (modularFlowGenerator K A) = 0 := by
  dsimp [modularFlowGenerator]
  rw [Matrix.trace_sub, Matrix.trace_mul_comm]
  exact sub_self _

theorem modularFlowGenerator_krein_antisymm (K A : Mat32)
    (hK : kreinAdj K = K) (hA : kreinAdj A = A) :
    kreinAdj (modularFlowGenerator K A) =
      -modularFlowGenerator K A := by
  rw [modularFlowGenerator, kreinAdj_sub, kreinAdj_mul, kreinAdj_mul,
    hK, hA]
  module

/-- Emergent state-dependent fluctuation metric $g_\psi(A, B) = \frac{1}{2}(X_{AB}(\psi) + X_{BA}(\psi))$. -/
noncomputable def emergentMetric (psi : Spinor32) (A B : Mat32) : ℝ :=
  (1 / 2 : ℝ) *
    (spacetimeCoordinate psi (A * B) +
      spacetimeCoordinate psi (B * A))

theorem emergentMetric_symm (psi : Spinor32) (A B : Mat32) :
    emergentMetric psi A B = emergentMetric psi B A := by
  dsimp [emergentMetric]
  rw [add_comm]

/-- Pullback of the coordinate functional to the Clifford algebra $\operatorname{Cl}(5,5)$. -/
noncomputable def cliffordCoordinate (psi : Spinor32) (x : Cl55) : ℝ :=
  spacetimeCoordinate psi (cl55SpinorAlgEquiv x)

/-- Pullback of the emergent metric to the Clifford algebra $\operatorname{Cl}(5,5)$. -/
noncomputable def cliffordMetric (psi : Spinor32) (x y : Cl55) : ℝ :=
  emergentMetric psi (cl55SpinorAlgEquiv x) (cl55SpinorAlgEquiv y)

theorem cliffordMetric_symm (psi : Spinor32) (x y : Cl55) :
    cliffordMetric psi x y = cliffordMetric psi y x :=
  emergentMetric_symm psi (cl55SpinorAlgEquiv x) (cl55SpinorAlgEquiv y)

theorem cliffordMetric_eq_product_readout (psi : Spinor32) (x y : Cl55) :
    cliffordMetric psi x y =
      (1 / 2 : ℝ) *
        (cliffordCoordinate psi (x * y) +
          cliffordCoordinate psi (y * x)) := by
  dsimp [cliffordMetric, emergentMetric, cliffordCoordinate]
  simp only [map_mul]

end InfoGeometry.Physics.EmergentSpacetime
