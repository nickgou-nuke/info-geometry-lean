import InfoGeometry.Quantum.QutritBraidIncidenceBridge
import InfoGeometry.Physics.TopologicalStandardModelBridge
import InfoGeometry.Clifford.OpSquareTriadBridge
import InfoGeometry.Geometry.MobiusClassification
import InfoGeometry.Geometry.MobiusInfinitesimal
import InfoGeometry.Canonical.MatrixDetExpTraceJacobi
import InfoGeometry.Topology.MobiusThreeTransitiveRecovered

/-!
# Qutrit-indexed Möbius operators, classification, and orientation

The three operators in this bridge are the canonical real Möbius infinitesimal
operators `I`, `N`, and `E`. Their square laws and discriminants give the
elliptic, parabolic, and hyperbolic classes. Exponentiating their trace-zero
`sl₂(ℂ)` matrices produces genuine determinant-one finite Möbius
transformations.

This module reuses three distinct owner layers:

* `Geometry.MobiusInfinitesimal`: generator, Riccati field, and discriminant;
* `Geometry.MobiusClassification`: elliptic/parabolic/hyperbolic/loxodromic
  classification;
* `Topology.MobiusGeometry`: finite projective action on the Riemann sphere.

A qutrit supplies three indices for the real Cayley--Klein sector. The fourth,
loxodromic, class requires a genuinely complex discriminant and is therefore
not silently folded into the qutrit triad. The braid action below permutes the
three Möbius classes; its sign is class-permutation orientation, not by itself
a theorem about spacetime orientability.
-/

noncomputable section

namespace InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge

open InfoGeometryCore
open InfoGeometry.Quantum.Qutrit
open InfoGeometry.Quantum.QutritBraidIncidenceBridge
open InfoGeometry.Topology.ArtinBraidS3Quotient
open InfoGeometry.Geometry
open InfoGeometry.Clifford.OpSquareTriadBridge
open InfoGeometry.Canonical.MatrixDetExpTraceJacobi

abbrev RealMat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev ComplexMat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The tripotent spectral labels index the three qutrit/Möbius sectors. -/
def tripotentStateEquivQutritLabel : TripotentState ≃ Fin 3 where
  toFun := InfoGeometry.Physics.tripotentStateIndex
  invFun := fun i =>
    match i with
    | ⟨0, _⟩ => TripotentState.neg
    | ⟨1, _⟩ => TripotentState.zero
    | ⟨2, _⟩ => TripotentState.pos
  left_inv := by intro s; cases s <;> rfl
  right_inv := by
    intro i
    refine Fin.cases rfl ?_ i
    intro i
    refine Fin.cases rfl ?_ i
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl

/-- Qutrit indices select the elliptic, parabolic, and hyperbolic square classes. -/
def qutritOpSquareClass : Fin 3 → OpSquareClass
  | ⟨0, _⟩ => .elliptic
  | ⟨1, _⟩ => .parabolic
  | ⟨2, _⟩ => .hyperbolic

/-- Qutrit indices select the three real Möbius classes. -/
def qutritMobiusClass : Fin 3 → MobiusClass
  | ⟨0, _⟩ => .elliptic
  | ⟨1, _⟩ => .parabolic
  | ⟨2, _⟩ => .hyperbolic

/-- The qutrit-indexed Möbius infinitesimal operator: `I`, `N`, or `E`. -/
def qutritMobiusOperator (i : Fin 3) : RealMat2 :=
  opSquareMatrix (qutritOpSquareClass i)

@[simp] theorem qutritMobiusOperator_zero :
    qutritMobiusOperator 0 = !![0, -1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qutritMobiusOperator, qutritOpSquareClass, opSquareMatrix,
      InfoGeometry.Algebra.HypercomplexTriad.I]

@[simp] theorem qutritMobiusOperator_one :
    qutritMobiusOperator 1 = !![0, 1; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qutritMobiusOperator, qutritOpSquareClass, opSquareMatrix,
      InfoGeometry.Algebra.HypercomplexTriad.N]

@[simp] theorem qutritMobiusOperator_two :
    qutritMobiusOperator 2 = !![1, 0; 0, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [qutritMobiusOperator, qutritOpSquareClass, opSquareMatrix,
      InfoGeometry.Algebra.HypercomplexTriad.E]

@[simp] theorem qutritMobiusOperator_apply (i : Fin 3) (a b : Fin 2) :
    qutritMobiusOperator i a b =
      opSquareMatrix (qutritOpSquareClass i) a b := by
  rfl

@[simp] theorem qutritMobiusOperator_entry (i : Fin 3) (a b : Fin 2) :
    qutritMobiusOperator i a b =
      match i.1 with
      | 0 => (if a = 0 ∧ b = 1 then (-1 : ℝ) else if a = 1 ∧ b = 0 then 1 else 0)
      | 1 => (if a = 0 ∧ b = 1 then 1 else 0)
      | _ => (if a = 0 ∧ b = 0 then 1 else if a = 1 ∧ b = 1 then -1 else 0) := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [qutritMobiusOperator, qutritOpSquareClass, opSquareMatrix,
      InfoGeometry.Algebra.HypercomplexTriad.I,
      InfoGeometry.Algebra.HypercomplexTriad.N,
      InfoGeometry.Algebra.HypercomplexTriad.E]

/-- Entrywise complexification of a real `2 × 2` operator. -/
def complexifyRealMat2 (A : RealMat2) : ComplexMat2 :=
  fun i j => (A i j : ℂ)

/-- Trace-zero complex generators corresponding respectively to `I`, `N`, and `E`. -/
def qutritMobiusGenerator (i : Fin 3) : sl2C :=
  match i with
  | ⟨0, _⟩ => sl2C.ofCoords 0 (-1) 1
  | ⟨1, _⟩ => sl2C.ofCoords 0 1 0
  | ⟨2, _⟩ => sl2C.ofCoords 1 0 0

/-- The `sl₂(ℂ)` generator matrix is exactly the complexified Möbius operator. -/
theorem qutritMobiusGenerator_matrix_eq_operator (i : Fin 3) :
    (qutritMobiusGenerator i).matrix = complexifyRealMat2 (qutritMobiusOperator i) := by
  refine Fin.cases ?_ ?_ i
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [qutritMobiusGenerator, qutritMobiusOperator,
      qutritOpSquareClass, complexifyRealMat2, sl2C.matrix, sl2C.ofCoords,
      sl2C.a, sl2C.b, sl2C.c, opSquareMatrix,
      InfoGeometry.Algebra.HypercomplexTriad.I]
  · intro i
    refine Fin.cases ?_ ?_ i
    · ext a b
      fin_cases a <;> fin_cases b <;> simp [qutritMobiusGenerator, qutritMobiusOperator,
        qutritOpSquareClass, complexifyRealMat2, sl2C.matrix, sl2C.ofCoords,
        sl2C.a, sl2C.b, sl2C.c, opSquareMatrix,
        InfoGeometry.Algebra.HypercomplexTriad.N]
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      ext a b
      fin_cases a <;> fin_cases b <;> simp [qutritMobiusGenerator, qutritMobiusOperator,
        qutritOpSquareClass, complexifyRealMat2, sl2C.matrix, sl2C.ofCoords,
        sl2C.a, sl2C.b, sl2C.c, opSquareMatrix,
        InfoGeometry.Algebra.HypercomplexTriad.E]

/-- Operator square laws: `I² = -1`, `N² = 0`, and `E² = 1`. -/
theorem qutritMobiusOperator_sq (i : Fin 3) :
    qutritMobiusOperator i * qutritMobiusOperator i =
      (opSquareScalar (qutritOpSquareClass i)) • (1 : RealMat2) := by
  exact opSquareMatrix_sq (qutritOpSquareClass i)

/-- The infinitesimal Möbius discriminants are `-4`, `0`, and `4`. -/
theorem qutritMobiusGenerator_discriminant :
    ∀ i : Fin 3,
      (qutritMobiusGenerator i).discriminant =
        match qutritMobiusClass i with
        | .elliptic => -4
        | .parabolic => 0
        | .hyperbolic => 4
        | .loxodromic => 0 := by
  intro i
  refine Fin.cases ?_ ?_ i
  · norm_num [qutritMobiusGenerator, qutritMobiusClass, sl2C.discriminant,
      sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c]
  · intro i
    refine Fin.cases ?_ ?_ i
    · norm_num [qutritMobiusGenerator, qutritMobiusClass, sl2C.discriminant,
        sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c]
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      norm_num [qutritMobiusGenerator, qutritMobiusClass, sl2C.discriminant,
        sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c]

/-- The real qutrit triad does not contain the genuinely complex loxodromic class. -/
theorem qutritMobiusClass_ne_loxodromic (i : Fin 3) :
    qutritMobiusClass i ≠ MobiusClass.loxodromic := by
  refine Fin.cases ?_ ?_ i
  · simp [qutritMobiusClass]
  · intro i
    refine Fin.cases ?_ ?_ i
    · simp [qutritMobiusClass]
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [qutritMobiusClass]

/-- The Möbius generator selected by a tripotent spectral value. -/
def tripotentMobiusGenerator (s : TripotentState) : sl2C :=
  qutritMobiusGenerator (tripotentStateEquivQutritLabel s)

/-- Tripotent values read back the elliptic/parabolic/hyperbolic discriminants. -/
theorem tripotentMobiusGenerator_discriminant :
    ∀ s : TripotentState,
      (tripotentMobiusGenerator s).discriminant =
        match s with
        | .neg => -4
        | .zero => 0
        | .pos => 4 := by
  intro s
  cases s <;> norm_num [tripotentMobiusGenerator, tripotentStateEquivQutritLabel,
    InfoGeometry.Physics.tripotentStateIndex, qutritMobiusGenerator,
    sl2C.discriminant, sl2C.ofCoords, sl2C.a, sl2C.b, sl2C.c]

/-- Finite one-parameter matrix flow generated by the selected Möbius operator. -/
def qutritMobiusMatrixFlow (i : Fin 3) (t : ℂ) : ComplexMat2 :=
  matrixExpFlow (qutritMobiusGenerator i).matrix t

/-- Every finite qutrit-indexed Möbius flow matrix has determinant one. -/
theorem qutritMobiusMatrixFlow_det (i : Fin 3) (t : ℂ) :
    Matrix.det (qutritMobiusMatrixFlow i t) = 1 := by
  unfold qutritMobiusMatrixFlow
  rw [det_matrixExpFlow_eq_exp_trace_mul]
  simp [Matrix.trace, sl2C.matrix]

/-- The finite Möbius flow starts at the identity. -/
theorem qutritMobiusMatrixFlow_zero (i : Fin 3) :
    qutritMobiusMatrixFlow i 0 = 1 := by
  simp [qutritMobiusMatrixFlow, matrixExpFlow]

/-- The finite matrices form an additive one-parameter Möbius flow. -/
theorem qutritMobiusMatrixFlow_add (i : Fin 3) (s t : ℂ) :
    qutritMobiusMatrixFlow i (s + t) =
      qutritMobiusMatrixFlow i s * qutritMobiusMatrixFlow i t := by
  let A := (qutritMobiusGenerator i).matrix
  have hcomm : Commute (s • A) (t • A) :=
    ((Commute.refl A).smul_left s).smul_right t
  simpa [qutritMobiusMatrixFlow, matrixExpFlow, A, add_smul] using
    (Matrix.exp_add_of_commute (s • A) (t • A) hcomm)

/-- The matrix exponential packaged as the canonical Riemann-sphere Möbius transformation. -/
def qutritMobiusTransform (i : Fin 3) (t : ℂ) : InfoGeometry.MobiusTransform where
  a := qutritMobiusMatrixFlow i t 0 0
  b := qutritMobiusMatrixFlow i t 0 1
  c := qutritMobiusMatrixFlow i t 1 0
  d := qutritMobiusMatrixFlow i t 1 1
  det_ne_zero := by
    have hdet :
        qutritMobiusMatrixFlow i t 0 0 * qutritMobiusMatrixFlow i t 1 1 -
          qutritMobiusMatrixFlow i t 0 1 * qutritMobiusMatrixFlow i t 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using qutritMobiusMatrixFlow_det i t
    rw [hdet]
    exact one_ne_zero

/-- At time zero, every selected finite Möbius flow acts identically. -/
theorem qutritMobiusTransform_zero_eval (i : Fin 3) (z : InfoGeometry.RiemannSphere) :
    (qutritMobiusTransform i 0).eval z = z := by
  cases z with
  | none =>
      simp [qutritMobiusTransform, qutritMobiusMatrixFlow_zero,
        InfoGeometry.MobiusTransform.eval]
  | some z =>
      simp [qutritMobiusTransform, qutritMobiusMatrixFlow_zero,
        InfoGeometry.MobiusTransform.eval]

/-- Triality cycle on the three real Möbius classes; loxodromic remains separate. -/
def realMobiusClassCycle : MobiusClass → MobiusClass
  | .elliptic => .parabolic
  | .parabolic => .hyperbolic
  | .hyperbolic => .elliptic
  | .loxodromic => .loxodromic

/-- The qutrit label cycle is exactly the real Möbius-class triality cycle. -/
theorem qutritMobiusClass_cycle (i : Fin 3) :
    qutritMobiusClass (qutritCycle i) = realMobiusClassCycle (qutritMobiusClass i) := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

/-- Orientation character of permutations of the three real Möbius classes. -/
def mobiusClassOrientationCharacter : Equiv.Perm (Fin 3) →* ℤˣ :=
  Equiv.Perm.sign

/-- The Möbius-class triality cycle is the product of adjacent Artin transpositions. -/
theorem qutritCycle_eq_sigma1_mul_sigma2 : qutritCycle = sigma1 * sigma2 := by
  apply Equiv.ext
  intro i
  refine Fin.cases rfl ?_ i
  intro i
  refine Fin.cases rfl ?_ i
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- The three-cycle preserves the orientation of the real Möbius-class triad. -/
theorem qutritMobiusClassCycle_orientation_preserving :
    mobiusClassOrientationCharacter qutritCycle = 1 := by
  rw [qutritCycle_eq_sigma1_mul_sigma2]
  change Equiv.Perm.sign (sigma1 * sigma2) = 1
  rw [Equiv.Perm.sign_mul]
  have hs1 : Equiv.Perm.sign sigma1 = -1 := Equiv.Perm.sign_swap (by omega)
  have hs2 : Equiv.Perm.sign sigma2 = -1 := Equiv.Perm.sign_swap (by omega)
  rw [hs1, hs2]
  norm_num

/-- A three-channel ordered frame on the Riemann sphere. -/
abbrev QutritMobiusFrame := Fin 3 → InfoGeometry.RiemannSphere

/-- A Möbius frame is nondegenerate when its three points are distinct. -/
def QutritMobiusFrame.Nondegenerate (z : QutritMobiusFrame) : Prop :=
  Function.Injective z

/-- Two nondegenerate three-channel frames determine a unique projective Möbius map. -/
theorem qutritFrame_strictly_three_transitive
    (z w : QutritMobiusFrame) (hz : z.Nondegenerate) (hw : w.Nondegenerate) :
    ∃ M : InfoGeometry.MobiusTransform,
      (∀ i, M.eval (z i) = w i) ∧
      ∀ M' : InfoGeometry.MobiusTransform,
        (∀ i, M'.eval (z i) = w i) → M.equiv M' := by
  have hz01 : z 0 ≠ z 1 := fun h => (by omega : (0 : Fin 3) ≠ 1) (hz h)
  have hz12 : z 1 ≠ z 2 := fun h => (by omega : (1 : Fin 3) ≠ 2) (hz h)
  have hz02 : z 0 ≠ z 2 := fun h => (by omega : (0 : Fin 3) ≠ 2) (hz h)
  have hw01 : w 0 ≠ w 1 := fun h => (by omega : (0 : Fin 3) ≠ 1) (hw h)
  have hw12 : w 1 ≠ w 2 := fun h => (by omega : (1 : Fin 3) ≠ 2) (hw h)
  have hw02 : w 0 ≠ w 2 := fun h => (by omega : (0 : Fin 3) ≠ 2) (hw h)
  obtain ⟨M, h0, h1, h2, huniq⟩ := InfoGeometry.strictly_three_transitive
    (z 0) (z 1) (z 2) hz01 hz12 hz02
    (w 0) (w 1) (w 2) hw01 hw12 hw02
  refine ⟨M, ?_, ?_⟩
  · intro i
    refine Fin.cases h0 ?_ i
    intro i
    refine Fin.cases h1 ?_ i
    intro i
    simpa [Fin.eq_zero i] using h2
  · intro M' hM'
    apply huniq M'
    exact ⟨hM' 0, hM' 1, hM' 2⟩

end InfoGeometry.Quantum.QutritMobiusTripotentOrientationBridge
