/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.EvenRegularRepresentation
import InfoGeometry.Quantum.RealKCategory
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Internal complex phase on the native even Clifford module

An orthogonal real two-plane with `Q u * Q v = 1` gives the actual even
Clifford element `B = ι(u)ι(v)` with `B * B = -1`. Right multiplication by
`B` defines the existing `RealKVect` structure on `CliffordAlgebra.even Q`.
All left regular observables commute with this phase action by associativity;
the bivector is not assumed central in the Clifford algebra.

The real coordinate map `(a,b) ↦ a • 1 + b • B` intertwines the coordinate
quarter-turn with that right action. Its circle gives internal phase elements
whose action is the existing categorical rotor. For the constructed orthogonal
plane, native reversion gives the usual inverse-phase relation. Complex scalars occur only in
comparison theorems for the already-derived complex module structure.

Grade involution fixes the even phase plane. Reversion changes the sign of
an orthogonal plane bivector. No metric-adjoint or Krein-isometry assertion is
made here; membership in Mathlib's spin group is also a separate obligation.
-/

noncomputable section

namespace InfoGeometry.Clifford.EvenInternalComplex

open CliffordAlgebra
open InfoGeometry.Quantum.RealKCategory
open InfoGeometry.Clifford.EvenRegularRepresentation

/-- The real quarter-turn on a coordinate plane. -/
def coordinateJ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (-p.2, p.1)
  map_add' p q := by ext <;> simp [add_comm]
  map_smul' r p := by ext <;> simp

/-- The coordinate plane is an object of the existing internal-complex category. -/
def coordinatePlane : RealKVect where
  V := ℝ × ℝ
  K := coordinateJ
  K_sq := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    rfl

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

local notation "EvenQ" => CliffordAlgebra.even Q

/-- A pair of native Clifford vectors, packaged by Mathlib's even embedding. -/
def planeBivector (u v : M) : EvenQ :=
  (CliffordAlgebra.even.ι Q).bilin u v

@[simp] theorem coe_planeBivector (u v : M) :
    (planeBivector Q u v : CliffordAlgebra Q) = ι Q u * ι Q v := rfl

theorem planeBivector_mem_even (u v : M) :
    (planeBivector Q u v : CliffordAlgebra Q) ∈ evenOdd Q 0 :=
  coe_mem_evenOdd_zero Q (planeBivector Q u v)

/-- Native grade involution fixes the plane bivector. -/
theorem involute_planeBivector (u v : M) :
    CliffordAlgebra.involute (planeBivector Q u v : CliffordAlgebra Q) =
      (planeBivector Q u v : CliffordAlgebra Q) :=
  CliffordAlgebra.involute_eq_of_mem_even (planeBivector_mem_even Q u v)

/-- Native reversion negates an orthogonal plane bivector. -/
theorem reverse_planeBivector (u v : M) (huv : Q.IsOrtho u v) :
    CliffordAlgebra.reverse (planeBivector Q u v : CliffordAlgebra Q) =
      -(planeBivector Q u v : CliffordAlgebra Q) := by
  change CliffordAlgebra.reverse (ι Q u * ι Q v) = -(ι Q u * ι Q v)
  rw [CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι,
    CliffordAlgebra.reverse_ι]
  exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho huv.symm

/-- Orthogonality and a positive unit product of quadratic norms give square `-1`. -/
theorem planeBivector_sq (u v : M) (huv : Q.IsOrtho u v)
    (hQ : Q u * Q v = 1) :
    planeBivector Q u v * planeBivector Q u v = -(1 : EvenQ) := by
  apply Subtype.ext
  change (ι Q u * ι Q v) * (ι Q u * ι Q v) = -(1 : CliffordAlgebra Q)
  calc
    (ι Q u * ι Q v) * (ι Q u * ι Q v) =
        ι Q u * (ι Q v * ι Q u) * ι Q v := by simp only [mul_assoc]
    _ = ι Q u * (-(ι Q u * ι Q v)) * ι Q v := by
      rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho huv.symm]
    _ = -((ι Q u * ι Q u) * (ι Q v * ι Q v)) := by
      simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(algebraMap ℝ (CliffordAlgebra Q) (Q u * Q v)) := by
      rw [CliffordAlgebra.ι_sq_scalar, CliffordAlgebra.ι_sq_scalar, map_mul]
    _ = -(1 : CliffordAlgebra Q) := by rw [hQ, map_one]

theorem planeBivector_sq_of_positive_plane (u v : M) (huv : Q.IsOrtho u v)
    (hu : Q u = 1) (hv : Q v = 1) :
    planeBivector Q u v * planeBivector Q u v = -(1 : EvenQ) :=
  planeBivector_sq Q u v huv (by simp [hu, hv])

theorem planeBivector_sq_of_negative_plane (u v : M) (huv : Q.IsOrtho u v)
    (hu : Q u = -1) (hv : Q v = -1) :
    planeBivector Q u v * planeBivector Q u v = -(1 : EvenQ) :=
  planeBivector_sq Q u v huv (by simp [hu, hv])

/-- The square law for right multiplication on the actual even algebra. -/
theorem rightRegular_sq (B : EvenQ) (hB : B * B = -(1 : EvenQ)) :
    (rightRegularLinearMap Q B).comp (rightRegularLinearMap Q B) =
      -(LinearMap.id : EvenQ →ₗ[ℝ] EvenQ) := by
  apply LinearMap.ext
  intro x
  change (x * B) * B = -x
  rw [mul_assoc, hB]
  simp

/-- The native even algebra, with its internal phase acting on the right. -/
abbrev rightRealK (B : EvenQ) (hB : B * B = -(1 : EvenQ)) : RealKVect where
  V := EvenQ
  K := rightRegularLinearMap Q B
  K_sq := rightRegular_sq Q B hB

/-- The geometric plane discharges the internal-phase square law. -/
def planeRealK (u v : M) (huv : Q.IsOrtho u v) (hQ : Q u * Q v = 1) :
    RealKVect :=
  rightRealK Q (planeBivector Q u v) (planeBivector_sq Q u v huv hQ)

/-- Every left regular observable is a morphism for this right complex structure. -/
def leftObservable (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (a : EvenQ) :
    RealKVect.Hom (rightRealK Q B hB) (rightRealK Q B hB) where
  hom := leftRegularLinearMap Q a
  comm := leftRegularLinearMap_comm_rightRegularLinearMap Q a B

@[simp] theorem leftObservable_apply
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (a x : EvenQ) :
    leftObservable Q B hB a x = a * x := rfl

/-- The native real two-plane generated by `1` and the even bivector. -/
def phasePlaneMap (B : EvenQ) : (ℝ × ℝ) →ₗ[ℝ] EvenQ where
  toFun p := p.1 • (1 : EvenQ) + p.2 • B
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' r p := by simp [smul_add, smul_smul]

@[simp] theorem phasePlaneMap_apply (B : EvenQ) (p : ℝ × ℝ) :
    phasePlaneMap Q B p = p.1 • (1 : EvenQ) + p.2 • B := rfl

/-- Coordinate quarter-turn is carried to actual right multiplication by `B`. -/
theorem phasePlaneMap_intertwines
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) :
    (phasePlaneMap Q B).comp coordinateJ =
      (rightRegularLinearMap Q B).comp (phasePlaneMap Q B) := by
  apply LinearMap.ext
  intro p
  change (-p.2) • (1 : EvenQ) + p.1 • B =
    (p.1 • (1 : EvenQ) + p.2 • B) * B
  simp only [add_mul, smul_mul_assoc, one_mul, hB, smul_neg, neg_smul]
  abel

/-- The coordinate phase plane and the even module are related by an actual morphism. -/
def phasePlaneHom (B : EvenQ) (hB : B * B = -(1 : EvenQ)) :
    RealKVect.Hom coordinatePlane (rightRealK Q B hB) where
  hom := phasePlaneMap Q B
  comm := phasePlaneMap_intertwines Q B hB

/-- Comparison with Mathlib's universal lift; native phase coordinates remain real. -/
theorem phasePlaneMap_eq_complex_lift
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (z : ℂ) :
    phasePlaneMap Q B (z.re, z.im) = Complex.lift ⟨B, hB⟩ z := by
  change z.re • (1 : EvenQ) + z.im • B = Complex.liftAux B hB z
  rw [Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one]

/-- The phase coordinates do not collapse on a nontrivial even algebra. -/
theorem phasePlaneMap_injective [Nontrivial EvenQ]
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) :
    Function.Injective (phasePlaneMap Q B) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change a • (1 : EvenQ) + b • B = c • (1 : EvenQ) + d • B at h
  have hz : (⟨a, b⟩ : ℂ) = (⟨c, d⟩ : ℂ) := by
    apply (Complex.lift ⟨B, hB⟩).injective
    change Complex.liftAux B hB (⟨a, b⟩ : ℂ) =
      Complex.liftAux B hB (⟨c, d⟩ : ℂ)
    simpa only [Complex.liftAux_apply, Algebra.algebraMap_eq_smul_one] using h
  exact Prod.ext (congrArg Complex.re hz) (congrArg Complex.im hz)

/-- The existing derived complex action is precisely multiplication on the right. -/
theorem complexSMul_eq_right_phase
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (z : ℂ) (x : EvenQ) :
    RealKVect.complexSMul (rightRealK Q B hB) z x =
      x * phasePlaneMap Q B (z.re, z.im) := by
  change z.re • x + z.im • (x * B) =
    x * (z.re • (1 : EvenQ) + z.im • B)
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one]

/-- An internal phase element in the even algebra. A general even square-minus-one
`B` need not be a geometric bivector or define an element of the spin group.
The orthogonal-plane specialization has the reversion law proved below. -/
def rotorElement (B : EvenQ) (θ : ℝ) : EvenQ :=
  phasePlaneMap Q B (Real.cos θ, Real.sin θ)

/-- Its right action is the existing categorical rotor. -/
theorem rightRegular_rotorElement
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ) :
    rightRegularLinearMap Q (rotorElement Q B θ) =
      (rotor (rightRealK Q B hB) θ).hom := by
  apply LinearMap.ext
  intro x
  change x * (Real.cos θ • (1 : EvenQ) + Real.sin θ • B) =
    Real.cos θ • x + Real.sin θ • (x * B)
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one]

/-- Real coordinate rotation is carried to right multiplication by the internal phase. -/
theorem phasePlaneMap_rotor_action
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ) (p : ℝ × ℝ) :
    phasePlaneMap Q B ((rotor coordinatePlane θ).hom p) =
      phasePlaneMap Q B p * rotorElement Q B θ := by
  have hJ : phasePlaneMap Q B (coordinateJ p) = phasePlaneMap Q B p * B :=
    congrArg (fun T : (ℝ × ℝ) →ₗ[ℝ] EvenQ => T p)
      (phasePlaneMap_intertwines Q B hB)
  change phasePlaneMap Q B (Real.cos θ • p + Real.sin θ • coordinateJ p) =
    phasePlaneMap Q B p * (Real.cos θ • (1 : EvenQ) + Real.sin θ • B)
  rw [map_add, map_smul, map_smul, hJ,
    mul_add, mul_smul_comm, mul_smul_comm, mul_one]

@[simp] theorem rotorElement_zero (B : EvenQ) :
    rotorElement Q B 0 = 1 := by simp [rotorElement]

/-- Multiplication of the native phase elements has the same addition law as
the categorical rotor action identified above. -/
theorem rotorElement_mul
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ φ : ℝ) :
    rotorElement Q B θ * rotorElement Q B φ = rotorElement Q B (θ + φ) := by
  change (Real.cos θ • (1 : EvenQ) + Real.sin θ • B) *
      (Real.cos φ • (1 : EvenQ) + Real.sin φ • B) =
    Real.cos (θ + φ) • (1 : EvenQ) + Real.sin (θ + φ) • B
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_smul, one_mul, mul_one, hB, smul_neg]
  rw [Real.cos_add, Real.sin_add, sub_smul, add_smul]
  abel

theorem rotorElement_mul_neg
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ) :
    rotorElement Q B θ * rotorElement Q B (-θ) = 1 := by
  rw [rotorElement_mul Q B hB, add_neg_cancel, rotorElement_zero]

theorem rotorElement_neg_mul
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ) :
    rotorElement Q B (-θ) * rotorElement Q B θ = 1 := by
  rw [rotorElement_mul Q B hB, neg_add_cancel, rotorElement_zero]

/-- The phase has the usual complex exponential only as a comparison readout. -/
theorem rotorElement_eq_complex_phase
    (B : EvenQ) (hB : B * B = -(1 : EvenQ)) (θ : ℝ) :
    rotorElement Q B θ = Complex.lift ⟨B, hB⟩ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [← phasePlaneMap_eq_complex_lift Q B hB]
  have hphase : Complex.exp ((θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hphase]
  simp only [rotorElement, phasePlaneMap_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]

/-- All the native even phase elements are fixed by Clifford grade involution. -/
theorem involute_phasePlaneMap (B : EvenQ) (p : ℝ × ℝ) :
    CliffordAlgebra.involute (phasePlaneMap Q B p : CliffordAlgebra Q) =
      (phasePlaneMap Q B p : CliffordAlgebra Q) :=
  CliffordAlgebra.involute_eq_of_mem_even
    (coe_mem_evenOdd_zero Q (phasePlaneMap Q B p))

/-- Reversion on an orthogonal phase plane is coordinate conjugation. -/
theorem reverse_phasePlaneMap (u v : M) (huv : Q.IsOrtho u v) (a b : ℝ) :
    CliffordAlgebra.reverse
        (phasePlaneMap Q (planeBivector Q u v) (a, b) : CliffordAlgebra Q) =
      (phasePlaneMap Q (planeBivector Q u v) (a, -b) : CliffordAlgebra Q) := by
  change CliffordAlgebra.reverse
      (a • (1 : CliffordAlgebra Q) + b • (planeBivector Q u v : CliffordAlgebra Q)) =
    a • (1 : CliffordAlgebra Q) + (-b) • (planeBivector Q u v : CliffordAlgebra Q)
  rw [map_add, map_smul, map_smul, CliffordAlgebra.reverse.map_one,
    reverse_planeBivector Q u v huv]
  simp

theorem reverse_rotorElement (u v : M) (huv : Q.IsOrtho u v) (θ : ℝ) :
    CliffordAlgebra.reverse
        (rotorElement Q (planeBivector Q u v) θ : CliffordAlgebra Q) =
      (rotorElement Q (planeBivector Q u v) (-θ) : CliffordAlgebra Q) := by
  simpa only [rotorElement, Real.cos_neg, Real.sin_neg] using
    reverse_phasePlaneMap Q u v huv (Real.cos θ) (Real.sin θ)

end InfoGeometry.Clifford.EvenInternalComplex
