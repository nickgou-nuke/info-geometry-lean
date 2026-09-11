import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ProjectiveBoundarySL2Composition

namespace InfoGeometry.Topology

/-!
# One-parameter families of determinant-one boundary blocks

The algebraic flow laws are separated from continuity.  This prevents an
algebraic representation from being promoted to a topological flow without a
genuine continuity proof on the chosen quotient topology.
-/

def SL2BoundaryMatrix.identity
    {R : Type*} [CommRing R] : SL2BoundaryMatrix R where
  matrix := ![![1, 0], ![0, 1]]
  det_eq_one := by simp [det2]

@[simp] theorem SL2BoundaryMatrix.identity_matrix
    {R : Type*} [CommRing R] :
    SL2BoundaryMatrix.identity.matrix = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [SL2BoundaryMatrix.identity, Matrix.one_apply]

instance {R : Type*} [CommRing R] : One (SL2BoundaryMatrix R) :=
  ⟨SL2BoundaryMatrix.identity⟩

instance {R : Type*} [CommRing R] : Mul (SL2BoundaryMatrix R) :=
  ⟨SL2BoundaryMatrix.mul⟩

theorem SL2BoundaryMatrix.one_mul
    {R : Type*} [CommRing R] (M : SL2BoundaryMatrix R) :
    (1 : SL2BoundaryMatrix R).mul M = M := by
  apply SL2BoundaryMatrix.ext
  change SL2BoundaryMatrix.identity.matrix * M.matrix = M.matrix
  rw [SL2BoundaryMatrix.identity_matrix, Matrix.one_mul]

theorem SL2BoundaryMatrix.mul_one
    {R : Type*} [CommRing R] (M : SL2BoundaryMatrix R) :
    M.mul (1 : SL2BoundaryMatrix R) = M := by
  apply SL2BoundaryMatrix.ext
  change M.matrix * SL2BoundaryMatrix.identity.matrix = M.matrix
  rw [SL2BoundaryMatrix.identity_matrix, Matrix.mul_one]

theorem SL2BoundaryMatrix.mul_assoc
    {R : Type*} [CommRing R]
    (A B C : SL2BoundaryMatrix R) :
    (A.mul B).mul C = A.mul (B.mul C) := by
  apply SL2BoundaryMatrix.ext
  simp [SL2BoundaryMatrix.mul, Matrix.mul_assoc]

instance {R : Type*} [CommRing R] : Monoid (SL2BoundaryMatrix R) where
  one := 1
  mul := (· * ·)
  one_mul := SL2BoundaryMatrix.one_mul
  mul_one := SL2BoundaryMatrix.mul_one
  mul_assoc := SL2BoundaryMatrix.mul_assoc

def SL2BoundaryMatrix.inv
    {R : Type*} [CommRing R]
    (M : SL2BoundaryMatrix R) : SL2BoundaryMatrix R where
  matrix := !![M.matrix 1 1, -M.matrix 0 1;
    -M.matrix 1 0, M.matrix 0 0]
  det_eq_one := by
    simp [det2]
    simpa [mul_comm] using M.det_eq_one

instance {R : Type*} [CommRing R] : Inv (SL2BoundaryMatrix R) :=
  ⟨SL2BoundaryMatrix.inv⟩

theorem SL2BoundaryMatrix.mul_inv
    {R : Type*} [CommRing R] (M : SL2BoundaryMatrix R) :
    M * M⁻¹ = (1 : SL2BoundaryMatrix R) := by
  change SL2BoundaryMatrix.mul M (SL2BoundaryMatrix.inv M) =
    SL2BoundaryMatrix.identity
  dsimp [SL2BoundaryMatrix.mul, SL2BoundaryMatrix.inv,
    SL2BoundaryMatrix.identity]
  apply SL2BoundaryMatrix.ext
  ext i j <;> fin_cases i <;> fin_cases j
  · calc
      _ = det2 M.matrix := by
        simp [Matrix.mul_apply, Fin.sum_univ_two, det2]
        ring
      _ = 1 := by
        simpa [det2, sub_eq_add_neg, add_comm] using M.det_eq_one
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · calc
      _ = det2 M.matrix := by
        simp [Matrix.mul_apply, Fin.sum_univ_two, det2]
        ring
      _ = 1 := M.det_eq_one

theorem SL2BoundaryMatrix.inv_mul
    {R : Type*} [CommRing R] (M : SL2BoundaryMatrix R) :
    M⁻¹ * M = (1 : SL2BoundaryMatrix R) := by
  change SL2BoundaryMatrix.mul (SL2BoundaryMatrix.inv M) M =
    SL2BoundaryMatrix.identity
  dsimp [SL2BoundaryMatrix.mul, SL2BoundaryMatrix.inv,
    SL2BoundaryMatrix.identity]
  apply SL2BoundaryMatrix.ext
  ext i j <;> fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, det2, sub_eq_add_neg, mul_comm] using M.det_eq_one
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, det2, sub_eq_add_neg,
      add_comm, mul_comm] using M.det_eq_one

instance {R : Type*} [CommRing R] : Group (SL2BoundaryMatrix R) where
  one := 1
  mul := (· * ·)
  inv := (·⁻¹)
  one_mul := SL2BoundaryMatrix.one_mul
  mul_one := SL2BoundaryMatrix.mul_one
  mul_assoc := SL2BoundaryMatrix.mul_assoc
  inv_mul_cancel := SL2BoundaryMatrix.inv_mul

theorem SL2BoundaryMatrix.identity_applyPair
    {R : Type*} [CommRing R] (p : UnimodularPair R) :
    SL2BoundaryMatrix.identity.applyPair p = p := by
  ext <;> simp [SL2BoundaryMatrix.identity, SL2BoundaryMatrix.applyPair]

theorem SL2BoundaryMatrix.identity_onBoundary
    {R : Type*} [CommRing R] (p : ProjectiveBoundary R) :
    SL2BoundaryMatrix.identity.onBoundary p = p := by
  refine Quotient.inductionOn p ?_
  intro q
  simpa [SL2BoundaryMatrix.onBoundary_mk] using
    congrArg projectiveBoundaryMk (SL2BoundaryMatrix.identity_applyPair q)

structure SL2BoundaryFlow (R : Type*) [CommRing R] where
  act : ℝ → SL2BoundaryMatrix R
  zero_law : act 0 = SL2BoundaryMatrix.identity
  add_law : ∀ s t : ℝ,
    act (s + t) = (act s).mul (act t)

theorem SL2BoundaryFlow.act_neg_mul_act
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) :
    Φ.act (-t) * Φ.act t = (1 : SL2BoundaryMatrix R) := by
  change (Φ.act (-t)).mul (Φ.act t) = SL2BoundaryMatrix.identity
  rw [← Φ.add_law (-t) t, neg_add_cancel, Φ.zero_law]

theorem SL2BoundaryFlow.act_mul_act_neg
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) :
    Φ.act t * Φ.act (-t) = (1 : SL2BoundaryMatrix R) := by
  change (Φ.act t).mul (Φ.act (-t)) = SL2BoundaryMatrix.identity
  rw [← Φ.add_law t (-t), add_neg_cancel, Φ.zero_law]

def SL2BoundaryFlow.onBoundary
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) :
    ProjectiveBoundary R → ProjectiveBoundary R :=
  (Φ.act t).onBoundary

theorem SL2BoundaryFlow.onBoundary_zero
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (p : ProjectiveBoundary R) :
    Φ.onBoundary 0 p = p := by
  rw [SL2BoundaryFlow.onBoundary, Φ.zero_law]
  exact SL2BoundaryMatrix.identity_onBoundary p

theorem SL2BoundaryFlow.onBoundary_neg_add
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) (p : ProjectiveBoundary R) :
    Φ.onBoundary (-t) (Φ.onBoundary t p) = p := by
  change (Φ.act (-t)).onBoundary ((Φ.act t).onBoundary p) = p
  calc
    (Φ.act (-t)).onBoundary ((Φ.act t).onBoundary p) =
        ((Φ.act (-t)).mul (Φ.act t)).onBoundary p := by
          symm
          exact SL2BoundaryMatrix.mul_onBoundary (Φ.act (-t)) (Φ.act t) p
    _ = p := by
      have h := Φ.act_neg_mul_act t
      change (Φ.act (-t)).mul (Φ.act t) = SL2BoundaryMatrix.identity at h
      rw [h]
      exact SL2BoundaryMatrix.identity_onBoundary p

theorem SL2BoundaryFlow.onBoundary_add_neg
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (t : ℝ) (p : ProjectiveBoundary R) :
    Φ.onBoundary t (Φ.onBoundary (-t) p) = p := by
  change (Φ.act t).onBoundary ((Φ.act (-t)).onBoundary p) = p
  calc
    (Φ.act t).onBoundary ((Φ.act (-t)).onBoundary p) =
        ((Φ.act t).mul (Φ.act (-t))).onBoundary p := by
          symm
          exact SL2BoundaryMatrix.mul_onBoundary (Φ.act t) (Φ.act (-t)) p
    _ = p := by
      have h := Φ.act_mul_act_neg t
      change (Φ.act t).mul (Φ.act (-t)) = SL2BoundaryMatrix.identity at h
      rw [h]
      exact SL2BoundaryMatrix.identity_onBoundary p

theorem SL2BoundaryFlow.onBoundary_add
    {R : Type*} [CommRing R]
    (Φ : SL2BoundaryFlow R) (s t : ℝ) (p : ProjectiveBoundary R) :
    Φ.onBoundary (s + t) p =
      Φ.onBoundary s (Φ.onBoundary t p) := by
  rw [SL2BoundaryFlow.onBoundary, Φ.add_law]
  exact SL2BoundaryMatrix.mul_onBoundary (Φ.act s) (Φ.act t) p

structure ContinuousSL2BoundaryFlow (R : Type*) [CommRing R]
    [TopologicalSpace (ProjectiveBoundary R)] where
  algebraic : SL2BoundaryFlow R
  continuous_action : Continuous
    (fun p : ℝ × ProjectiveBoundary R =>
      algebraic.onBoundary p.1 p.2)

end InfoGeometry.Topology
