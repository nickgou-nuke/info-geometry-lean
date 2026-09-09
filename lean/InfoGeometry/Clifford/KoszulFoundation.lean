import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# InfoGeometry.Clifford.KoszulFoundation

Kernel-checked Clifford-algebra pivot for the supergraded/Koszul lane.

Mathlib already owns the native Clifford algebra, its polar anticommutator, and
its grade involution `CliffordAlgebra.involute`.  This file exposes those facts
under repository-facing names and adds one finite list-product volume-element
calculation.

No Berezinian functor, ABS isomorphism, Dirac index theorem, Bott-periodicity
classification theorem, or tenfold-way physics statement is asserted here.
-/

namespace InfoGeometry.Clifford.KoszulFoundation

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- The native Clifford anticommutator is the polar form of the quadratic form. -/
theorem clifford_polarization (v w : M) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w +
        CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v =
      algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q v w) :=
  CliffordAlgebra.ι_mul_ι_add_swap v w

/-- Orthogonal vectors anticommute in the native Clifford algebra. -/
theorem clifford_orthogonal_anticommute (v w : M) (h : Q.IsOrtho v w) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w =
      -(CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho h

/-- The same anticommutation conclusion from an explicit polar-zero hypothesis. -/
theorem clifford_anticommute_of_polar_eq_zero
    (v w : M) (h : QuadraticMap.polar Q v w = 0) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w =
      -(CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) := by
  have hsum := clifford_polarization (Q := Q) v w
  rw [h, map_zero] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

/-- Mathlib's grade involution sends a vector generator to its negative. -/
theorem clifford_involute_ι (v : M) :
    CliffordAlgebra.involute (CliffordAlgebra.ι Q v) = -CliffordAlgebra.ι Q v :=
  CliffordAlgebra.involute_ι v

/-- Mathlib's grade involution is an involution. -/
theorem clifford_involute_involutive (x : CliffordAlgebra Q) :
    CliffordAlgebra.involute (CliffordAlgebra.involute x) = x :=
  CliffordAlgebra.involute_involute x

/-- The product of two vector generators is even under the grade involution. -/
theorem clifford_involute_two_vectors (v w : M) :
    CliffordAlgebra.involute (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) =
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w := by
  rw [map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_ι]
  rw [neg_mul, mul_neg, neg_neg]

/-- Ordered finite product of Clifford generators attached to a list of vectors. -/
def cliffordVolumeElement (Q : QuadraticForm R M) (vectors : List M) : CliffordAlgebra Q :=
  (vectors.map (CliffordAlgebra.ι Q)).prod

/-- The empty list has unit volume element. -/
theorem cliffordVolumeElement_nil :
    cliffordVolumeElement Q [] = (1 : CliffordAlgebra Q) := by
  change (List.map (CliffordAlgebra.ι Q) []).prod = (1 : CliffordAlgebra Q)
  rfl

/-- Prepending a vector left-multiplies the finite volume element by its Clifford image. -/
theorem cliffordVolumeElement_cons (v : M) (vectors : List M) :
    cliffordVolumeElement Q (v :: vectors) =
      CliffordAlgebra.ι Q v * cliffordVolumeElement Q vectors := by
  change (CliffordAlgebra.ι Q v :: List.map (CliffordAlgebra.ι Q) vectors).prod =
      CliffordAlgebra.ι Q v * (List.map (CliffordAlgebra.ι Q) vectors).prod
  rfl

/--
The grade involution acts on a finite ordered product by the parity of its
length: `involute(e₁⋯eₙ) = (-1)^n • e₁⋯eₙ`.
-/
theorem clifford_involute_volumeElement (vectors : List M) :
    CliffordAlgebra.involute (cliffordVolumeElement Q vectors) =
      (-1 : R) ^ vectors.length • cliffordVolumeElement Q vectors := by
  induction vectors with
  | nil =>
      simp [cliffordVolumeElement]
  | cons v vectors ih =>
      change CliffordAlgebra.involute (CliffordAlgebra.ι Q v * cliffordVolumeElement Q vectors) =
        (-1 : R) ^ (vectors.length + 1) •
          (CliffordAlgebra.ι Q v * cliffordVolumeElement Q vectors)
      rw [map_mul, CliffordAlgebra.involute_ι, ih]
      rw [pow_succ]
      simp only [Algebra.smul_def, map_mul, map_neg, map_one]
      rw [mul_neg_one]
      rw [neg_mul, neg_mul]
      congr 1
      rw [← mul_assoc]
      rw [← Algebra.commutes ((-1 : R) ^ vectors.length) (CliffordAlgebra.ι Q v)]
      rw [mul_assoc]

/-- A vector orthogonal to each factor in a finite ordered product anticommutes with the whole product. -/
theorem clifford_anticommute_listProduct
    (v : M) (vectors : List M) (h : ∀ w ∈ vectors, Q.IsOrtho v w) :
    CliffordAlgebra.ι Q v * (vectors.map (CliffordAlgebra.ι Q)).prod =
      (-1 : R) ^ vectors.length •
        ((vectors.map (CliffordAlgebra.ι Q)).prod * CliffordAlgebra.ι Q v) := by
  induction vectors with
  | nil => simp
  | cons w ws ih =>
      have hw : Q.IsOrtho v w := h w (by simp)
      have hws : ∀ x ∈ ws, Q.IsOrtho v x := fun x hx => h x (by simp [hx])
      rw [List.map_cons, List.prod_cons]
      calc
        CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q w * (ws.map (CliffordAlgebra.ι Q)).prod)
            = (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) * (ws.map (CliffordAlgebra.ι Q)).prod := by
                rw [mul_assoc]
        _ = -((CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v) * (ws.map (CliffordAlgebra.ι Q)).prod) := by
                rw [clifford_orthogonal_anticommute (Q := Q) v w hw, neg_mul]
        _ = - (CliffordAlgebra.ι Q w * (CliffordAlgebra.ι Q v * (ws.map (CliffordAlgebra.ι Q)).prod)) := by
                rw [mul_assoc]
        _ = - (CliffordAlgebra.ι Q w * ((-1 : R) ^ ws.length • ((ws.map (CliffordAlgebra.ι Q)).prod * CliffordAlgebra.ι Q v))) := by
                rw [ih hws]
        _ = (-1 : R) ^ ws.length.succ • ((CliffordAlgebra.ι Q w * (ws.map (CliffordAlgebra.ι Q)).prod) * CliffordAlgebra.ι Q v) := by
                simp [pow_succ, mul_assoc]

/--
A `List.Pairwise` orthogonality hypothesis on `v :: vectors` supplies the
head-to-tail hypotheses needed to move `ι Q v` through the volume element.
-/
theorem clifford_anticommute_listProduct_of_pairwise_cons
    (v : M) (vectors : List M)
    (h : List.Pairwise (fun x y => Q.IsOrtho x y) (v :: vectors)) :
    CliffordAlgebra.ι Q v * cliffordVolumeElement Q vectors =
      (-1 : R) ^ vectors.length •
        (cliffordVolumeElement Q vectors * CliffordAlgebra.ι Q v) :=
  clifford_anticommute_listProduct v vectors
    (fun _ hw => List.rel_of_pairwise_cons h hw)

/-
Adjoining a vector orthogonal to every factor gives the recursive square law
for an ordered Clifford volume element.  The sign records the number of
factors crossed before the two copies of the new generator meet.
-/
theorem cliffordVolumeElement_cons_sq
    (v : M) (vectors : List M) (h : ∀ w ∈ vectors, Q.IsOrtho v w) :
    cliffordVolumeElement Q (v :: vectors) * cliffordVolumeElement Q (v :: vectors) =
      (-1 : R) ^ vectors.length •
        (algebraMap R (CliffordAlgebra Q) (Q v) *
          (cliffordVolumeElement Q vectors * cliffordVolumeElement Q vectors)) := by
  let V := cliffordVolumeElement Q vectors
  let s : R := (-1 : R) ^ vectors.length
  have hmove : CliffordAlgebra.ι Q v * V = s • (V * CliffordAlgebra.ι Q v) := by
    exact clifford_anticommute_listProduct v vectors h
  have hs : s * s = 1 := by
    simp [s, ← pow_add]
  have hmove' : V * CliffordAlgebra.ι Q v = s • (CliffordAlgebra.ι Q v * V) := by
    calc
      V * CliffordAlgebra.ι Q v = (1 : R) • (V * CliffordAlgebra.ι Q v) := by simp
      _ = (s * s) • (V * CliffordAlgebra.ι Q v) := by rw [hs]
      _ = s • (s • (V * CliffordAlgebra.ι Q v)) := by simp [mul_smul]
      _ = s • (CliffordAlgebra.ι Q v * V) := by rw [← hmove]
  rw [cliffordVolumeElement_cons]
  calc
    (CliffordAlgebra.ι Q v * V) * (CliffordAlgebra.ι Q v * V) =
        CliffordAlgebra.ι Q v * (V * CliffordAlgebra.ι Q v) * V := by
          simp only [mul_assoc]
    _ = CliffordAlgebra.ι Q v * (s • (CliffordAlgebra.ι Q v * V)) * V := by
          rw [hmove']
    _ = s • ((CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) * (V * V)) := by
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          congr 1
          simp only [mul_assoc]
    _ = s • (algebraMap R (CliffordAlgebra Q) (Q v) * (V * V)) := by
          rw [CliffordAlgebra.ι_sq_scalar]

/-! Scalar recursion for the square of an orthogonal ordered Clifford product. -/
def cliffordVolumeSquareScalar (Q : QuadraticForm R M) : List M → R
  | [] => 1
  | v :: vectors =>
      (-1 : R) ^ vectors.length * Q v * cliffordVolumeSquareScalar Q vectors

theorem cliffordVolumeElement_sq_of_pairwise
    (vectors : List M) (h : vectors.Pairwise (fun v w => Q.IsOrtho v w)) :
    cliffordVolumeElement Q vectors * cliffordVolumeElement Q vectors =
      algebraMap R (CliffordAlgebra Q) (cliffordVolumeSquareScalar Q vectors) := by
  induction vectors with
  | nil => simp [cliffordVolumeElement, cliffordVolumeSquareScalar]
  | cons v vectors ih =>
      rw [cliffordVolumeElement_cons_sq v vectors
        (fun w hw => List.rel_of_pairwise_cons h hw)]
      rw [ih (List.pairwise_cons.mp h).2]
      simp [cliffordVolumeSquareScalar, Algebra.smul_def, mul_assoc]

/-- Even-length ordered Clifford products are fixed by the grade involution. -/
theorem clifford_involute_volumeElement_of_even_length
    (vectors : List M) (h : Even vectors.length) :
    CliffordAlgebra.involute (cliffordVolumeElement Q vectors) =
      cliffordVolumeElement Q vectors := by
  rw [clifford_involute_volumeElement, h.neg_one_pow]
  simp

/-- Odd-length ordered Clifford products change sign under the grade involution. -/
theorem clifford_involute_volumeElement_of_odd_length
    (vectors : List M) (h : Odd vectors.length) :
    CliffordAlgebra.involute (cliffordVolumeElement Q vectors) =
      -cliffordVolumeElement Q vectors := by
  rw [clifford_involute_volumeElement, h.neg_one_pow]
  simp [Algebra.smul_def]

end InfoGeometry.Clifford.KoszulFoundation
