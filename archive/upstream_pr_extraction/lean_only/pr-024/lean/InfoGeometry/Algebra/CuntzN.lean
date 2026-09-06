import Mathlib
import InfoGeometry.Algebra.GenericDirac

/-!
# Cuntz-N Algebra — Finite Hodge-Dirac Operator

General Cuntz algebra O_N with N isometries S_1,…,S_N on a *-ring.
The Dirac operator is D = Σ_i (S_i + S*_i). Proved self-adjoint.

For O_∞ indexed by primes: D_β = Σ_p p^{-β}(S_p + S*_p), Boltzmann regularized.

Uses the same abstract star-ring approach as `CuntzCantorSpectralTriple.lean`.
-/

namespace InfoGeometry.Algebra.Cuntz

variable {N : ℕ}

/--
**Cuntz algebra O_N** on a star ring.

  S*_i·S_j = δ_{ij}·1    (isometries with orthogonal ranges)
  Σ_i S_i·S*_i = 1         (completeness / range sum)
-/
structure CuntzNAlgebra (Op : Type*) [Ring Op] [StarRing Op] where
  S : Fin N → Op
  isometry : ∀ i j, star (S i) * (S j) = if i = j then 1 else 0
  range_sum : ∑ i : Fin N, (S i) * star (S i) = 1

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (O : CuntzNAlgebra (N := N) Op)

/--
**Discrete Hodge-Dirac operator for O_N**.

  D = Σ_{i=1}^N (S_i + S*_i)
-/
def hodgeDirac : Op :=
  finiteDirac O.S

/--
**Self-adjointness of the Hodge-Dirac operator (PROVED).**

  D* = Σ (S_i + S*_i)* = Σ (S*_i + S_i) = Σ (S_i + S*_i) = D.
-/
theorem hodge_dirac_self_adjoint : star (hodgeDirac O) = hodgeDirac O := by
  exact (finiteDirac_selfAdjoint O.S).star_eq

/--
**Idempotence of range projections (PROVED).**

  P_i = S_i·S*_i,  P_i² = P_i.
-/
theorem range_projection_idempotent (i : Fin N) :
    (O.S i * star (O.S i)) * (O.S i * star (O.S i)) = O.S i * star (O.S i) := by
  have h_isom : star (O.S i) * (O.S i) = 1 := by
    simpa using O.isometry i i
  calc
    (O.S i * star (O.S i)) * (O.S i * star (O.S i))
        = O.S i * (star (O.S i) * (O.S i)) * star (O.S i) := by noncomm_ring
    _ = O.S i * 1 * star (O.S i) := by rw [h_isom]
    _ = O.S i * star (O.S i) := by simp

/--
**Orthogonality of range projections for i ≠ j (PROVED).**

  P_i·P_j = 0.
-/
theorem range_projection_orthogonal (i j : Fin N) (hij : i ≠ j) :
    (O.S i * star (O.S i)) * (O.S j * star (O.S j)) = 0 := by
  have h_orth : star (O.S i) * (O.S j) = 0 := by
    simpa [hij] using O.isometry i j
  calc
    (O.S i * star (O.S i)) * (O.S j * star (O.S j))
        = O.S i * (star (O.S i) * (O.S j)) * star (O.S j) := by noncomm_ring
    _ = O.S i * 0 * star (O.S j) := by rw [h_orth]
    _ = 0 := by simp

/--
**Completeness: Σ_i P_i = 1 (PROVED).**
-/
theorem range_projections_sum_one :
    ∑ i : Fin N, (O.S i) * star (O.S i) = 1 :=
  O.range_sum

/-! ## Tensor-algebra quotient presentation -/

inductive CuntzSymbol (N : ℕ) where
  | generator : Fin N → CuntzSymbol N
  | adjoint : Fin N → CuntzSymbol N
deriving DecidableEq

abbrev CuntzGeneratorModule (R : Type*) [Zero R] (N : ℕ) : Type _ :=
  CuntzSymbol N →₀ R

abbrev CuntzTensorAlgebra (R : Type*) [CommSemiring R] (N : ℕ) : Type _ :=
  TensorAlgebra R (CuntzGeneratorModule R N)

noncomputable def cuntzGeneratorVector {R : Type*} [Zero R] [One R] {N : ℕ} (i : Fin N) :
    CuntzGeneratorModule R N :=
  Finsupp.single (CuntzSymbol.generator i) 1

noncomputable def cuntzAdjointVector {R : Type*} [Zero R] [One R] {N : ℕ} (i : Fin N) :
    CuntzGeneratorModule R N :=
  Finsupp.single (CuntzSymbol.adjoint i) 1

noncomputable def cuntzTensorGenerator {R : Type*} [CommSemiring R] {N : ℕ} (i : Fin N) :
    CuntzTensorAlgebra R N :=
  TensorAlgebra.ι R (cuntzGeneratorVector (R := R) i)

noncomputable def cuntzTensorAdjoint {R : Type*} [CommSemiring R] {N : ℕ} (i : Fin N) :
    CuntzTensorAlgebra R N :=
  TensorAlgebra.ι R (cuntzAdjointVector (R := R) i)

inductive CuntzTensorRel (R : Type*) [CommRing R] (N : ℕ) :
    CuntzTensorAlgebra R N → CuntzTensorAlgebra R N → Prop where
  | isometry (i j : Fin N) :
      CuntzTensorRel R N
        (cuntzTensorAdjoint (R := R) i * cuntzTensorGenerator (R := R) j)
        (if i = j then (1 : CuntzTensorAlgebra R N) else 0)
  | range_sum :
      CuntzTensorRel R N
        (∑ i : Fin N, cuntzTensorGenerator (R := R) i * cuntzTensorAdjoint (R := R) i)
        1

def CuntzTensorQuotient (R : Type*) [CommRing R] (N : ℕ) : Type _ :=
  RingQuot (CuntzTensorRel R N)
deriving Inhabited, Ring, Algebra R

noncomputable def cuntzQuotientMap {R : Type*} [CommRing R] {N : ℕ} :
    CuntzTensorAlgebra R N →ₐ[R] CuntzTensorQuotient R N :=
  RingQuot.mkAlgHom R (CuntzTensorRel R N)

noncomputable def cuntzQuotientGenerator {R : Type*} [CommRing R] {N : ℕ} (i : Fin N) :
    CuntzTensorQuotient R N :=
  cuntzQuotientMap (R := R) (N := N) (cuntzTensorGenerator (R := R) i)

noncomputable def cuntzQuotientAdjoint {R : Type*} [CommRing R] {N : ℕ} (i : Fin N) :
    CuntzTensorQuotient R N :=
  cuntzQuotientMap (R := R) (N := N) (cuntzTensorAdjoint (R := R) i)

@[simp]
theorem cuntzQuotient_isometry {R : Type*} [CommRing R] {N : ℕ} (i j : Fin N) :
    cuntzQuotientAdjoint (R := R) i * cuntzQuotientGenerator (R := R) j =
      if i = j then (1 : CuntzTensorQuotient R N) else 0 := by
  simpa [cuntzQuotientAdjoint, cuntzQuotientGenerator, cuntzQuotientMap]
    using RingQuot.mkAlgHom_rel R (CuntzTensorRel.isometry (R := R) (N := N) i j)

@[simp]
theorem cuntzQuotient_range_sum {R : Type*} [CommRing R] (N : ℕ) :
    ∑ i : Fin N, cuntzQuotientGenerator (R := R) i * cuntzQuotientAdjoint (R := R) i =
      1 := by
  simpa [cuntzQuotientGenerator, cuntzQuotientAdjoint, cuntzQuotientMap]
    using RingQuot.mkAlgHom_rel R (CuntzTensorRel.range_sum (R := R) (N := N))

structure AlgebraicCuntzNPresentation (R : Type*) [CommSemiring R] (N : ℕ)
    (A : Type*) [Semiring A] [Algebra R A] where
  S : Fin N → A
  T : Fin N → A
  isometry : ∀ i j, T i * S j = if i = j then 1 else 0
  range_sum : ∑ i : Fin N, S i * T i = 1

noncomputable def algebraicCuntzSymbolMap {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) :
    CuntzGeneratorModule R N →ₗ[R] A :=
  Finsupp.linearCombination R fun
    | CuntzSymbol.generator i => P.S i
    | CuntzSymbol.adjoint i => P.T i

@[simp]
theorem algebraicCuntzSymbolMap_generator {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    algebraicCuntzSymbolMap (R := R) P (cuntzGeneratorVector (R := R) i) = P.S i := by
  simp [algebraicCuntzSymbolMap, cuntzGeneratorVector]

@[simp]
theorem algebraicCuntzSymbolMap_adjoint {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    algebraicCuntzSymbolMap (R := R) P (cuntzAdjointVector (R := R) i) = P.T i := by
  simp [algebraicCuntzSymbolMap, cuntzAdjointVector]

noncomputable def algebraicCuntzTensorLift {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) :
    CuntzTensorAlgebra R N →ₐ[R] A :=
  TensorAlgebra.lift R (algebraicCuntzSymbolMap (R := R) P)

@[simp]
theorem algebraicCuntzTensorLift_generator {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    algebraicCuntzTensorLift (R := R) P (cuntzTensorGenerator (R := R) i) = P.S i := by
  simp [algebraicCuntzTensorLift, cuntzTensorGenerator]

@[simp]
theorem algebraicCuntzTensorLift_adjoint {R : Type*} [CommSemiring R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    algebraicCuntzTensorLift (R := R) P (cuntzTensorAdjoint (R := R) i) = P.T i := by
  simp [algebraicCuntzTensorLift, cuntzTensorAdjoint]

theorem algebraicCuntzTensorLift_respects {R : Type*} [CommRing R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) :
    ∀ ⦃x y : CuntzTensorAlgebra R N⦄, CuntzTensorRel R N x y →
      algebraicCuntzTensorLift (R := R) P x = algebraicCuntzTensorLift (R := R) P y := by
  intro x y h
  induction h with
  | isometry i j =>
      simpa using P.isometry i j
  | range_sum =>
      simpa using P.range_sum

noncomputable def AlgebraicCuntzNPresentation.lift {R : Type*} [CommRing R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) :
    CuntzTensorQuotient R N →ₐ[R] A :=
  RingQuot.liftAlgHom R
    ⟨algebraicCuntzTensorLift (R := R) P, algebraicCuntzTensorLift_respects (R := R) P⟩

@[simp]
theorem AlgebraicCuntzNPresentation.lift_generator {R : Type*} [CommRing R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    P.lift (cuntzQuotientGenerator (R := R) i) = P.S i := by
  change
    ((RingQuot.liftAlgHom R)
      ⟨algebraicCuntzTensorLift (R := R) P, algebraicCuntzTensorLift_respects (R := R) P⟩)
        ((RingQuot.mkAlgHom R (CuntzTensorRel R N)) (cuntzTensorGenerator (R := R) i)) =
      P.S i
  exact (RingQuot.liftAlgHom_mkAlgHom_apply R
      (algebraicCuntzTensorLift (R := R) P)
      (s := CuntzTensorRel R N)
      (algebraicCuntzTensorLift_respects (R := R) P)
      (cuntzTensorGenerator (R := R) i)).trans
    (algebraicCuntzTensorLift_generator (R := R) P i)

@[simp]
theorem AlgebraicCuntzNPresentation.lift_adjoint {R : Type*} [CommRing R] {N : ℕ}
    {A : Type*} [Semiring A] [Algebra R A]
    (P : AlgebraicCuntzNPresentation R N A) (i : Fin N) :
    P.lift (cuntzQuotientAdjoint (R := R) i) = P.T i := by
  change
    ((RingQuot.liftAlgHom R)
      ⟨algebraicCuntzTensorLift (R := R) P, algebraicCuntzTensorLift_respects (R := R) P⟩)
        ((RingQuot.mkAlgHom R (CuntzTensorRel R N)) (cuntzTensorAdjoint (R := R) i)) =
      P.T i
  exact (RingQuot.liftAlgHom_mkAlgHom_apply R
      (algebraicCuntzTensorLift (R := R) P)
      (s := CuntzTensorRel R N)
      (algebraicCuntzTensorLift_respects (R := R) P)
      (cuntzTensorAdjoint (R := R) i)).trans
    (algebraicCuntzTensorLift_adjoint (R := R) P i)

noncomputable def cuntzTensorQuotientPresentation (R : Type*) [CommRing R] (N : ℕ) :
    AlgebraicCuntzNPresentation R N (CuntzTensorQuotient R N) where
  S := cuntzQuotientGenerator (R := R)
  T := cuntzQuotientAdjoint (R := R)
  isometry := cuntzQuotient_isometry (R := R)
  range_sum := cuntzQuotient_range_sum (R := R) N

end InfoGeometry.Algebra.Cuntz
