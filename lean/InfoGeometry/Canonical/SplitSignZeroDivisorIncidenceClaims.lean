import InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
import InfoGeometry.Arithmetic.HestenesKreinChiralProjectors
import InfoGeometry.Canonical.SplitQuaternionMatrixModel
import InfoGeometry.Canonical.SplitOctonionClassification
import InfoGeometry.Canonical.SplitOctonionClassificationCore
import InfoGeometry.Tessellation.Incidence

/-!
# Split sign, idempotents, incidence, and Zorn witness claims

This file collects the theorem-safe statements that are already formalized in
the repository and that match the text's legitimate mathematics:

* the split sign has explicit nonzero zero divisors;
* those split factors are not nilpotent;
* the split chiral projectors are orthogonal idempotents;
* supported corner incidence is square-zero;
* explicit Zorn commutator and associator witnesses exist.

It does **not** claim the stronger unproved classification statements:
`commutant = scalars`, `nucleus = scalars`, `Der(O_s) ≅ g₂(2)`, or any `E₈(8)`
identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitSignZeroDivisorIncidenceClaims

open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics
open InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex
open InfoGeometry.Arithmetic.HestenesKreinChiralProjectors
open InfoGeometry.Canonical.SplitQuaternionMatrixModel
open InfoGeometry.Canonical.SplitOctonionClassification
open InfoGeometry.Canonical.SplitOctonionClassificationCore
open InfoGeometry.Tessellation

/-- Split sign gives explicit nonzero zero divisors. -/
theorem split_sign_has_nonzero_zero_divisors :
    ∃ u v : SplitComplex, u ≠ zero ∧ v ≠ zero ∧ mul u v = zero :=
  InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.split_sign_has_nonzero_zero_divisors

/-- The split-sign zero divisors are not nilpotent. -/
theorem split_sign_zero_divisors_not_nilpotent :
    mul (add one j) (add one j) ≠ zero ∧
      mul (add one (neg j)) (add one (neg j)) ≠ zero := by
  exact ⟨one_add_j_sq_ne_zero, one_sub_j_sq_ne_zero⟩

/-- The split chiral projectors are orthogonal idempotents. -/
theorem split_projectors_orthogonal_idempotent :
    splitIdempotentPlus * splitIdempotentPlus = splitIdempotentPlus ∧
      splitIdempotentMinus * splitIdempotentMinus = splitIdempotentMinus ∧
      splitIdempotentPlus * splitIdempotentMinus = 0 ∧
      splitIdempotentMinus * splitIdempotentPlus = 0 := by
  exact ⟨splitIdempotentPlus_sq, splitIdempotentMinus_sq,
    splitIdempotentPlus_mul_minus, splitIdempotentMinus_mul_plus⟩

/-- The split Krein spine: generator square, idempotents, and square-zero hops. -/
theorem splitKreinSpine_claim :
    splitComplexEpsilon * splitComplexEpsilon = (1 : Mat2)
      ∧ splitIdempotentPlus * splitIdempotentPlus = splitIdempotentPlus
      ∧ splitIdempotentMinus * splitIdempotentMinus = splitIdempotentMinus
      ∧ splitIdempotentPlus * splitIdempotentMinus = 0
      ∧ splitIdempotentMinus * splitIdempotentPlus = 0
      ∧ splitNilpotentPlus * splitNilpotentPlus = 0
      ∧ splitNilpotentMinus * splitNilpotentMinus = 0 :=
  InfoGeometry.Canonical.SplitQuaternionMatrixModel.splitKreinSpine

/-- Supported corner incidence is square-zero. -/
theorem supported_corner_incidence_square_zero
    {A : Type*} [Semiring A]
    {src tgt : Diamond A}
    (L : SupportedLightray A src tgt) :
    L.N * L.N = 0 :=
  Tessellation.supported_lightray_square_zero L

/-- A non-scalar Zorn element has a nonzero commutator witness. -/
theorem non_scalar_has_nonzero_commutator
    {R : Type*} [CommRing R]
    {x : InfoGeometry.Canonical.ZornMatrix R}
    (hx : ¬ ∃ r : R, x = r • (1 : InfoGeometry.Canonical.ZornMatrix R)) :
    ∃ y : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.commutator (R := R) x y ≠ 0 :=
  InfoGeometry.Canonical.SplitOctonionClassification.ZornMatrix.exists_nonzero_commutator_of_not_scalar
    (R := R) (x := x) hx

/--
The concrete associator witness currently formalized in the explicit Zorn core:
if the `y`-vector is nonzero, there exists a nonzero associator witness.
-/
theorem nonzero_associator_of_y_ne_zero
    {R : Type*} [CommRing R]
    (x : InfoGeometry.Canonical.ZornMatrix R)
    (hy : x.y ≠ 0) :
    ∃ y z : InfoGeometry.Canonical.ZornMatrix R,
      SplitOctonionClassificationCore.ZornMatrix.associator (R := R) x y z ≠ 0 :=
  SplitOctonionClassificationCore.ZornMatrix.nonzero_associator_of_y_ne_zero (R := R) x hy

end InfoGeometry.Canonical.SplitSignZeroDivisorIncidenceClaims
