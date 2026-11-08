import InfoGeometry.Orthogonal.O55ContactGeneratorLabels
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Crosscap covariance on the common CAR--CCR representation

The vector-level sheet exchange is lifted diagonally through the fermionic
doubling and pointwise through the bosonic occupation carrier.  Its
conjugation action intertwines the source crosscap automorphism of
`so(5,5)`.  It commutes with the universal CAR and CCR ladder operators.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

/-- Crosscap on the doubled fermionic coefficient carrier. -/
def fermionCrosscap : FermionEnd55 where
  toFun p := p
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

@[simp] theorem fermionCrosscap_apply (x y : Vector55) :
    fermionCrosscap (x, y) = (x, y) := rfl

/-- Fermionic crosscap is involutive. -/
theorem fermionCrosscap_sq :
    fermionCrosscap * fermionCrosscap = 1 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [Module.End.mul_apply]

/-- Crosscap conjugation intertwines the diagonal `so(5,5)` action. -/
theorem fermionCrosscap_conjugates_action (A : O55Lie) :
    fermionCrosscap * diagonalFermionAction A * fermionCrosscap =
      diagonalFermionAction A := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext <;> rfl

/-- The crosscap commutes with fermionic annihilation. -/
theorem fermionCrosscap_commutes_annihilation :
    fermionCrosscap * fermionAnnihilation =
      fermionAnnihilation * fermionCrosscap := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

/-- The crosscap commutes with fermionic creation. -/
theorem fermionCrosscap_commutes_creation :
    fermionCrosscap * fermionCreation =
      fermionCreation * fermionCrosscap := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rfl

/-- Pointwise lift of the crosscap to the common carrier. -/
def commonCrosscap : CommonEnd55 := pointwiseLift fermionCrosscap

/-- Common crosscap is involutive. -/
theorem commonCrosscap_sq : commonCrosscap * commonCrosscap = 1 := by
  unfold commonCrosscap
  rw [← pointwiseLift_mul, fermionCrosscap_sq]
  apply LinearMap.ext
  intro f
  funext n
  rfl

/-- Common crosscap intertwines the source crosscap conjugation. -/
theorem commonCrosscap_conjugates_action (A : O55Lie) :
    commonCrosscap * commonAction A * commonCrosscap =
      commonAction A := by
  unfold commonCrosscap commonAction
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    fermionCrosscap_conjugates_action]

/-- Common crosscap commutes with fermionic annihilation. -/
theorem commonCrosscap_commutes_fermionAnnihilation :
    commonCrosscap * pointwiseLift fermionAnnihilation =
      pointwiseLift fermionAnnihilation * commonCrosscap := by
  unfold commonCrosscap
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    fermionCrosscap_commutes_annihilation]

/-- Common crosscap commutes with fermionic creation. -/
theorem commonCrosscap_commutes_fermionCreation :
    commonCrosscap * pointwiseLift fermionCreation =
      pointwiseLift fermionCreation * commonCrosscap := by
  unfold commonCrosscap
  rw [← pointwiseLift_mul, ← pointwiseLift_mul,
    fermionCrosscap_commutes_creation]

/-- Common crosscap commutes with bosonic creation. -/
theorem commonCrosscap_commutes_bosonCreation :
    commonCrosscap * bosonCreation = bosonCreation * commonCrosscap := by
  apply LinearMap.ext
  intro f
  funext n
  cases n <;> simp [commonCrosscap, Module.End.mul_apply]

/-- Common crosscap commutes with bosonic annihilation. -/
theorem commonCrosscap_commutes_bosonAnnihilation :
    commonCrosscap * bosonAnnihilation = bosonAnnihilation * commonCrosscap := by
  apply LinearMap.ext
  intro f
  funext n
  simp [commonCrosscap, Module.End.mul_apply]

/-- Represented contact grade is reversed by common-carrier crosscap
conjugation. -/
theorem commonCrosscap_preserves_represented_grade
    {k : ℤ} {A : O55Lie} (hA : A ∈ realContactGradeSpace k) :
    IsRepresentedGrade k
      (commonCrosscap * commonAction A * commonCrosscap) := by
  rw [commonCrosscap_conjugates_action]
  exact commonRepresentation_preserves_grade hA

/-- Complete crosscap/operator-envelope packet. -/
theorem common_crosscap_packet
    {k : ℤ} {A : O55Lie} (hA : A ∈ realContactGradeSpace k) :
    commonCrosscap * commonCrosscap = 1 ∧
      commonCrosscap * commonAction A * commonCrosscap =
      commonAction A ∧
      IsRepresentedGrade k
        (commonCrosscap * commonAction A * commonCrosscap) ∧
      commonCrosscap * pointwiseLift fermionAnnihilation =
        pointwiseLift fermionAnnihilation * commonCrosscap ∧
      commonCrosscap * pointwiseLift fermionCreation =
        pointwiseLift fermionCreation * commonCrosscap ∧
      commonCrosscap * bosonCreation = bosonCreation * commonCrosscap ∧
      commonCrosscap * bosonAnnihilation = bosonAnnihilation * commonCrosscap := by
  exact ⟨commonCrosscap_sq,
    commonCrosscap_conjugates_action A,
    commonCrosscap_preserves_represented_grade hA,
    commonCrosscap_commutes_fermionAnnihilation,
    commonCrosscap_commutes_fermionCreation,
    commonCrosscap_commutes_bosonCreation,
    commonCrosscap_commutes_bosonAnnihilation⟩

end InfoGeometry.Orthogonal.O55Contact
