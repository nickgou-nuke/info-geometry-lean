import Mathlib
import InfoGeometry.Algebra.NonAssocDerivation
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Canonical.ZornQuaternionPeirceCAR

/-!
# Zorn derivation Lie algebra and associative CAR/CCR envelopes

The nonassociative multiplication of the split-octonion Zorn carrier and the
composition product of its linear endomorphisms are different operations.
Nonassociativity of the former does not obstruct either of the following:

* the Leibniz derivations form an ordinary Lie algebra under the commutator of
  endomorphisms;
* associative operator enlargements of the Zorn module carry exact CAR and CCR
  representations.

This file keeps all three carriers explicit:

1. `NativeZorn`, with the nonassociative Zorn product;
2. `NativeZornDerLie`, a Lie subalgebra of `End_R(NativeZorn)`;
3. doubled and countable operator modules, whose endomorphism rings are
   associative and support exact fermionic and bosonic ladder relations.

The CAR operators below act on a two-sheet module `NativeZorn × NativeZorn`.
The CCR operators act on the algebraic sequence module `ℕ → NativeZorn`.
Every Zorn derivation lifts coefficientwise and commutes with these universal
sheet/occupation operators.  Thus the derivation Lie algebra is an even
symmetry algebra of both representations.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope

open InfoGeometry.Algebra
open InfoGeometry.Algebra.NonAssocDerivation
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.ZornQuaternionPeirceCAR

/-! ## 1. The derivation Lie algebra -/

abbrev NativeZorn := InfoGeometry.Algebra.ZornVectorMatrix ℝ
abbrev NativeZornEnd := Module.End ℝ NativeZorn
abbrev NativeZornDerLie :=
  InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ NativeZorn

/-- A derivation in the native Lie carrier satisfies the Leibniz rule for the
nonassociative Zorn multiplication. -/
@[simp] theorem derivationLie_leibniz
    (D : NativeZornDerLie) (x y : NativeZorn) :
    (D : NativeZornEnd) (x * y) =
      (D : NativeZornEnd) x * y + x * (D : NativeZornEnd) y :=
  InfoGeometry.Algebra.NonAssocDerivation.derivations_leibniz
    ℝ NativeZorn D x y

/-- The Lie bracket is composition commutator in the associative endomorphism
algebra, independently of the associativity of the Zorn product. -/
@[simp] theorem derivationLie_bracket_apply
    (D E : NativeZornDerLie) (x : NativeZorn) :
    (((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) x) =
      (D : NativeZornEnd) ((E : NativeZornEnd) x) -
        (E : NativeZornEnd) ((D : NativeZornEnd) x) :=
  InfoGeometry.Algebra.NonAssocDerivation.lie_apply
    ℝ NativeZorn D E x

/-- Closure of the Zorn derivations under the endomorphism commutator. -/
theorem derivationLie_commutator_mem
    (D E : NativeZornDerLie) :
    ⁅(D : NativeZornEnd), (E : NativeZornEnd)⁆ ∈
      InfoGeometry.Algebra.NonAssocDerivation.derivations ℝ NativeZorn :=
  InfoGeometry.Algebra.NonAssocDerivation.commutator_mem
    ℝ NativeZorn D E

/-! ## 2. Exact CAR on the doubled Zorn module -/

abbrev FermionSheetModule := NativeZorn × NativeZorn
abbrev FermionSheetEnd := Module.End ℝ FermionSheetModule

/-- Universal annihilation map on the two-sheet coefficient module:
`a(x₀,x₁) = (x₁,0)`. -/
def fermionAnnihilation : FermionSheetEnd where
  toFun ψ := (ψ.2, 0)
  map_add' := by
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩
    change (x₁ + y₁, 0) = (x₁ + y₁, 0 + 0)
    exact Prod.ext rfl
      (ZornVectorMatrix.zero_add (0 : NativeZorn)).symm
  map_smul' := by
    rintro c ⟨x₀, x₁⟩
    change (c • x₁, 0) = (c • x₁, c • 0)
    exact Prod.ext rfl (ZornVectorMatrix.smul_zero c).symm

/-- Universal creation map on the two-sheet coefficient module:
`a†(x₀,x₁) = (0,x₀)`. -/
def fermionCreation : FermionSheetEnd where
  toFun ψ := (0, ψ.1)
  map_add' := by
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩
    change (0, x₀ + y₀) = (0 + 0, x₀ + y₀)
    exact Prod.ext
      (ZornVectorMatrix.zero_add (0 : NativeZorn)).symm rfl
  map_smul' := by
    rintro c ⟨x₀, x₁⟩
    change (0, c • x₀) = (c • 0, c • x₀)
    exact Prod.ext (ZornVectorMatrix.smul_zero c).symm rfl

@[simp] theorem fermionAnnihilation_apply (x₀ x₁ : NativeZorn) :
    fermionAnnihilation (x₀, x₁) = (x₁, 0) := rfl

@[simp] theorem fermionCreation_apply (x₀ x₁ : NativeZorn) :
    fermionCreation (x₀, x₁) = (0, x₀) := rfl

/-- Fermionic nilpotency in the associative endomorphism algebra. -/
@[simp] theorem fermionAnnihilation_sq :
    fermionAnnihilation * fermionAnnihilation = 0 := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation,
    ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add]

/-- Fermionic nilpotency in the associative endomorphism algebra. -/
@[simp] theorem fermionCreation_sq :
    fermionCreation * fermionCreation = 0 := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation,
    ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add]

/-- Exact one-mode CAR representation on the doubled Zorn module. -/
theorem fermion_CAR :
    fermionAnnihilation * fermionCreation +
      fermionCreation * fermionAnnihilation = 1 := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation,
    ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add,
    ZornVectorMatrix.sub_eq_add_neg]

/-- Number projection onto the occupied sheet. -/
def fermionNumber : FermionSheetEnd :=
  fermionCreation * fermionAnnihilation

@[simp] theorem fermionNumber_apply (x₀ x₁ : NativeZorn) :
    fermionNumber (x₀, x₁) = (0, x₁) := rfl

/-- Standard number-operator weight of the creation map. -/
theorem fermionNumber_comm_creation :
    fermionNumber * fermionCreation -
      fermionCreation * fermionNumber = fermionCreation := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation,
    ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add,
    ZornVectorMatrix.sub_eq_add_neg]

/-- Standard number-operator weight of the annihilation map. -/
theorem fermionNumber_comm_annihilation :
    fermionNumber * fermionAnnihilation -
      fermionAnnihilation * fermionNumber = -fermionAnnihilation := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp [Module.End.mul_apply, fermionAnnihilation, fermionCreation,
    sub_eq_add_neg, ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add]

/-! ## 3. The derivation Lie algebra as the even CAR symmetry -/

/-- Diagonal lift of a Zorn endomorphism to the two-sheet carrier. -/
def diagonalSheetLift (D : NativeZornEnd) : FermionSheetEnd where
  toFun ψ := (D ψ.1, D ψ.2)
  map_add' := by
    intro ψ φ
    exact Prod.ext (map_add D _ _) (map_add D _ _)
  map_smul' := by
    intro c ψ
    exact Prod.ext (map_smul D c _) (map_smul D c _)

@[simp] theorem diagonalSheetLift_apply
    (D : NativeZornEnd) (x₀ x₁ : NativeZorn) :
    diagonalSheetLift D (x₀, x₁) = (D x₀, D x₁) := rfl

/-- The diagonal lift preserves composition. -/
theorem diagonalSheetLift_mul (D E : NativeZornEnd) :
    diagonalSheetLift (D * E) =
      diagonalSheetLift D * diagonalSheetLift E := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  have hD0 : D ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
    change D (0 : NativeZorn) = 0
    exact map_zero D
  simp [Module.End.mul_apply, diagonalSheetLift, fermionAnnihilation,
    hD0]

/-- Hence it preserves the commutator Lie bracket. -/
theorem diagonalSheetLift_commutator (D E : NativeZornEnd) :
    diagonalSheetLift (D * E - E * D) =
      diagonalSheetLift D * diagonalSheetLift E -
        diagonalSheetLift E * diagonalSheetLift D := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  have hD0 : D ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
    change D (0 : NativeZorn) = 0
    exact map_zero D
  simp [Module.End.mul_apply, diagonalSheetLift, fermionCreation,
    hD0]

/-- Every diagonal coefficient endomorphism commutes with the universal
annihilation map. -/
theorem diagonalSheetLift_commutes_annihilation (D : NativeZornEnd) :
    diagonalSheetLift D * fermionAnnihilation =
      fermionAnnihilation * diagonalSheetLift D := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  change (D x₁, D 0) = (D x₁, 0)
  exact Prod.ext rfl (map_zero D)

/-- Every diagonal coefficient endomorphism commutes with the universal
creation map. -/
theorem diagonalSheetLift_commutes_creation (D : NativeZornEnd) :
    diagonalSheetLift D * fermionCreation =
      fermionCreation * diagonalSheetLift D := by
  apply LinearMap.ext
  rintro ⟨x₀, x₁⟩
  simp only [Module.End.mul_apply, diagonalSheetLift_apply,
    fermionCreation_apply]
  exact Prod.ext (map_zero D) rfl

/-- In particular, every split-octonion derivation acts as an even symmetry of
the exact CAR representation. -/
theorem derivation_even_CAR_symmetry (D : NativeZornDerLie) :
    diagonalSheetLift (D : NativeZornEnd) * fermionAnnihilation =
        fermionAnnihilation * diagonalSheetLift (D : NativeZornEnd) ∧
      diagonalSheetLift (D : NativeZornEnd) * fermionCreation =
        fermionCreation * diagonalSheetLift (D : NativeZornEnd) :=
  ⟨diagonalSheetLift_commutes_annihilation (D : NativeZornEnd),
    diagonalSheetLift_commutes_creation (D : NativeZornEnd)⟩

/-! ## 4. Exact CCR on a countable Zorn-valued occupation module -/

abbrev BosonSequenceModule := ℕ → NativeZorn
abbrev BosonSequenceEnd := Module.End ℝ BosonSequenceModule

/-- Unnormalised creation shift `C f (n+1) = f n`. -/
def bosonCreation : BosonSequenceEnd where
  toFun f n :=
    match n with
    | 0 => 0
    | k + 1 => f k
  map_add' := by
    intro f g
    funext n
    cases n <;> simp [ZornVectorMatrix.zero_add, ZornVectorMatrix.add_zero]
  map_smul' := by
    intro c f
    funext n
    cases n <;> simp [ZornVectorMatrix.smul_zero]

/-- Unnormalised annihilation shift `A f n = (n+1) f(n+1)`. -/
def bosonAnnihilation : BosonSequenceEnd where
  toFun f n := ((n + 1 : ℕ) : ℝ) • f (n + 1)
  map_add' := by
    intro f g
    funext n
    simp only [Pi.add_apply, smul_add]
  map_smul' := by
    intro c f
    funext n
    simp only [Pi.smul_apply, smul_smul]
    simp only [RingHom.id_apply]
    rw [mul_comm]

@[simp] theorem bosonCreation_zero (f : BosonSequenceModule) :
    bosonCreation f 0 = 0 := rfl

@[simp] theorem bosonCreation_succ (f : BosonSequenceModule) (n : ℕ) :
    bosonCreation f (n + 1) = f n := rfl

@[simp] theorem bosonAnnihilation_apply
    (f : BosonSequenceModule) (n : ℕ) :
    bosonAnnihilation f n = ((n + 1 : ℕ) : ℝ) • f (n + 1) := rfl

/-- Exact algebraic Heisenberg CCR on the infinite sequence module. -/
theorem boson_CCR :
    bosonAnnihilation * bosonCreation -
      bosonCreation * bosonAnnihilation = 1 := by
  apply LinearMap.ext
  intro f
  funext n
  change bosonAnnihilation (bosonCreation f) n -
      bosonCreation (bosonAnnihilation f) n = f n
  cases n with
  | zero =>
      simp [bosonCreation, bosonAnnihilation,
        ZornVectorMatrix.one_smul, ZornVectorMatrix.zero_add,
        ZornVectorMatrix.add_zero]
  | succ n =>
      change (((n + 2 : ℕ) : ℝ) • f (n + 1)) -
          (((n + 1 : ℕ) : ℝ) • f (n + 1)) = f (n + 1)
      rw [← sub_smul]
      have hscalar :
          (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = 1 := by
        norm_num
      rw [hscalar, one_smul]

/-- Pointwise lift of a Zorn endomorphism to the bosonic occupation module. -/
def pointwiseSequenceLift (D : NativeZornEnd) : BosonSequenceEnd where
  toFun f n := D (f n)
  map_add' := by
    intro f g
    funext n
    exact map_add D _ _
  map_smul' := by
    intro c f
    funext n
    exact map_smul D c _

/-- Coefficient endomorphisms commute with the bosonic creation shift. -/
theorem pointwiseSequenceLift_commutes_creation (D : NativeZornEnd) :
    pointwiseSequenceLift D * bosonCreation =
      bosonCreation * pointwiseSequenceLift D := by
  apply LinearMap.ext
  intro f
  funext n
  cases n with
  | zero =>
      change D 0 = 0
      exact map_zero D
  | succ n =>
      rfl

/-- Coefficient endomorphisms commute with the weighted annihilation shift. -/
theorem pointwiseSequenceLift_commutes_annihilation (D : NativeZornEnd) :
    pointwiseSequenceLift D * bosonAnnihilation =
      bosonAnnihilation * pointwiseSequenceLift D := by
  apply LinearMap.ext
  intro f
  funext n
  change D (((n + 1 : ℕ) : ℝ) • f (n + 1)) =
    ((n + 1 : ℕ) : ℝ) • D (f (n + 1))
  exact map_smul D _ _

/-- Every split-octonion derivation acts as an even symmetry of the exact CCR
representation. -/
theorem derivation_even_CCR_symmetry (D : NativeZornDerLie) :
    pointwiseSequenceLift (D : NativeZornEnd) * bosonCreation =
        bosonCreation * pointwiseSequenceLift (D : NativeZornEnd) ∧
      pointwiseSequenceLift (D : NativeZornEnd) * bosonAnnihilation =
        bosonAnnihilation * pointwiseSequenceLift (D : NativeZornEnd) :=
  ⟨pointwiseSequenceLift_commutes_creation (D : NativeZornEnd),
    pointwiseSequenceLift_commutes_annihilation (D : NativeZornEnd)⟩

/-! ## 5. Separation and combined closure -/

/-- The element-level Peirce contraction and the associative operator CAR are
both exact. They live on different carriers and neither is invalidated by the
ambient Zorn nonassociativity. -/
theorem peirce_and_operator_CAR
    (u v : InfoGeometry.Canonical.ZornVectorMatrixExplicit.Vec3) :
    zornMul (upperRoot u) (lowerRoot v) +
        zornMul (lowerRoot v) (upperRoot u) =
      dot3 u v • zornOne ∧
    fermionAnnihilation * fermionCreation +
        fermionCreation * fermionAnnihilation = 1 :=
  ⟨peirce_CAR u v, fermion_CAR⟩

/-- Compact theorem packet: derivations form a Lie algebra and act evenly on
simultaneous exact CAR and CCR operator representations. -/
theorem zorn_derivation_lie_CAR_CCR_packet
    (D E : NativeZornDerLie) (x y : NativeZorn) :
    (D : NativeZornEnd) (x * y) =
        (D : NativeZornEnd) x * y + x * (D : NativeZornEnd) y ∧
      (((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) x) =
        (D : NativeZornEnd) ((E : NativeZornEnd) x) -
          (E : NativeZornEnd) ((D : NativeZornEnd) x) ∧
      fermionAnnihilation * fermionCreation +
          fermionCreation * fermionAnnihilation = 1 ∧
      bosonAnnihilation * bosonCreation -
          bosonCreation * bosonAnnihilation = 1 ∧
      diagonalSheetLift (D : NativeZornEnd) * fermionCreation =
          fermionCreation * diagonalSheetLift (D : NativeZornEnd) ∧
      pointwiseSequenceLift (D : NativeZornEnd) * bosonCreation =
          bosonCreation * pointwiseSequenceLift (D : NativeZornEnd) := by
  exact ⟨derivationLie_leibniz D x y,
    derivationLie_bracket_apply D E x,
    fermion_CAR,
    boson_CCR,
    diagonalSheetLift_commutes_creation (D : NativeZornEnd),
    pointwiseSequenceLift_commutes_creation (D : NativeZornEnd)⟩

end InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
