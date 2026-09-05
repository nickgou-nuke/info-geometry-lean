import InfoGeometry.Exceptional.FreudenthalSymplecticContactGrading

/-!
# Common CAR--CCR representation of the symplectic contact Lie algebra

The common algebraic carrier is

`N -> ((R x F(J) x R) x (R x F(J) x R))`.

The inner doubling carries an exact one-mode CAR representation. The outer
countable coordinate carries the unnormalised algebraic oscillator shifts with
exact CCR. The faithful contact representation acts coefficientwise on both
fermionic sheets and therefore commutes with all universal ladder maps.

No Hilbert completion, adjoint-domain statement, or boundedness assertion is
made here.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

abbrev SymplecticContactSheet :=
  SymplecticContactModule (J := J) × SymplecticContactModule (J := J)

abbrev SymplecticContactCommonCarrier :=
  ℕ → SymplecticContactSheet (J := J)

abbrev SymplecticContactCommonEnd :=
  Module.End ℝ (SymplecticContactCommonCarrier (J := J))

/-- Universal one-mode annihilation on the inner two-sheet carrier. -/
def contactFermionAnnihilation :
    SymplecticContactCommonEnd (J := J) where
  toFun ψ n := ((ψ n).2, 0)
  map_add' ψ φ := by
    funext n
    rfl
  map_smul' c ψ := by
    funext n
    rfl

/-- Universal one-mode creation on the inner two-sheet carrier. -/
def contactFermionCreation :
    SymplecticContactCommonEnd (J := J) where
  toFun ψ n := (0, (ψ n).1)
  map_add' ψ φ := by
    funext n
    rfl
  map_smul' c ψ := by
    funext n
    rfl

@[simp] theorem contactFermionAnnihilation_apply
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    contactFermionAnnihilation ψ n = ((ψ n).2, 0) := rfl

@[simp] theorem contactFermionCreation_apply
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    contactFermionCreation ψ n = (0, (ψ n).1) := rfl

@[simp] theorem contactFermionAnnihilation_sq :
    contactFermionAnnihilation (J := J) *
      contactFermionAnnihilation = 0 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

@[simp] theorem contactFermionCreation_sq :
    contactFermionCreation (J := J) *
      contactFermionCreation = 0 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- Exact one-mode CAR. -/
theorem contactFermion_CAR :
    contactFermionAnnihilation (J := J) *
        contactFermionCreation (J := J) +
      contactFermionCreation (J := J) *
        contactFermionAnnihilation (J := J) = 1 := by
  apply LinearMap.ext
  intro ψ
  funext n
  rcases ψ n with ⟨x, y⟩
  rfl

/-- Algebraic bosonic creation shift on the outer occupation coordinate. -/
def contactBosonCreation :
    SymplecticContactCommonEnd (J := J) where
  toFun ψ n :=
    match n with
    | 0 => 0
    | k + 1 => ψ k
  map_add' ψ φ := by
    funext n
    cases n <;> rfl
  map_smul' c ψ := by
    funext n
    cases n <;> rfl

/-- Algebraic bosonic annihilation shift in the polynomial basis. -/
def contactBosonAnnihilation :
    SymplecticContactCommonEnd (J := J) where
  toFun ψ n := ((n + 1 : ℕ) : ℝ) • ψ (n + 1)
  map_add' ψ φ := by
    funext n
    simp [smul_add]
  map_smul' c ψ := by
    funext n
    simp only [Pi.smul_apply, smul_smul]
    rw [mul_comm]

@[simp] theorem contactBosonCreation_zero
    (ψ : SymplecticContactCommonCarrier (J := J)) :
    contactBosonCreation ψ 0 = 0 := rfl

@[simp] theorem contactBosonCreation_succ
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    contactBosonCreation ψ (n + 1) = ψ n := rfl

@[simp] theorem contactBosonAnnihilation_apply
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    contactBosonAnnihilation ψ n =
      ((n + 1 : ℕ) : ℝ) • ψ (n + 1) := rfl

/-- Exact algebraic Heisenberg CCR. -/
theorem contactBoson_CCR :
    contactBosonAnnihilation (J := J) *
        contactBosonCreation (J := J) -
      contactBosonCreation (J := J) *
        contactBosonAnnihilation (J := J) = 1 := by
  apply LinearMap.ext
  intro ψ
  funext n
  change contactBosonAnnihilation (contactBosonCreation ψ) n -
      contactBosonCreation (contactBosonAnnihilation ψ) n = ψ n
  cases n with
  | zero =>
      change (1 : ℝ) • ψ 0 - 0 = ψ 0
      simp
  | succ n =>
      change (((n + 2 : ℕ) : ℝ) • ψ (n + 1)) -
          (((n + 1 : ℕ) : ℝ) • ψ (n + 1)) = ψ (n + 1)
      rw [← sub_smul]
      have hscalar :
          (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) = 1 := by
        norm_num
      rw [hscalar, one_smul]

/-- Fermionic annihilation commutes with bosonic creation. -/
theorem contactFermionAnnihilation_commutes_bosonCreation :
    contactFermionAnnihilation (J := J) *
        contactBosonCreation (J := J) =
      contactBosonCreation (J := J) *
        contactFermionAnnihilation (J := J) := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n <;> rfl

/-- Fermionic creation commutes with bosonic creation. -/
theorem contactFermionCreation_commutes_bosonCreation :
    contactFermionCreation (J := J) * contactBosonCreation (J := J) =
      contactBosonCreation (J := J) * contactFermionCreation (J := J) := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n <;> rfl

/-- Fermionic annihilation commutes with bosonic annihilation. -/
theorem contactFermionAnnihilation_commutes_bosonAnnihilation :
    contactFermionAnnihilation (J := J) *
        contactBosonAnnihilation (J := J) =
      contactBosonAnnihilation (J := J) *
        contactFermionAnnihilation (J := J) := by
  apply LinearMap.ext
  intro ψ
  funext n
  change (((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).2, 0) =
    ((n + 1 : ℕ) : ℝ) • ((ψ (n + 1)).2, 0)
  rfl

/-- Fermionic creation commutes with bosonic annihilation. -/
theorem contactFermionCreation_commutes_bosonAnnihilation :
    contactFermionCreation (J := J) *
        contactBosonAnnihilation (J := J) =
      contactBosonAnnihilation (J := J) *
        contactFermionCreation (J := J) := by
  apply LinearMap.ext
  intro ψ
  funext n
  change (0, ((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).1) =
    ((n + 1 : ℕ) : ℝ) • (0, (ψ (n + 1)).1)
  rfl

/-- Diagonal coefficientwise lift of a contact-module endomorphism. -/
def symplecticContactCommonLift :
    SymplecticContactEnd (J := J) →ₗ[ℝ]
      SymplecticContactCommonEnd (J := J) where
  toFun T :=
    { toFun := fun ψ n => (T (ψ n).1, T (ψ n).2)
      map_add' := by
        intro ψ φ
        funext n
        exact Prod.ext (T.map_add _ _) (T.map_add _ _)
      map_smul' := by
        intro c ψ
        funext n
        exact Prod.ext (T.map_smul c _) (T.map_smul c _) }
  map_add' S T := by
    apply LinearMap.ext
    intro ψ
    funext n
    rfl
  map_smul' c T := by
    apply LinearMap.ext
    intro ψ
    funext n
    rfl

@[simp] theorem symplecticContactCommonLift_apply
    (T : SymplecticContactEnd (J := J))
    (ψ : SymplecticContactCommonCarrier (J := J)) (n : ℕ) :
    symplecticContactCommonLift T ψ n =
      (T (ψ n).1, T (ψ n).2) := rfl

/-- The coefficientwise lift preserves composition. -/
theorem symplecticContactCommonLift_mul
    (S T : SymplecticContactEnd (J := J)) :
    symplecticContactCommonLift (S * T) =
      symplecticContactCommonLift S * symplecticContactCommonLift T := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- The coefficientwise lift is faithful. -/
theorem symplecticContactCommonLift_injective :
    Function.Injective
      (symplecticContactCommonLift (J := J)) := by
  intro S T hST
  apply LinearMap.ext
  intro x
  let ψ : SymplecticContactCommonCarrier (J := J) :=
    fun _ => (x, 0)
  have h0 := congrArg
    (fun F : SymplecticContactCommonEnd (J := J) => F ψ 0) hST
  simpa [symplecticContactCommonLift, ψ] using
    congrArg (fun q => q.1) h0

/-- The coefficientwise lift as a native Lie homomorphism. -/
def symplecticContactCommonLiftLieHom :
    SymplecticContactEnd (J := J) →ₗ⁅ℝ⁆
      SymplecticContactCommonEnd (J := J) where
  toLinearMap := symplecticContactCommonLift
  map_lie' S T := by
    apply LinearMap.ext
    intro ψ
    funext n
    rfl

/-- The requested common-carrier Lie representation. -/
def symplecticContactCommonRepresentation :
    FiveGradedCarrier D →ₗ⁅ℝ⁆
      SymplecticContactCommonEnd (J := J) :=
  (symplecticContactCommonLiftLieHom (J := J)).comp
    (symplecticContactRepresentationLieHom D)

@[simp] theorem symplecticContactCommonRepresentation_apply
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D u =
      symplecticContactCommonLift
        (symplecticContactRepresentation D u) := rfl

/-- Bracket preservation on the common CAR--CCR carrier. -/
theorem symplecticContactCommonRepresentation_bracket
    (u v : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D ⁅u, v⁆ =
      ⁅symplecticContactCommonRepresentation D u,
        symplecticContactCommonRepresentation D v⁆ :=
  (symplecticContactCommonRepresentation D).map_lie u v

/-- The common-carrier representation remains faithful. -/
theorem symplecticContactCommonRepresentation_injective :
    Function.Injective (symplecticContactCommonRepresentation D) := by
  intro u v huv
  apply symplecticContactRepresentationLieHom_injective D
  apply symplecticContactCommonLift_injective (J := J)
  simpa [symplecticContactCommonRepresentation] using huv

/-- The represented Lie algebra commutes with the universal fermionic
annihilation operator. -/
theorem symplecticContactCommonRepresentation_commutes_fermionAnnihilation
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D u *
        contactFermionAnnihilation (J := J) =
      contactFermionAnnihilation (J := J) *
        symplecticContactCommonRepresentation D u := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- The represented Lie algebra commutes with the universal fermionic creation
operator. -/
theorem symplecticContactCommonRepresentation_commutes_fermionCreation
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D u *
        contactFermionCreation (J := J) =
      contactFermionCreation (J := J) *
        symplecticContactCommonRepresentation D u := by
  apply LinearMap.ext
  intro ψ
  funext n
  rfl

/-- The represented Lie algebra commutes with bosonic creation. -/
theorem symplecticContactCommonRepresentation_commutes_bosonCreation
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D u *
        contactBosonCreation (J := J) =
      contactBosonCreation (J := J) *
        symplecticContactCommonRepresentation D u := by
  apply LinearMap.ext
  intro ψ
  funext n
  cases n <;> rfl

/-- The represented Lie algebra commutes with bosonic annihilation. -/
theorem symplecticContactCommonRepresentation_commutes_bosonAnnihilation
    (u : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D u *
        contactBosonAnnihilation (J := J) =
      contactBosonAnnihilation (J := J) *
        symplecticContactCommonRepresentation D u := by
  apply LinearMap.ext
  intro ψ
  funext n
  change
    (symplecticContactRepresentation D u
        (((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).1),
      symplecticContactRepresentation D u
        (((n + 1 : ℕ) : ℝ) • (ψ (n + 1)).2)) =
    (((n + 1 : ℕ) : ℝ) •
        symplecticContactRepresentation D u (ψ (n + 1)).1,
      ((n + 1 : ℕ) : ℝ) •
        symplecticContactRepresentation D u (ψ (n + 1)).2)
  exact Prod.ext
    ((symplecticContactRepresentation D u).map_smul _ _)
    ((symplecticContactRepresentation D u).map_smul _ _)

/-- Adjoint grade predicate on the common operator target. -/
def SymplecticContactCommonHasGrade
    (k : ℤ) (T : SymplecticContactCommonEnd (J := J)) : Prop :=
  ⁅symplecticContactCommonRepresentation D (symplecticContactEuler D), T⁆ =
    (k : ℝ) • T

/-- Grade-`k` operator eigenspace on the common target. -/
def symplecticContactCommonGradeSpace (k : ℤ) :
    Submodule ℝ (SymplecticContactCommonEnd (J := J)) where
  carrier := {T | SymplecticContactCommonHasGrade D k T}
  zero_mem' := by
    simp [SymplecticContactCommonHasGrade]
  add_mem' := by
    intro S T hS hT
    unfold SymplecticContactCommonHasGrade at hS hT ⊢
    rw [lie_add, hS, hT, smul_add]
  smul_mem' := by
    intro c T hT
    unfold SymplecticContactCommonHasGrade at hT ⊢
    rw [lie_smul, hT]
    simp [smul_smul, mul_comm]

@[simp] theorem mem_symplecticContactCommonGradeSpace
    (k : ℤ) (T : SymplecticContactCommonEnd (J := J)) :
    T ∈ symplecticContactCommonGradeSpace D k ↔
      SymplecticContactCommonHasGrade D k T := Iff.rfl

/-- Operator commutators add represented grades. -/
theorem symplecticContactCommon_lie_mem_grade_add
    {k l : ℤ}
    {S T : SymplecticContactCommonEnd (J := J)}
    (hS : S ∈ symplecticContactCommonGradeSpace D k)
    (hT : T ∈ symplecticContactCommonGradeSpace D l) :
    ⁅S, T⁆ ∈ symplecticContactCommonGradeSpace D (k + l) := by
  unfold SymplecticContactCommonHasGrade at hS hT ⊢
  rw [leibniz_lie, hS, hT, smul_lie, lie_smul, ← add_smul]
  simp only [Int.cast_add]

/-- The common representation preserves every contact grade. -/
theorem symplecticContactCommonRepresentation_preserves_grade
    {k : ℤ} {u : FiveGradedCarrier D}
    (hu : u ∈ symplecticContactGradeSpace D k) :
    symplecticContactCommonRepresentation D u ∈
      symplecticContactCommonGradeSpace D k := by
  change SymplecticContactCommonHasGrade D k
    (symplecticContactCommonRepresentation D u)
  change SymplecticContactHasGrade D k u at hu
  unfold SymplecticContactCommonHasGrade SymplecticContactHasGrade at *
  rw [← symplecticContactCommonRepresentation_bracket, hu, map_smul]

/-- Restricted grade-preserving linear representation. -/
def symplecticContactCommonGradeMap (k : ℤ) :
    symplecticContactGradeSpace D k →ₗ[ℝ]
      symplecticContactCommonGradeSpace D k where
  toFun u :=
    ⟨symplecticContactCommonRepresentation D u.1,
      symplecticContactCommonRepresentation_preserves_grade D u.2⟩
  map_add' u v := by
    apply Subtype.ext
    simp
  map_smul' c u := by
    apply Subtype.ext
    simp

/-- Literal submodule form of `rho(g_k) subseteq g_k^op`. -/
theorem symplecticContactCommonRepresentation_grade_subset
    (k : ℤ) :
    ∀ u ∈ symplecticContactGradeSpace D k,
      symplecticContactCommonRepresentation D u ∈
        symplecticContactCommonGradeSpace D k := by
  intro u hu
  exact symplecticContactCommonRepresentation_preserves_grade D hu

/-- End-to-end representation packet. -/
theorem symplectic_contact_common_CAR_CCR_packet
    (u v : FiveGradedCarrier D) :
    symplecticContactCommonRepresentation D ⁅u, v⁆ =
        ⁅symplecticContactCommonRepresentation D u,
          symplecticContactCommonRepresentation D v⁆ ∧
      Function.Injective (symplecticContactCommonRepresentation D) ∧
      contactFermionAnnihilation (J := J) *
          contactFermionCreation (J := J) +
        contactFermionCreation (J := J) *
          contactFermionAnnihilation (J := J) = 1 ∧
      contactBosonAnnihilation (J := J) *
          contactBosonCreation (J := J) -
        contactBosonCreation (J := J) *
          contactBosonAnnihilation (J := J) = 1 ∧
      symplecticContactCommonRepresentation D u *
          contactFermionCreation (J := J) =
        contactFermionCreation (J := J) *
          symplecticContactCommonRepresentation D u ∧
      symplecticContactCommonRepresentation D u *
          contactBosonCreation (J := J) =
        contactBosonCreation (J := J) *
          symplecticContactCommonRepresentation D u := by
  exact ⟨symplecticContactCommonRepresentation_bracket D u v,
    symplecticContactCommonRepresentation_injective D,
    contactFermion_CAR,
    contactBoson_CCR,
    symplecticContactCommonRepresentation_commutes_fermionCreation D u,
    symplecticContactCommonRepresentation_commutes_bosonCreation D u⟩

end InfoGeometry.Exceptional.Freudenthal
