import InfoGeometry.NCG.NoncommutativeDifferentialCalculus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.NCG.NoncommutativeNoetherPoisson
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Algebra.Lie.Cochain

set_option linter.unusedSectionVars false

/-! The first two degrees of the Chevalley--Eilenberg differential for
operator-valued forms.  The bracket term is part of the definition: replacing
it by two commuting coordinate derivatives would make this interface unsound
for a noncommutative derivation algebra. -/

namespace InfoGeometry.NCG.DerivationDifferential

open InfoGeometry.NCG.Calculus
open LieModule.Cohomology

abbrev NativeLieOneCochain (R L M : Type*) [CommRing R]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] :=
  LieModule.Cohomology.oneCochain R L M

abbrev NativeLieTwoCochain (R L M : Type*) [CommRing R]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M] :=
  LieModule.Cohomology.twoCochain R L M

theorem nativeCE_d2_d1_zero (R L M : Type*) [CommRing R]
    [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M]
    (f : NativeLieOneCochain R L M) :
    LieModule.Cohomology.d₂₃ R L M
        (LieModule.Cohomology.d₁₂ R L M f) = 0 := by
  have h := LieModule.Cohomology.d₂₃_comp_d₁₂ R L M
  have hf := congrArg (fun T => T f) h
  simpa [LinearMap.comp_apply] using hf

variable {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]

structure System (A 𝔤 : Type*) [Ring A] where
  derivation : 𝔤 → NCDerivation A
  bracket : 𝔤 → 𝔤 → 𝔤
  bracket_action : ∀ D E a,
    derivation D (derivation E a) - derivation E (derivation D a) =
      derivation (bracket D E) a

/-! A system whose abstract index bracket is explicitly Lie-theoretic.

`System` is retained as the compatibility layer used by the older low-degree
coordinate API.  The present structure is the canonical boundary for generic
Chevalley--Eilenberg and Bianchi results: the additional fields prevent those
results from being stated for an arbitrary, unstructured binary operation.
-/
structure LieSystem (A 𝔤 : Type*) [Ring A] [AddCommGroup 𝔤]
    extends System A 𝔤 where
  derivation_zero : derivation 0 = 0
  derivation_add : ∀ D E, derivation (D + E) = derivation D + derivation E
  bracket_zero : ∀ D, bracket 0 D = 0
  bracket_add_left : ∀ D E F, bracket (D + E) F = bracket D F + bracket E F
  bracket_add_right : ∀ D E F, bracket D (E + F) = bracket D E + bracket D F
  bracket_neg_left : ∀ D E, bracket (-D) E = -bracket D E
  bracket_neg_right : ∀ D E, bracket D (-E) = -bracket D E
  bracket_skew : ∀ D E, bracket E D = -bracket D E
  bracket_jacobi : ∀ D E F,
    bracket D (bracket E F) + bracket E (bracket F D) +
        bracket F (bracket D E) = 0

namespace LieSystem

@[simp] theorem bracket_zero_apply (S : LieSystem A 𝔤) (D : 𝔤) :
    S.toSystem.bracket 0 D = 0 :=
  S.bracket_zero D

theorem bracket_add_left_apply (S : LieSystem A 𝔤) (D E F : 𝔤) :
    S.toSystem.bracket (D + E) F =
      S.toSystem.bracket D F + S.toSystem.bracket E F :=
  S.bracket_add_left D E F

theorem bracket_add_right_apply (S : LieSystem A 𝔤) (D E F : 𝔤) :
    S.toSystem.bracket D (E + F) =
      S.toSystem.bracket D E + S.toSystem.bracket D F :=
  S.bracket_add_right D E F

theorem bracket_skew_apply (S : LieSystem A 𝔤) (D E : 𝔤) :
    S.toSystem.bracket E D = -S.toSystem.bracket D E :=
  S.bracket_skew D E

theorem bracket_jacobi_apply (S : LieSystem A 𝔤) (D E F : 𝔤) :
    S.toSystem.bracket D (S.toSystem.bracket E F) +
        S.toSystem.bracket E (S.toSystem.bracket F D) +
        S.toSystem.bracket F (S.toSystem.bracket D E) = 0 :=
  S.bracket_jacobi D E F

end LieSystem

def IsDerivationBracketCompatible (S : System A 𝔤) : Prop :=
  ∀ D E, NCDerivation.commutator (S.derivation D) (S.derivation E) =
    S.derivation (S.bracket D E)

theorem system_bracket_action_iff_derivation_bracket_compatible
    (S : System A 𝔤) :
    (∀ D E a,
      S.derivation D (S.derivation E a) -
          S.derivation E (S.derivation D a) =
        S.derivation (S.bracket D E) a) ↔
      IsDerivationBracketCompatible S := by
  constructor
  · intro h D E
    apply NCDerivation.ext
    intro a
    simpa [IsDerivationBracketCompatible, NCDerivation.commutator_apply] using h D E a
  · intro h D E a
    have hDE := congrArg (fun T : NCDerivation A => T a) (h D E)
    simpa [IsDerivationBracketCompatible, NCDerivation.commutator_apply] using hDE

abbrev Form0 (A : Type*) := A
abbrev Form1 (𝔤 A : Type*) := 𝔤 → A
abbrev Form2 (𝔤 A : Type*) := 𝔤 → 𝔤 → A
abbrev Form3 (𝔤 A : Type*) := 𝔤 → 𝔤 → 𝔤 → A

/-! Native Mathlib carrier for derivation-valued forms. -/
abbrev NativeDerivationForm (R V M : Type*) [Semiring R]
    [AddCommMonoid V] [AddCommMonoid M] [Module R V] [Module R M]
    (n : ℕ) := V [⋀^Fin n]→ₗ[R] M

theorem nativeDerivationForm_vanishes_on_repeated_slot
    {R V M : Type*} [Semiring R]
    [AddCommMonoid V] [AddCommMonoid M] [Module R V] [Module R M]
    (n : ℕ) (ω : NativeDerivationForm R V M n) (v : Fin n → V)
    {i j : Fin n} (hij : i ≠ j) (h : v i = v j) :
    ω v = 0 := by
  exact ω.map_eq_zero_of_eq' v i j h hij

def multilinearMapToNativeDerivationForm
    {R V M : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (n : ℕ)
    (m : MultilinearMap R (fun _ : Fin n => V) M)
    (halt : ∀ (v : Fin n → V) (i j : Fin n),
      v i = v j → i ≠ j → m v = 0) :
    NativeDerivationForm R V M n :=
  { toMultilinearMap := m
    map_eq_zero_of_eq' := halt }

@[simp] theorem multilinearMapToNativeDerivationForm_apply
    {R V M : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (n : ℕ)
    (m : MultilinearMap R (fun _ : Fin n => V) M)
    (halt : ∀ (v : Fin n → V) (i j : Fin n),
      v i = v j → i ≠ j → m v = 0) (v : Fin n → V) :
    multilinearMapToNativeDerivationForm n m halt v = m v := by
  rfl

def linearMapToNativeDerivationForm
    {R V M : Type*} [CommSemiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (f : V →ₗ[R] M) :
    NativeDerivationForm R V M 1 := by
  let m : MultilinearMap R (fun _ : Fin 1 => V) M :=
    MultilinearMap.mk' (fun v => f (v 0))
      (by
        intro v i x y
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [Function.update] using f.map_add x y)
      (by
        intro v i c x
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [Function.update] using f.map_smul c x)
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        have : i = j := Fin.eq_zero i |>.trans (Fin.eq_zero j).symm
        exact (hij this).elim }

@[simp] theorem linearMapToNativeDerivationForm_apply
    {R V M : Type*} [CommSemiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (f : V →ₗ[R] M) (v : Fin 1 → V) :
    linearMapToNativeDerivationForm f v = f (v 0) := by
  rfl

/-
/-
def bilinearMapToNativeDerivationForm
    {R V M : Type*} [CommSemiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (f : V →ₗ[R] V →ₗ[R] M)
    (hdiag : ∀ v, f v v = 0) : NativeDerivationForm R V M 2 := by
  let m : MultilinearMap R (fun _ : Fin 2 => V) M :=
    MultilinearMap.mk' (fun v => f (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i <;> simp [Function.update])
      (by
        intro v i c x
        fin_cases i <;> simp [Function.update])
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change f (v 0) (v 1) = 0
          have h' : v 0 = v 1 := by simpa using h
          rw [← h']
          exact hdiag (v 0)
        · change f (v 0) (v 1) = 0
          have h' : v 1 = v 0 := by simpa using h
          rw [h']
          exact hdiag (v 0)
        · exact (hij rfl).elim }

 -/

def bilinearMapToNativeDerivationForm
    {R V M : Type*} [CommSemiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (f : V →ₗ[R] V →ₗ[R] M)
    (hdiag : ∀ v, f v v = 0) : NativeDerivationForm R V M 2 := by
  let m : MultilinearMap R (fun _ : Fin 2 => V) M :=
    MultilinearMap.mk' (fun v => f (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i
        · change f (x + y) (v 1) = f x (v 1) + f y (v 1)
          exact f.map_add x y
        · change f (v 0) (x + y) = f (v 0) x + f (v 0) y
          exact (f (v 0)).map_add x y)
      (by
        intro v i c x
        fin_cases i
        · change f (c • x) (v 1) = c • f x (v 1)
          exact f.map_smul c x
        · change f (v 0) (c • x) = c • f (v 0) x
          exact (f (v 0)).map_smul c x)
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change f (v 0) (v 1) = 0
          have h' : v 0 = v 1 := by simpa using h
          rw [← h']
          exact hdiag (v 0)
        · change f (v 0) (v 1) = 0
          have h' : v 1 = v 0 := by simpa using h
          rw [h']
          exact hdiag (v 0)
        · exact (hij rfl).elim }

 -/

def bilinearToNativeDerivationForm
    {R V M : Type*} [Semiring R] [AddCommMonoid V] [AddCommMonoid M]
    [Module R V] [Module R M] (f : V → V → M)
    (hadd₁ : ∀ x y z, f (x + y) z = f x z + f y z)
    (hadd₂ : ∀ x y z, f x (y + z) = f x y + f x z)
    (hsmul₁ : ∀ (c : R) x y, f (c • x) y = c • f x y)
    (hsmul₂ : ∀ (c : R) x y, f x (c • y) = c • f x y)
    (hdiag : ∀ x, f x x = 0) : NativeDerivationForm R V M 2 := by
  let m : MultilinearMap R (fun _ : Fin 2 => V) M :=
    MultilinearMap.mk' (fun v => f (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i
        · simpa [Function.update] using hadd₁ x y (v 1)
        · simpa [Function.update] using hadd₂ (v 0) x y)
      (by
        intro v i c x
        fin_cases i
        · simpa [Function.update] using hsmul₁ c x (v 1)
        · simpa [Function.update] using hsmul₂ c (v 0) x)
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · have h' : v 0 = v 1 := by simpa using h
          change f (v 0) (v 1) = 0
          rw [← h']
          exact hdiag (v 0)
        · have h' : v 1 = v 0 := by simpa using h
          change f (v 0) (v 1) = 0
          rw [h']
          exact hdiag (v 0)
        · exact (hij rfl).elim }

abbrev DerivationForm (𝔤 A : Type*) [AddCommGroup 𝔤] [AddCommGroup A]
    (n : ℕ) := 𝔤 [⋀^Fin n]→ₗ[ℤ] A

theorem derivationForm_vanishes_on_repeated_slot
    {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (n : ℕ) (ω : DerivationForm 𝔤 A n) (v : Fin n → 𝔤)
    {i j : Fin n} (hij : i ≠ j) (h : v i = v j) :
    ω v = 0 := by
  exact ω.map_eq_zero_of_eq' v i j h hij

/-! A linear one-form is kept separate from the general function-valued form. -/
abbrev LinearForm1 (𝔤 A : Type*) [AddCommGroup 𝔤] [AddCommGroup A] :=
  𝔤 →ₗ[ℤ] A
abbrev LinearForm2 (𝔤 A : Type*) [AddCommGroup 𝔤] [AddCommGroup A] :=
  𝔤 →ₗ[ℤ] 𝔤 →ₗ[ℤ] A

/-! Symmetric response tensors and exterior two-forms are distinct objects.
The first is a bilinear response; the second is a genuine alternating map. -/
def IsSymmetricLinearForm2 {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm2 𝔤 A) : Prop :=
  ∀ D E, η D E = η E D

def IsExteriorLinearForm2 {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm2 𝔤 A) : Prop :=
  (∀ D, η D D = 0) ∧ ∀ D E, η E D = -η D E
abbrev LinearForm3 (𝔤 A : Type*) [AddCommGroup 𝔤] [AddCommGroup A] :=
    𝔤 →ₗ[ℤ] 𝔤 →ₗ[ℤ] 𝔤 →ₗ[ℤ] A

/-! A linear derivation action is the native CE input for zero-forms.  The
Leibniz law is kept as a proposition rather than inferred from linearity. -/
structure LinearDerivationAction (A 𝔤 : Type*) [Ring A] [AddCommGroup 𝔤] where
  toLinearMap : 𝔤 →ₗ[ℤ] (A →ₗ[ℤ] A)
  leibniz : ∀ D a b,
    toLinearMap D (a * b) = toLinearMap D a * b + a * toLinearMap D b

/-! The structured Lie-system boundary feeds the native CE action through
underlying linear maps.  The bundled `NCDerivation` records themselves need
not carry an additive instance. -/
def LieSystem.toLinearDerivationAction
    (S : LieSystem A 𝔤) : LinearDerivationAction A 𝔤 where
  toLinearMap :=
    { toFun := fun D => (S.derivation D).toLinearMap
      map_add' := by
        intro D E
        exact congrArg NCDerivation.toLinearMap (S.derivation_add D E)
      map_smul' := by
        intro n D
        let ρ : 𝔤 →+ (A →ₗ[ℤ] A) :=
          { toFun := fun X => (S.derivation X).toLinearMap
            map_zero' := congrArg NCDerivation.toLinearMap S.derivation_zero
            map_add' := fun X Y =>
              congrArg NCDerivation.toLinearMap (S.derivation_add X Y) }
        exact ρ.map_zsmul D n }
  leibniz := by
    intro D a b
    exact (S.derivation D).leibniz a b

theorem LieSystem.toLinearDerivationAction_bracket_action
    (S : LieSystem A 𝔤) (D E : 𝔤) (a : A) :
    S.toLinearDerivationAction.toLinearMap D
          (S.toLinearDerivationAction.toLinearMap E a) -
        S.toLinearDerivationAction.toLinearMap E
          (S.toLinearDerivationAction.toLinearMap D a) =
      S.toLinearDerivationAction.toLinearMap
        (S.toSystem.bracket D E) a := by
  exact S.toSystem.bracket_action D E a

def LinearDerivationAction.toNCDerivation {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (ρ : LinearDerivationAction A 𝔤) (D : 𝔤) : NCDerivation A :=
  { toLinearMap := ρ.toLinearMap D
    leibniz' := ρ.leibniz D }

def LinearDerivationAction.toSystem {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (ρ : LinearDerivationAction A 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (hcompat : ∀ D E a,
      ρ.toNCDerivation D (ρ.toNCDerivation E a) -
          ρ.toNCDerivation E (ρ.toNCDerivation D a) =
        ρ.toNCDerivation (bracket D E) a) : System A 𝔤 :=
  { derivation := ρ.toNCDerivation
    bracket := bracket
    bracket_action := hcompat }

/-
/-! Native CE data: the bracket is linear in both parameters and alternating on
the diagonal.  This refinement is separate from `System` for compatibility. -/
structure LinearCESystem (A 𝔤 : Type*) [Ring A] [AddCommGroup 𝔤] where
  action : LinearDerivationAction A 𝔤
  bracket : 𝔤 →ₗ[ℤ] 𝔤 →ₗ[ℤ] 𝔤
  bracket_self : ∀ D, bracket D D = 0

def LinearCESystem.differential1 {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (S : LinearCESystem A 𝔤) (ω : LinearForm1 𝔤 A) : LinearForm2 𝔤 A :=
  { toFun := fun D =>
      { toFun := fun E =>
          S.action.toLinearMap D (ω E) -
            S.action.toLinearMap E (ω D) - ω (S.bracket D E)
        map_add' := by
          intro E F
          change S.action.toLinearMap D (ω (E + F)) -
              S.action.toLinearMap (E + F) (ω D) - ω (S.bracket D (E + F)) = _
          simp only [ω.map_add, S.action.toLinearMap.map_add,
            (S.bracket D).map_add, LinearMap.add_apply,
            (S.action.toLinearMap D).map_add]
          try simp only [smul_add, add_smul, neg_smul]
          abel_nf
        map_smul' := by
          intro c E
          change S.action.toLinearMap D (ω (c • E)) -
              S.action.toLinearMap (c • E) (ω D) - ω (S.bracket D (c • E)) = _
          simp only [ω.map_smul, S.action.toLinearMap.map_smul,
            (S.bracket D).map_smul, LinearMap.smul_apply,
            (S.action.toLinearMap D).map_smul]
          try simp only [smul_add, add_smul, neg_smul]
          abel_nf }
    map_add' := by
      intro D E
      apply LinearMap.ext
      intro F
      change S.action.toLinearMap (D + E) (ω F) -
          S.action.toLinearMap F (ω (D + E)) - ω (S.bracket (D + E) F) = _
      simp only [S.action.toLinearMap.map_add, ω.map_add,
        S.bracket.map_add, LinearMap.add_apply,
        (S.action.toLinearMap F).map_add]
      try simp only [smul_add, add_smul, neg_smul]
      abel_nf
    map_smul' := by
      intro c D
      apply LinearMap.ext
      intro E
      change S.action.toLinearMap (c • D) (ω E) -
          S.action.toLinearMap E (ω (c • D)) - ω (S.bracket (c • D) E) = _
      simp only [S.action.toLinearMap.map_smul, ω.map_smul,
        S.bracket.map_smul, LinearMap.smul_apply,
        (S.action.toLinearMap E).map_smul]
      try simp only [smul_add, add_smul, neg_smul]
      abel_nf }

theorem LinearCESystem.differential1_self (S : LinearCESystem A 𝔤)
    (ω : LinearForm1 𝔤 A) (D : 𝔤) :
    S.differential1 ω D D = 0 := by
  simp [LinearCESystem.differential1, S.bracket_self D]

 -/

def differential0Native {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (ρ : LinearDerivationAction A 𝔤) (a : A) : LinearForm1 𝔤 A :=
  { toFun := fun D => ρ.toLinearMap D a
    map_add' := by
      intro D E
      rw [ρ.toLinearMap.map_add]
      rfl
    map_smul' := by
      intro c D
      rw [ρ.toLinearMap.map_smul]
      rfl }

theorem differential0Native_mul {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (ρ : LinearDerivationAction A 𝔤) (a b : A) (D : 𝔤) :
    differential0Native ρ (a * b) D =
      differential0Native ρ a D * b + a * differential0Native ρ b D := by
  exact ρ.leibniz D a b

def linearFormToDerivationForm {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (ω : LinearForm1 𝔤 A) : DerivationForm 𝔤 A 1 := by
  let m : MultilinearMap ℤ (fun _ : Fin 1 => 𝔤) A :=
    MultilinearMap.mk' (fun v => ω (v 0))
      (by
        intro v i x y
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [Function.update] using ω.map_add _ _)
      (by
        intro v i c x
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simpa [Function.update] using ω.map_smul c _)
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        have : i = j := Fin.eq_zero i |>.trans (Fin.eq_zero j).symm
        exact (hij this).elim }

def bilinearFormToDerivationForm {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm2 𝔤 A) (hdiag : ∀ D, η D D = 0) : DerivationForm 𝔤 A 2 := by
  let m : MultilinearMap ℤ (fun _ : Fin 2 => 𝔤) A :=
    MultilinearMap.mk' (fun v => η (v 0) (v 1))
      (by
        intro v i x y
        fin_cases i <;> simp [Function.update])
      (by
        intro v i c x
        fin_cases i <;> simp [Function.update])
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change η (v 0) (v 1) = 0
          have h01 : v 0 = v 1 := by simpa using h
          rw [← h01]
          exact hdiag (v 0)
        · change η (v 0) (v 1) = 0
          have h10 : v 1 = v 0 := by simpa using h
          rw [h10]
          exact hdiag (v 0)
        · exact (hij rfl).elim }

def exteriorLinearForm2ToDerivationForm
    {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm2 𝔤 A) (hη : IsExteriorLinearForm2 η) :
    DerivationForm 𝔤 A 2 :=
  bilinearFormToDerivationForm η hη.1

@[simp] theorem linearFormToDerivationForm_apply
    {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (ω : LinearForm1 𝔤 A) (D : 𝔤) :
    linearFormToDerivationForm ω (fun _ : Fin 1 => D) = ω D := by
  rfl

@[simp] theorem bilinearFormToDerivationForm_apply
    {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm2 𝔤 A) (hdiag : ∀ D, η D D = 0)
    (v : Fin 2 → 𝔤) :
    bilinearFormToDerivationForm η hdiag v = η (v 0) (v 1) := by
  rfl

def linearForm3.toDerivationForm {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm3 𝔤 A)
    (h01 : ∀ D E, η D D E = 0)
    (h02 : ∀ D E, η D E D = 0)
    (h12 : ∀ D E, η D E E = 0) : DerivationForm 𝔤 A 3 := by
  let m : MultilinearMap ℤ (fun _ : Fin 3 => 𝔤) A :=
    MultilinearMap.mk' (fun v => η (v 0) (v 1) (v 2))
      (by
        intro v i x y
        fin_cases i <;> simp [Function.update])
      (by
        intro v i c x
        fin_cases i <;> simp [Function.update])
  exact
    { toMultilinearMap := m
      map_eq_zero_of_eq' := by
        intro v i j h hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 0 = v 1 := by simpa using h
          rw [← h']
          exact h01 (v 0) (v 2)
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 0 = v 2 := by simpa using h
          rw [← h']
          exact h02 (v 0) (v 1)
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 1 = v 0 := by simpa using h
          rw [h']
          exact h01 (v 0) (v 2)
        · exact (hij rfl).elim
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 1 = v 2 := by simpa using h
          rw [← h']
          exact h12 (v 0) (v 1)
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 2 = v 0 := by simpa using h
          rw [h']
          exact h02 (v 0) (v 1)
        · change η (v 0) (v 1) (v 2) = 0
          have h' : v 2 = v 1 := by simpa using h
          rw [h']
          exact h12 (v 0) (v 1)
        · exact (hij rfl).elim }

@[simp] theorem linearForm3.toDerivationForm_apply
    {𝔤 A : Type*} [AddCommGroup 𝔤] [AddCommGroup A]
    (η : LinearForm3 𝔤 A)
    (h01 : ∀ D E, η D D E = 0)
    (h02 : ∀ D E, η D E D = 0)
    (h12 : ∀ D E, η D E E = 0) (v : Fin 3 → 𝔤) :
    linearForm3.toDerivationForm η h01 h02 h12 v = η (v 0) (v 1) (v 2) := by
  rfl

theorem linearForm3_apply_add_left (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η (D + E) F G = η D F G + η E F G := by
  exact congrArg (fun L => L F G) (η.map_add D E)

theorem linearForm3_apply_sub_left (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η (D - E) F G = η D F G - η E F G := by
  exact congrArg (fun L => L F G) (η.map_sub D E)

theorem linearForm3_apply_neg_left (η : LinearForm3 𝔤 A) (D E F : 𝔤) :
    η (-D) E F = -η D E F := by
  exact congrArg (fun L => L E F) (η.map_neg D)

theorem linearForm3_apply_add_middle (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η D (E + F) G = η D E G + η D F G := by
  exact congrArg (fun L => L G) ((η D).map_add E F)

theorem linearForm3_apply_sub_middle (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η D (E - F) G = η D E G - η D F G := by
  exact congrArg (fun L => L G) ((η D).map_sub E F)

theorem linearForm3_apply_neg_middle (η : LinearForm3 𝔤 A) (D E F : 𝔤) :
    η D (-E) F = -η D E F := by
  exact congrArg (fun L => L F) ((η D).map_neg E)

theorem linearForm3_apply_add_right (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η D E (F + G) = η D E F + η D E G := by
  exact (η D E).map_add F G

theorem linearForm3_apply_sub_right (η : LinearForm3 𝔤 A) (D E F G : 𝔤) :
    η D E (F - G) = η D E F - η D E G := by
  exact (η D E).map_sub F G

theorem linearForm3_apply_neg_right (η : LinearForm3 𝔤 A) (D E F : 𝔤) :
    η D E (-F) = -η D E F := by
  exact (η D E).map_neg F

theorem linearForm2_apply_add_left (η : LinearForm2 𝔤 A) (D E F : 𝔤) :
    η (D + E) F = η D F + η E F := by
  exact congrArg (fun L => L F) (η.map_add D E)

theorem linearForm2_apply_sub_left (η : LinearForm2 𝔤 A) (D E F : 𝔤) :
    η (D - E) F = η D F - η E F := by
  exact congrArg (fun L => L F) (η.map_sub D E)

theorem linearForm2_apply_neg_left (η : LinearForm2 𝔤 A) (D E : 𝔤) :
    η (-D) E = -η D E := by
  exact congrArg (fun L => L E) (η.map_neg D)

theorem linearForm2_apply_add_right (η : LinearForm2 𝔤 A) (D E F : 𝔤) :
    η D (E + F) = η D E + η D F := by
  exact (η D).map_add E F

theorem linearForm2_apply_sub_right (η : LinearForm2 𝔤 A) (D E F : 𝔤) :
    η D (E - F) = η D E - η D F := by
  exact (η D).map_sub E F

theorem linearForm2_apply_neg_right (η : LinearForm2 𝔤 A) (D E : 𝔤) :
    η D (-E) = -η D E := by
  exact (η D).map_neg E

def IsAlternating2 (ω : Form2 𝔤 A) : Prop :=
  ∀ D E, ω E D = -ω D E

def IsAlternating3 (ω : Form3 𝔤 A) : Prop :=
  ∀ D E F, ω E D F = -ω D E F ∧ ω D F E = -ω D E F

def innerDerivation (K : A) : NCDerivation A where
  toLinearMap := InfoGeometry.NCG.adLie ℤ K
  leibniz' := by
    intro x y
    exact InfoGeometry.NCG.adLie_leibniz K x y

@[simp] theorem innerDerivation_apply (K X : A) :
    innerDerivation K X = K * X - X * K := rfl

def innerSystem : System A A where
  derivation := innerDerivation
  bracket := InfoGeometry.NCG.bracket
  bracket_action := by
    intro D E a
    exact InfoGeometry.NCG.adLie_commutator D E a

/-! The associative commutator action satisfies the full Lie-system contract.
This is the canonical concrete instance used when the coefficient algebra is
itself the index algebra. -/
def innerLieSystem : LieSystem A A where
  toSystem := innerSystem
  derivation_zero := by
    apply NCDerivation.ext
    intro a
    change (0 * a - a * 0) = 0
    simp
  derivation_add := by
    intro D E
    apply NCDerivation.ext
    intro a
    change ( (D + E) * a - a * (D + E)) =
      (D * a - a * D) + (E * a - a * E)
    noncomm_ring
  bracket_zero := by
    intro D
    simp [innerSystem, InfoGeometry.NCG.bracket]
  bracket_add_left := by
    intro D E F
    exact InfoGeometry.NCG.bracket_add_left D E F
  bracket_add_right := by
    intro D E F
    exact InfoGeometry.NCG.bracket_add_right D E F
  bracket_neg_left := by
    intro D E
    simp only [innerSystem, InfoGeometry.NCG.bracket]
    noncomm_ring
  bracket_neg_right := by
    intro D E
    simp only [innerSystem, InfoGeometry.NCG.bracket]
    noncomm_ring
  bracket_skew := by
    intro D E
    exact InfoGeometry.NCG.bracket_skew E D
  bracket_jacobi := by
    intro D E F
    exact InfoGeometry.NCG.bracket_jacobi D E F

@[simp] theorem innerLieSystem_toSystem :
    (innerLieSystem (A := A)).toSystem = innerSystem :=
  rfl

theorem innerSystem_derivation_bracket_compatible :
    IsDerivationBracketCompatible (innerSystem (A := A)) := by
  intro D E
  apply NCDerivation.ext
  intro a
  exact InfoGeometry.NCG.adLie_commutator D E a

theorem innerSystem_bracket_skew (D E : A) :
    innerSystem.bracket E D = -innerSystem.bracket D E := by
  exact InfoGeometry.NCG.bracket_skew E D

theorem innerSystem_bracket_jacobi (D E F : A) :
    innerSystem.bracket D (innerSystem.bracket E F) +
        innerSystem.bracket E (innerSystem.bracket F D) +
        innerSystem.bracket F (innerSystem.bracket D E) = 0 := by
  exact InfoGeometry.NCG.bracket_jacobi D E F

theorem linearForm_apply_neg_one_smul (Γ : A →ₗ[ℤ] A) (x : A) :
    Γ ((-1 : A) • x) = -Γ x := by
  rw [neg_one_smul]
  exact Γ.map_neg x

theorem linearForm_apply_sub (Γ : A →ₗ[ℤ] A) (x y : A) :
    Γ (x - y) = Γ x - Γ y := by
  exact Γ.map_sub x y

def differential0 (S : System A 𝔤) (a : Form0 A) : Form1 𝔤 A :=
  fun D => S.derivation D a

theorem differential0Native_eq_differential0
    {A 𝔤 : Type*} [Ring A] [AddCommGroup 𝔤]
    (ρ : LinearDerivationAction A 𝔤) (bracket : 𝔤 → 𝔤 → 𝔤)
    (hcompat : ∀ D E a,
      ρ.toNCDerivation D (ρ.toNCDerivation E a) -
          ρ.toNCDerivation E (ρ.toNCDerivation D a) =
        ρ.toNCDerivation (bracket D E) a) (a : A) (D : 𝔤) :
    differential0 (ρ.toSystem bracket hcompat) a D = differential0Native ρ a D := by
  rfl

theorem differential0_mul (S : System A 𝔤) (a b : A) (D : 𝔤) :
    differential0 S (a * b) D =
      differential0 S a D * b + a * differential0 S b D := by
  exact (S.derivation D).leibniz a b

def differential1 (S : System A 𝔤) (ω : Form1 𝔤 A) : Form2 𝔤 A :=
  fun D E => S.derivation D (ω E) - S.derivation E (ω D) - ω (S.bracket D E)

def differential1Linear {𝔤 A : Type*} [Ring A] [AddCommGroup 𝔤]
    (S : System A 𝔤) (ω : LinearForm1 𝔤 A) : Form2 𝔤 A :=
  differential1 S ω

theorem differential1_isAlternating2 (S : System A 𝔤) (ω : Form1 𝔤 A)
    (hω : ∀ D, ω (-D) = -ω D)
    (hbracket : ∀ D E, S.bracket E D = -S.bracket D E) :
    IsAlternating2 (differential1 S ω) := by
  intro D E
  unfold differential1
  have hw : ω (-(S.bracket D E)) = -ω (S.bracket D E) :=
    hω (S.bracket D E)
  rw [hbracket D E, hw]
  abel

theorem innerSystem_differential1_isAlternating2 (ω : A →ₗ[ℤ] A) :
    IsAlternating2 (differential1 innerSystem ω) := by
  apply differential1_isAlternating2
  · intro D
    exact ω.map_neg D
  · intro D E
    exact InfoGeometry.NCG.bracket_skew E D

theorem differential1Linear_isAlternating2 {𝔤 A : Type*} [Ring A]
    [AddCommGroup 𝔤] (S : System A 𝔤) (ω : LinearForm1 𝔤 A)
    (hbracket : ∀ D E, S.bracket E D = -S.bracket D E) :
    IsAlternating2 (differential1Linear S ω) := by
  apply differential1_isAlternating2 S ω
  · intro D
    exact ω.map_neg D
  · exact hbracket

theorem differential1_differential0 (S : System A 𝔤) (a : A) (D E : 𝔤) :
    differential1 S (differential0 S a) D E = 0 := by
  unfold differential1 differential0
  rw [S.bracket_action]
  abel

def differential2 (S : System A 𝔤) (η : Form2 𝔤 A) : Form3 𝔤 A :=
  fun D E F =>
    S.derivation D (η E F) - S.derivation E (η D F) + S.derivation F (η D E) -
      η (S.bracket D E) F + η (S.bracket D F) E - η (S.bracket E F) D

def differential2Linear {𝔤 A : Type*} [Ring A] [AddCommGroup 𝔤]
    (S : System A 𝔤) (η : LinearForm2 𝔤 A) : Form3 𝔤 A :=
  differential2 S (fun D E => η D E)

theorem nativeCE_inner_differential2
    {A : Type*} [Ring A]
    (η : LieModule.Cohomology.twoCochain ℤ A A) (D E F : A) :
    LieModule.Cohomology.d₂₃ ℤ A A η D E F =
      differential2 innerSystem (fun X Y => η X Y) D E F := by
  rfl

def curvature (S : System A 𝔤) (Γ : Form1 𝔤 A) : Form2 𝔤 A :=
  fun D E => differential1 S Γ D E + (Γ D * Γ E - Γ E * Γ D)

theorem curvature_isAlternating2 (S : System A 𝔤) (Γ : Form1 𝔤 A)
    (hΓ : ∀ D, Γ (-D) = -Γ D)
    (hbracket : ∀ D E, S.bracket E D = -S.bracket D E) :
    IsAlternating2 (curvature S Γ) := by
  intro D E
  unfold curvature
  rw [differential1_isAlternating2 S Γ hΓ hbracket D E]
  noncomm_ring

theorem innerSystem_curvature_isAlternating2 (Γ : A →ₗ[ℤ] A) :
    IsAlternating2 (curvature innerSystem Γ) := by
  apply curvature_isAlternating2
  · intro D
    exact Γ.map_neg D
  · intro D E
    exact InfoGeometry.NCG.bracket_skew E D

theorem nativeCE_inner_differential1
    {A : Type*} [Ring A] (ω : A →ₗ[ℤ] A) (D E : A) :
    LieModule.Cohomology.d₁₂ ℤ A A ω D E =
      differential1 innerSystem ω D E := by
  rfl

theorem innerSystem_differential2_differential1
    {A : Type*} [Ring A] (ω : A →ₗ[ℤ] A) (D E F : A) :
    differential2 innerSystem (fun X Y => differential1 innerSystem ω X Y)
        D E F = 0 := by
  have h := nativeCE_d2_d1_zero ℤ A A ω
  have h' := congrArg (fun η => η D E F) h
  have hω :
      (fun X Y => (LieModule.Cohomology.d₁₂ ℤ A A ω X) Y) =
        (fun X Y => differential1 innerSystem ω X Y) := by
    funext X Y
    exact nativeCE_inner_differential1 ω X Y
  rw [← hω]
  rw [← nativeCE_inner_differential2
    (LieModule.Cohomology.d₁₂ ℤ A A ω) D E F]
  exact h'

def covariant (S : System A 𝔤) (Γ : Form1 𝔤 A) (D : 𝔤) (a : A) : A :=
  S.derivation D a + Γ D * a - a * Γ D

def covariantDifferential2 (S : System A 𝔤) (Γ : Form1 𝔤 A)
    (η : Form2 𝔤 A) : Form3 𝔤 A :=
  fun D E F =>
    differential2 S η D E F +
      (Γ D * η E F - η E F * Γ D) -
      (Γ E * η D F - η D F * Γ E) +
      (Γ F * η D E - η D E * Γ F)

theorem covariant_leibniz (S : System A 𝔤) (Γ : Form1 𝔤 A) (D : 𝔤) (a b : A) :
    covariant S Γ D (a * b) =
      covariant S Γ D a * b + a * covariant S Γ D b := by
  unfold covariant
  simp only [NCDerivation.leibniz]
  noncomm_ring

@[simp] theorem covariant_one (S : System A 𝔤) (Γ : Form1 𝔤 A) (D : 𝔤) :
    covariant S Γ D 1 = 0 := by
  unfold covariant
  simp

theorem covariant_commutator_sub_bracket (S : System A 𝔤) (Γ : Form1 𝔤 A)
    (a : A) (D E : 𝔤) :
    covariant S Γ D (covariant S Γ E a) -
        covariant S Γ E (covariant S Γ D a) -
        covariant S Γ (S.bracket D E) a =
      curvature S Γ D E * a - a * curvature S Γ D E := by
  unfold covariant curvature differential1
  simp only [NCDerivation.map_add, NCDerivation.map_sub,
    NCDerivation.leibniz]
  have h := S.bracket_action D E a
  have h' : S.derivation D (S.derivation E a) =
      S.derivation E (S.derivation D a) + S.derivation (S.bracket D E) a := by
    simpa [sub_eq_iff_eq_add, add_comm] using h
  rw [h']
  noncomm_ring

theorem curvature_apply (S : System A 𝔤) (Γ : Form1 𝔤 A) (D E : 𝔤) :
    curvature S Γ D E =
      S.derivation D (Γ E) - S.derivation E (Γ D) - Γ (S.bracket D E) +
        (Γ D * Γ E - Γ E * Γ D) := by
  rfl

end InfoGeometry.NCG.DerivationDifferential
