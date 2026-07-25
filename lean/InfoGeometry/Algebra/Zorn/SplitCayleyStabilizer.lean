import InfoGeometry.Algebra.Zorn.ConcreteComposition

/-!
# Native split-Cayley automorphism/stabilizer model

`splitCayleyStabilizer R` is the concrete multiplication-stabilizer subgroup of
linear equivalences of the eight-coordinate Zorn cell.  It is deliberately not
identified here with a split Chevalley group of type `G₂`; that classification
is a separate theorem.
-/

namespace InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer

open InfoGeometry.Algebra.Zorn.ConcreteComposition

variable {R : Type*} [CommRing R]

namespace ZornCell

/-- The eight Zorn coordinates as a finite free `Fin 8` coordinate vector. -/
def coordEquiv : ZornCell R ≃ (Fin 8 → R) where
  toFun X := ![X.r, X.s, X.x1, X.x2, X.x3, X.y1, X.y2, X.y3]
  invFun v :=
    { r := v 0, s := v 1, x1 := v 2, x2 := v 3, x3 := v 4,
      y1 := v 5, y2 := v 6, y3 := v 7 }
  left_inv X := by
    rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
    rfl
  right_inv v := by
    funext i
    fin_cases i <;> rfl

instance : AddCommGroup (ZornCell R) :=
  Equiv.addCommGroup (coordEquiv (R := R))

instance : Module R (ZornCell R) :=
  Equiv.module R (coordEquiv (R := R))

end ZornCell

/-- The multiplicative identity in the Zorn cell model. -/
def zornOne : ZornCell R :=
  { r := 1, s := 1, x1 := 0, x2 := 0, x3 := 0,
    y1 := 0, y2 := 0, y3 := 0 }

@[simp] theorem zornOne_mul (X : ZornCell R) :
    zornOne (R := R) * X = X := by
  change ZornCell.mulZ (zornOne (R := R)) X = X
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold zornOne ZornCell.mulZ
  ring_nf

@[simp] theorem mul_zornOne (X : ZornCell R) :
    X * zornOne (R := R) = X := by
  change ZornCell.mulZ X (zornOne (R := R)) = X
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold zornOne ZornCell.mulZ
  ring_nf

@[simp] theorem detZ_zornOne :
    ZornCell.detZ (zornOne (R := R)) = 1 := by
  unfold zornOne ZornCell.detZ
  ring

/-- A linear equivalence preserving the Zorn unit and multiplication. -/
def IsSplitCayleyAut (e : ZornCell R ≃ₗ[R] ZornCell R) : Prop :=
  e (zornOne (R := R)) = zornOne (R := R) ∧
    ∀ X Y : ZornCell R, e (X * Y) = e X * e Y

/-- Concrete multiplication-stabilizer subgroup of the finite free Zorn model. -/
def splitCayleyStabilizer : Subgroup (ZornCell R ≃ₗ[R] ZornCell R) where
  carrier := {e | IsSplitCayleyAut e}
  one_mem' := by
    constructor
    · rfl
    · intro X Y
      rfl
  mul_mem' := by
    intro e f he hf
    constructor
    · rw [LinearEquiv.mul_apply, hf.1, he.1]
    · intro X Y
      simp only [LinearEquiv.mul_apply]
      rw [hf.2, he.2]
  inv_mem' := by
    intro e he
    constructor
    · apply e.injective
      simp [he.1]
    · intro X Y
      apply e.injective
      simpa using (he.2 (e.symm X) (e.symm Y)).symm

/-- The native automorphism group of the concrete split-Cayley model. -/
abbrev SplitCayleyAut := splitCayleyStabilizer (R := R)

/-- Every split-Cayley automorphism fixes the scalar line pointwise. -/
theorem map_scalar_zornOne (e : SplitCayleyAut (R := R)) (r : R) :
    e.1 (r • zornOne (R := R)) = r • zornOne (R := R) := by
  rw [map_smul, e.property.1]

/-- In particular, every split-Cayley automorphism fixes zero. -/
@[simp] theorem map_zero_zornCell (e : SplitCayleyAut (R := R)) :
    e.1 (0 : ZornCell R) = 0 := by
  exact map_zero e.1

/-- The automorphism and stabilizer surfaces coincide by construction. -/
def autEquivStabilizer :
    SplitCayleyAut (R := R) ≃* splitCayleyStabilizer (R := R) :=
  MulEquiv.refl _

@[simp] theorem autEquivStabilizer_apply
    (e : SplitCayleyAut (R := R)) : autEquivStabilizer e = e := rfl

end InfoGeometry.Algebra.Zorn.SplitCayleyStabilizer
