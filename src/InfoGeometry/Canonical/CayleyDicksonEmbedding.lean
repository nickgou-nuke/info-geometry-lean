import InfoGeometry.Canonical.AlbertCayleyDickson
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.AlbertCayleyDickson

open AlbertStep

variable {F A : Type*} [CommRing F] [Ring A] [Algebra F A] [Module F A]
  [SMulCommClass F A A] [IsScalarTower F A A] [StarRing A]

/-- Addition for AlbertStep -/
instance {γ : F} : Add (AlbertStep F A γ) where
  add x y := ⟨x.p + y.p, x.q + y.q⟩

/-- Negation for AlbertStep -/
instance {γ : F} : Neg (AlbertStep F A γ) where
  neg x := ⟨-x.p, -x.q⟩

/-- Scalar multiplication for AlbertStep -/
instance {γ : F} : SMul F (AlbertStep F A γ) where
  smul c x := ⟨c • x.p, c • x.q⟩

@[simp] theorem add_p {γ : F} (x y : AlbertStep F A γ) : (x + y).p = x.p + y.p := rfl
@[simp] theorem add_q {γ : F} (x y : AlbertStep F A γ) : (x + y).q = x.q + y.q := rfl
@[simp] theorem neg_p {γ : F} (x : AlbertStep F A γ) : (-x).p = -x.p := rfl
@[simp] theorem neg_q {γ : F} (x : AlbertStep F A γ) : (-x).q = -x.q := rfl
@[simp] theorem smul_p {γ : F} (c : F) (x : AlbertStep F A γ) : (c • x).p = c • x.p := rfl
@[simp] theorem smul_q {γ : F} (c : F) (x : AlbertStep F A γ) : (c • x).q = c • x.q := rfl

/-- The canonical algebraic inclusion of one Cayley-Dickson stage into the next. -/
def cdEmbed {γ : F} (x : A) : AlbertStep F A γ := ⟨x, 0⟩

theorem cdEmbed_zero {γ : F} : cdEmbed (0 : A) = (0 : AlbertStep F A γ) := rfl

theorem cdEmbed_one {γ : F} : cdEmbed (1 : A) = (1 : AlbertStep F A γ) := rfl

theorem cdEmbed_add {γ : F} (x y : A) :
    cdEmbed (γ := γ) (x + y) = cdEmbed x + cdEmbed y := by
  ext <;> simp [cdEmbed]

theorem cdEmbed_neg {γ : F} (x : A) :
    cdEmbed (γ := γ) (-x) = -cdEmbed x := by
  ext <;> simp [cdEmbed]

theorem cdEmbed_smul {γ : F} (c : F) (x : A) :
    cdEmbed (γ := γ) (c • x) = c • cdEmbed x := by
  ext
  · rfl
  · change (0 : A) = c • (0 : A)
    rw [Algebra.smul_def, mul_zero]

theorem cdEmbed_conj {γ : F} (x : A) :
    cdEmbed (γ := γ) (star x) = conj (γ := γ) (cdEmbed x) := by
  simp [cdEmbed, conj]

theorem cdEmbed_mul {γ : F} (x y : A) :
    cdEmbed (γ := γ) (x * y) =
      mul (γ := γ) (cdEmbed x) (cdEmbed y) := by
  ext
  · change x * y = x * y + γ • (star (0 : A) * 0)
    simp [Algebra.smul_def]
  · change (0 : A) = 0 * x + 0 * star y
    simp

theorem cdEmbed_injective {γ : F} :
    Function.Injective (cdEmbed (F := F) (A := A) (γ := γ)) := by
  intro x y h
  exact congrArg AlbertStep.p h

/-- The temporal insertion (delay-like) map. -/
def cdDelay {γ : F} (x : A) : AlbertStep F A γ := ⟨0, x⟩

theorem cdDelay_add {γ : F} (x y : A) :
    cdDelay (γ := γ) (x + y) = cdDelay x + cdDelay y := by
  ext <;> simp [cdDelay]

theorem cdDelay_conj {γ : F} (x : A) :
    conj (F := F) (A := A) (γ := γ) (cdDelay (γ := γ) x) =
      -cdDelay (γ := γ) x := by
  ext <;> simp [cdDelay, conj]

theorem cdDelay_mul_formula {γ : F} (x y : A) :
    mul (F := F) (A := A) (γ := γ) (cdDelay (γ := γ) x) (cdDelay (γ := γ) y) =
      cdEmbed (γ := γ) (γ • (star y * x)) := by
  ext
  · simp [cdDelay, cdEmbed, mul]
  · simp [cdDelay, cdEmbed, mul]

theorem cdDelay_not_mul_in_general [Nontrivial A] :
    mul (F := F) (A := A) (γ := (1 : F)) (cdDelay (γ := (1 : F)) (1 : A))
        (cdDelay (γ := (1 : F)) (1 : A)) ≠
      cdDelay (γ := (1 : F)) ((1 : A) * 1) := by
  intro h
  have h1 : mul (F := F) (A := A) (γ := (1 : F))
      (cdDelay (γ := (1 : F)) (1 : A))
      (cdDelay (γ := (1 : F)) (1 : A)) = cdEmbed (γ := (1 : F)) (1 : A) := by
    rw [cdDelay_mul_formula (F := F) (A := A) (γ := (1 : F))]
    simp [Algebra.smul_def]
  rw [h1] at h
  have h2 : (cdEmbed (γ := (1 : F)) (1 : A)).p = (cdDelay (γ := (1 : F)) ((1 : A) * 1)).p := congrArg AlbertStep.p h
  rw [mul_one] at h2
  change (1 : A) = 0 at h2
  exact (one_ne_zero : (1 : A) ≠ 0) h2

end InfoGeometry.Canonical.AlbertCayleyDickson
