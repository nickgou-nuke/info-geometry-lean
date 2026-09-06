import Mathlib

/-!
# Algebraic modular flows realized by unitary conjugation

This owner records only the algebraic input needed for a modular-flow
isometry.  No exponential, analytic continuation, or diagonalization is
introduced: the represented flow is required to be conjugation by an element
with both unitary identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.ModularFlowIsometry

variable {A B : Type*}
variable [Semiring A] [Algebra ℂ A] [StarRing A]
variable [NormedRing B] [NormOneClass B] [NormedAlgebra ℂ B] [StarRing B]
variable [CStarRing B]

structure Data where
  representation : A →⋆ₐ[ℂ] B
  flow : A →⋆ₐ[ℂ] A
  implementer : B
  implementer_left : star implementer * implementer = 1
  implementer_right : implementer * star implementer = 1
  intertwines : ∀ a, representation (flow a) =
    implementer * representation a * star implementer

/-- The concrete algebra homomorphism implemented by the supplied
unitary-like element. -/
def unitaryConjugationAlgHom (d : Data (A := A) (B := B)) : B →ₐ[ℂ] B := by
  refine AlgHom.mk ?_ ?_
  refine RingHom.mk ?_ ?_ ?_
  · refine MonoidHom.mk ?_ ?_
    · exact
        { toFun := fun x => d.implementer * x * star d.implementer
          map_one' := by
            simp only [mul_one, d.implementer_right] }
    · intro x y
      change d.implementer * (x * y) * star d.implementer =
        (d.implementer * x * star d.implementer) *
          (d.implementer * y * star d.implementer)
      calc
        d.implementer * (x * y) * star d.implementer =
            d.implementer * x * (y * star d.implementer) := by
              simp only [mul_assoc]
        _ = d.implementer * x *
            ((star d.implementer * d.implementer) *
              (y * star d.implementer)) := by
              rw [d.implementer_left, one_mul]
        _ = (d.implementer * x * star d.implementer) *
            (d.implementer * y * star d.implementer) := by
              simp only [mul_assoc]
  · simp
  · intro x y
    simp only [mul_add, add_mul]
  · intro c
    calc
      d.implementer * (algebraMap ℂ B) c * star d.implementer =
          (algebraMap ℂ B) c * d.implementer * star d.implementer := by
            rw [Algebra.commutes]
      _ = (algebraMap ℂ B) c := by
        simp only [mul_assoc, d.implementer_right, mul_one]

/-- The concrete star-algebra homomorphism implemented by conjugation. -/
def unitaryConjugationStarAlgHom (d : Data (A := A) (B := B)) :
    B →⋆ₐ[ℂ] B where
  toAlgHom := unitaryConjugationAlgHom d
  map_star' x := by
    simp only [unitaryConjugationAlgHom, star_mul, star_star]
    rw [mul_assoc]

omit [NormOneClass B] [CStarRing B] in
private theorem data_unitaryConjugation_left_inverse
    (d : Data (A := A) (B := B)) (x : B) :
    star d.implementer *
        (unitaryConjugationStarAlgHom d x) * d.implementer = x := by
  change star d.implementer *
      (d.implementer * x * star d.implementer) * d.implementer = x
  calc
    star d.implementer *
        (d.implementer * x * star d.implementer) * d.implementer =
        (star d.implementer * d.implementer) * x *
          (star d.implementer * d.implementer) := by
            simp only [mul_assoc]
    _ = x := by rw [d.implementer_left, one_mul, mul_one]

omit [NormOneClass B] [CStarRing B] in
private theorem data_unitaryConjugation_right_inverse
    (d : Data (A := A) (B := B)) (x : B) :
    d.implementer *
        (star d.implementer * x * d.implementer) * star d.implementer = x := by
  calc
    d.implementer *
        (star d.implementer * x * d.implementer) * star d.implementer =
        (d.implementer * star d.implementer) * x *
          (d.implementer * star d.implementer) := by
            simp only [mul_assoc]
    _ = x := by rw [d.implementer_right, one_mul, mul_one]

/-- The implemented conjugation is a native star-algebra equivalence. -/
def unitaryConjugationStarAlgEquiv (d : Data (A := A) (B := B)) :
    B ≃⋆ₐ[ℂ] B := by
  apply StarAlgEquiv.ofBijective (unitaryConjugationStarAlgHom d)
  constructor
  · intro x y hxy
    have := congrArg (fun z => star d.implementer * z * d.implementer) hxy
    simpa only [data_unitaryConjugation_left_inverse d] using this
  · intro y
    refine ⟨star d.implementer * y * d.implementer, ?_⟩
    exact data_unitaryConjugation_right_inverse d y

omit [NormOneClass B] [CStarRing B] in
@[simp] theorem unitaryConjugationStarAlgEquiv_apply
    (d : Data (A := A) (B := B)) (x : B) :
    unitaryConjugationStarAlgEquiv d x =
      d.implementer * x * star d.implementer :=
  rfl

private theorem implementer_norm_eq_one (d : Data (A := A) (B := B)) :
    ‖d.implementer‖ = 1 := by
  have hsquare : ‖d.implementer‖ * ‖d.implementer‖ = 1 := by
    calc
      ‖d.implementer‖ * ‖d.implementer‖ =
          ‖star d.implementer * d.implementer‖ :=
        (CStarRing.norm_star_mul_self).symm
      _ = ‖(1 : B)‖ := by rw [d.implementer_left]
      _ = 1 := norm_one
  have hnonneg : 0 ≤ ‖d.implementer‖ := norm_nonneg _
  nlinarith

private theorem implementer_star_norm_eq_one (d : Data (A := A) (B := B)) :
    ‖star d.implementer‖ = 1 := by
  rw [norm_star, implementer_norm_eq_one d]

private theorem unitary_conjugation_le {B : Type*} [NormedRing B]
    [NormOneClass B] [StarRing B] (u x : B)
    (hu : ‖u‖ = 1) (hstar : ‖star u‖ = 1) :
    ‖u * x * star u‖ ≤ ‖x‖ := by
  calc
    ‖u * x * star u‖ ≤ ‖u * x‖ * ‖star u‖ := norm_mul_le _ _
    _ ≤ (‖u‖ * ‖x‖) * ‖star u‖ := by
      exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖x‖ := by rw [hu, hstar]; ring

theorem unitary_conjugation_norm (d : Data (A := A) (B := B)) (x : B) :
    ‖d.implementer * x * star d.implementer‖ = ‖x‖ := by
  have hu : ‖d.implementer‖ = 1 := implementer_norm_eq_one d
  have hstar : ‖star d.implementer‖ = 1 := implementer_star_norm_eq_one d
  have hupper :
      ‖d.implementer * x * star d.implementer‖ ≤ ‖x‖ :=
    unitary_conjugation_le d.implementer x hu hstar
  have hrecover :
      star d.implementer *
          (d.implementer * x * star d.implementer) * d.implementer = x := by
    calc
      star d.implementer *
          (d.implementer * x * star d.implementer) * d.implementer =
          (star d.implementer * d.implementer) *
            x * (star d.implementer * d.implementer) := by
              simp only [mul_assoc]
      _ = x := by rw [d.implementer_left, one_mul, mul_one]
  have hlower :
      ‖x‖ ≤ ‖d.implementer * x * star d.implementer‖ := by
    calc
      ‖x‖ = ‖star d.implementer *
          (d.implementer * x * star d.implementer) * d.implementer‖ :=
        congrArg norm hrecover.symm
      _ ≤ ‖d.implementer * x * star d.implementer‖ := by
        simpa only [star_star, hstar, hu] using
          unitary_conjugation_le (star d.implementer)
            (d.implementer * x * star d.implementer) hstar (by simpa using hu)
  exact le_antisymm hupper hlower

def pulledNorm (d : Data (A := A) (B := B)) (a : A) : ℝ :=
  ‖d.representation a‖

theorem flow_preserves_pulledNorm (d : Data (A := A) (B := B)) (a : A) :
    pulledNorm d (d.flow a) = pulledNorm d a := by
  unfold pulledNorm
  rw [d.intertwines]
  exact unitary_conjugation_norm d (d.representation a)

omit [NormOneClass B] [CStarRing B] in
theorem flow_intertwines_unitaryConjugationStarAlgEquiv
    (d : Data (A := A) (B := B)) (a : A) :
    d.representation (d.flow a) =
      unitaryConjugationStarAlgEquiv d (d.representation a) :=
  d.intertwines a

section NativeUnitary

variable {C : Type*} [CStarAlgebra C] [Nontrivial C]

/-- Conjugation by a Mathlib unitary in a C-star algebra. -/
def unitaryConjugation (u : unitary C) (x : C) : C :=
  (u : C) * x * (star u : C)

omit [Nontrivial C] in
@[simp] theorem unitaryConjugation_one (u : unitary C) :
    unitaryConjugation u 1 = 1 := by
  simp [unitaryConjugation]

omit [Nontrivial C] in
theorem unitaryConjugation_left_inverse (u : unitary C) (x : C) :
    unitaryConjugation (star u) (unitaryConjugation u x) = x := by
  simp only [unitaryConjugation, Unitary.coe_star, star_star]
  change (star (u : C)) * ((u : C) * x * star (u : C)) * (u : C) = x
  calc
    star (u : C) * ((u : C) * x * star (u : C)) * (u : C) =
        (star (u : C) * (u : C)) * x *
          (star (u : C) * (u : C)) := by noncomm_ring
    _ = x := by rw [Unitary.coe_star_mul_self, one_mul, mul_one]

theorem unitaryConjugation_norm (u : unitary C) (x : C) :
    ‖unitaryConjugation u x‖ = ‖x‖ := by
  have hbound (v : unitary C) (z : C) :
      ‖unitaryConjugation v z‖ ≤ ‖z‖ := by
    calc
      ‖unitaryConjugation v z‖ ≤
          ‖(v : C) * z‖ * ‖(star v : C)‖ := norm_mul_le _ _
      _ ≤ (‖(v : C)‖ * ‖z‖) * ‖(star v : C)‖ := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖z‖ := by
        rw [CStarRing.norm_of_mem_unitary v.prop,
          norm_star, CStarRing.norm_of_mem_unitary v.prop,
          one_mul, mul_one]
  apply le_antisymm (hbound u x)
  have hreverse := hbound (star u) (unitaryConjugation u x)
  simpa [unitaryConjugation_left_inverse u x] using hreverse

omit [Nontrivial C] in
theorem unitaryConjugation_injective (u : unitary C) :
    Function.Injective (unitaryConjugation u) := by
  intro x y hxy
  exact (unitaryConjugation_left_inverse u x).symm.trans
    ((congrArg (unitaryConjugation (star u)) hxy).trans
      (unitaryConjugation_left_inverse u y))

end NativeUnitary

end InfoGeometry.Canonical.ModularFlowIsometry
