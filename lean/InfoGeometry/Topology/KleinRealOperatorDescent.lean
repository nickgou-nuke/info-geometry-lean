import InfoGeometry.Topology.KleinBottleOrbitQuotient
import InfoGeometry.Canonical.DiscreteDiracHodgeChiral

/-! Real linear operators on the existing glide quotient. Descent requires
preservation of glide-invariant fields; no spectral or dynamical hypothesis
is inferred from the quotient construction. -/

noncomputable section

namespace InfoGeometry.Topology.KleinRealOperatorDescent

open KleinBrillouinBase KleinBottleOrbitQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def invariantFields : Submodule ℝ (BrillouinTorus → V) where
  carrier := {field | ∀ point, field (torusGlide point) = field point}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro first second first_fixed second_fixed point
    exact congrArg₂ (· + ·) (first_fixed point) (second_fixed point)
  smul_mem' := by
    intro scalar field fixed point
    exact congrArg (scalar • ·) (fixed point)

def fieldEquiv : (KleinBrillouinQuotient → V) ≃ₗ[ℝ] invariantFields where
  toFun field := ⟨fun point => field (quotientMap point), fun point =>
    congrArg field (quotientMap_glide point)⟩
  invFun field := Quotient.lift (field : BrillouinTorus → V) (by
    intro first second related
    rcases related with rfl | related
    · rfl
    · rw [related, field.property first])
  left_inv := by
    intro field
    funext point
    obtain ⟨representative, rfl⟩ := quotientMap_surjective point
    rfl
  right_inv := by
    intro field
    apply Subtype.ext
    rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem fieldEquiv_apply (field : KleinBrillouinQuotient → V)
    (point : BrillouinTorus) :
    fieldEquiv field point = field (quotientMap point) := rfl

@[simp] theorem fieldEquiv_symm_apply (field : invariantFields (V := V))
    (point : BrillouinTorus) :
    fieldEquiv.symm field (quotientMap point) = field point := rfl

def glidePullback : Module.End ℝ (BrillouinTorus → V) where
  toFun field point := field (torusGlide point)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem commuting_preserves_invariants
    (operator : Module.End ℝ (BrillouinTorus → V))
    (commutes : Commute operator glidePullback)
    (field : invariantFields (V := V)) :
    operator field ∈ invariantFields := by
  intro point
  have fixed : glidePullback (field : BrillouinTorus → V) = field :=
    funext field.property
  have transported := congrFun (LinearMap.congr_fun commutes.eq
    (field : BrillouinTorus → V)) point
  change operator (glidePullback field) point =
    operator field (torusGlide point) at transported
  rw [fixed] at transported
  exact transported.symm

def restrictOperator (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) : Module.End ℝ (invariantFields (V := V)) :=
  operator.restrict (fun field fixed => preserves ⟨field, fixed⟩)

def quotientOperator (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) : Module.End ℝ (KleinBrillouinQuotient → V) :=
  fieldEquiv.symm.conjAlgEquiv ℝ (restrictOperator operator preserves)

@[simp] theorem quotientOperator_apply
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields)
    (field : KleinBrillouinQuotient → V) (point : BrillouinTorus) :
    quotientOperator operator preserves field (quotientMap point) =
      operator (fun representative => field (quotientMap representative)) point := rfl

theorem quotientOperator_unique
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields)
    (candidate : Module.End ℝ (KleinBrillouinQuotient → V))
    (evaluation : ∀ field point, candidate field (quotientMap point) =
      operator (fun representative => field (quotientMap representative)) point) :
    candidate = quotientOperator operator preserves := by
  ext field point
  obtain ⟨representative, rfl⟩ := quotientMap_surjective point
  exact evaluation field representative

theorem restrictOperator_sq_zero
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) (square : operator * operator = 0) :
    restrictOperator operator preserves * restrictOperator operator preserves = 0 := by
  apply LinearMap.ext
  intro field
  apply Subtype.ext
  exact LinearMap.congr_fun square (field : BrillouinTorus → V)

theorem quotientOperator_sq_zero
    (operator : Module.End ℝ (BrillouinTorus → V))
    (preserves : ∀ field : invariantFields (V := V),
      operator field ∈ invariantFields) (square : operator * operator = 0) :
    quotientOperator operator preserves * quotientOperator operator preserves = 0 := by
  unfold quotientOperator
  rw [← map_mul, restrictOperator_sq_zero operator preserves square, map_zero]

theorem quotient_dirac_square
    (differential codifferential : Module.End ℝ (BrillouinTorus → V))
    (differential_preserves : ∀ field : invariantFields (V := V),
      differential field ∈ invariantFields)
    (codifferential_preserves : ∀ field : invariantFields (V := V),
      codifferential field ∈ invariantFields)
    (differential_square : differential * differential = 0)
    (codifferential_square : codifferential * codifferential = 0) :
    let descendedD := quotientOperator differential differential_preserves
    let descendedCod := quotientOperator codifferential codifferential_preserves
    Canonical.DiscreteDiracHodgeChiral.diracHodge descendedD descendedCod *
        Canonical.DiscreteDiracHodgeChiral.diracHodge descendedD descendedCod =
      Canonical.DiscreteDiracHodgeChiral.hodgeLaplacian descendedD descendedCod := by
  exact Canonical.DiscreteDiracHodgeChiral.diracHodge_sq_eq_hodgeLaplacian _ _
    (quotientOperator_sq_zero differential differential_preserves differential_square)
    (quotientOperator_sq_zero codifferential codifferential_preserves codifferential_square)

end InfoGeometry.Topology.KleinRealOperatorDescent
