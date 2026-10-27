import InfoGeometry.Topology.KleinCliffordPinLift

/-!
# Associated orbit spaces and equivariant spinor fields

The full affine deck group, not its involutive torus shadow, acts on the fibre.
Thus a negative Clifford lift can be antiperiodic under a full translation.
These are actual quotient carriers and sections. Local triviality and a smooth
connection are not inferred from the algebraic quotient construction alone.
-/
noncomputable section
namespace InfoGeometry.Topology.KleinAssociatedSpinors
open KleinQuotientDeckInvariants KleinDeckRepresentation KleinCliffordPinLift
open scoped KleinDeckRepresentation Matrix
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Native module-valued deck equivariance, retaining the spatial base point. -/
def equivariantSections (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) :
    Submodule ℂ (PlanePoint → E) where
  carrier := {ψ | ∀ g p, ψ (deckAction g p)=ρ g (ψ p)}
  zero_mem' := by intros; simp
  add_mem' := by intro f h hf hh g p; simp [hf g p,hh g p]
  smul_mem' := by intro c f hf g p; simp [hf g p]

/-- The existing affine action on the total space of the trivial cover bundle. -/
def totalAction (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (g : KleinDeckGroup) (x : PlanePoint × E) : PlanePoint × E :=
  (deckAction g x.1, ρ g x.2)

@[simp] theorem totalAction_one (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) (x : PlanePoint × E) :
    totalAction ρ 1 x=x := by simp [totalAction,deckAction_one]

theorem totalAction_mul (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (g h : KleinDeckGroup) (x : PlanePoint × E) :
    totalAction ρ (g*h) x=totalAction ρ g (totalAction ρ h x) := by
  simp [totalAction,deckAction_mul,map_mul]

/-- Full-cover orbit relation; no periodic spinor trivialization is imposed. -/
def associatedSetoid (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) : Setoid (PlanePoint × E) where
  r x y := ∃ g, totalAction ρ g x=y
  iseqv := by
    constructor
    · intro x; exact ⟨1,totalAction_one ρ x⟩
    · intro x y h
      obtain ⟨g,rfl⟩ := h
      exact ⟨g⁻¹, by rw [← totalAction_mul]; simp⟩
    · intro x y z hxy hyz
      obtain ⟨g,rfl⟩ := hxy
      obtain ⟨h,rfl⟩ := hyz
      exact ⟨h*g,totalAction_mul ρ h g x⟩

def deckOrbitSetoid : Setoid PlanePoint where
  r p q := ∃ g, deckAction g p=q
  iseqv := by
    constructor
    · intro p; exact ⟨1,deckAction_one p⟩
    · intro p q h
      obtain ⟨g,rfl⟩ := h
      exact ⟨g⁻¹, by rw [← deckAction_mul]; simpa using deckAction_one p⟩
    · intro p q r hpq hqr
      obtain ⟨g,rfl⟩ := hpq
      obtain ⟨h,rfl⟩ := hqr
      exact ⟨h*g,deckAction_mul h g p⟩

abbrev DeckOrbitBase := Quotient deckOrbitSetoid
abbrev AssociatedSpace (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) := Quotient (associatedSetoid ρ)

def bundleProjection (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E)) : AssociatedSpace ρ → DeckOrbitBase :=
  Quotient.map Prod.fst (by
    intro x y h
    obtain ⟨g,hg⟩ := h
    exact ⟨g,congrArg Prod.fst hg⟩)

/-- An equivariant field really descends to a section of the associated quotient. -/
def descendedSection (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (ψ : equivariantSections ρ) : DeckOrbitBase → AssociatedSpace ρ :=
  Quotient.lift (fun p => Quotient.mk _ (p,ψ p)) (by
    intro p q h
    obtain ⟨g,rfl⟩ := h
    apply Quotient.sound
    exact ⟨g,by simp [totalAction,ψ.property g p]⟩)

theorem descendedSection_projects (ρ : KleinDeckGroup →* (E ≃ₗ[ℂ] E))
    (ψ : equivariantSections ρ) (q : DeckOrbitBase) :
    bundleProjection ρ (descendedSection ρ ψ q)=q := by
  induction q using Quotient.inductionOn
  rfl

/-- The same unit acts on both actual spinor blocks of a twistor. -/
def twistorBlockAction (R : Matˣ) : Twistor4 ≃ₗ[ℂ] Twistor4 where
  toFun Z := (R.val.mulVec Z.1,R.val.mulVec Z.2)
  invFun Z := (R.inv.mulVec Z.1,R.inv.mulVec Z.2)
  left_inv Z := by simp [Matrix.mulVec_mulVec]
  right_inv Z := by simp [Matrix.mulVec_mulVec]
  map_add' Z W := by simp [Matrix.mulVec_add]
  map_smul' c Z := by simp [Matrix.mulVec_smul]

def twistorBlockHom : Matˣ →* (Twistor4 ≃ₗ[ℂ] Twistor4) where
  toFun := twistorBlockAction
  map_one' := by ext Z <;> simp [twistorBlockAction]
  map_mul' R S := by ext Z <;> simp [twistorBlockAction,Matrix.mulVec_mulVec]

def twistorPlusMonodromy (s t : Bool) : KleinDeckGroup →* (Twistor4 ≃ₗ[ℂ] Twistor4) :=
  twistorBlockHom.comp (plusMonodromy s t)

def twistorMinusMonodromy (s t : Bool) : KleinDeckGroup →* (Twistor4 ≃ₗ[ℂ] Twistor4) :=
  twistorBlockHom.comp (minusMonodromy s t)

/-- Minus-lift monodromy is visible on the twistor, but not on its quadratic kinematics. -/
theorem kinematic_negative_holonomy (Z : Twistor4) : kinematic (-Z)=kinematic Z := by
  simpa using kinematic_phase_invariant (-1 : ℂ) (by norm_num) Z

theorem twistorMinus_double_glide (s t : Bool) (Z : Twistor4) :
    twistorMinusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) Z = -Z := by
  change twistorBlockAction (minusMonodromy s t
    (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)) Z = -Z
  simp [twistorBlockAction,minus_double_glide]

theorem equivariant_kinematic_double_glide (s t : Bool)
    (ψ : equivariantSections (twistorMinusMonodromy s t)) (p : PlanePoint) :
    kinematic (ψ (p.1,p.2+2))=kinematic (ψ p) := by
  have h := ψ.property (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) p
  have hb : deckAction (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b) p =
      (p.1,p.2+2) := by simp [deckAction,KleinDeckGroup.mul,KleinDeckGroup.b,signR,signZ]
  rw [hb,twistorMinus_double_glide] at h
  rw [h,kinematic_negative_holonomy]

/-- A nonzero smooth cover-level field realizes the negative-glide boundary condition. -/
def minusWave (p : PlanePoint) : Spinor :=
  Complex.exp (((Real.pi / 2 * p.2 : ℝ) : ℂ) * Complex.I) • ![1,1]

private theorem exp_half_pi :
    Complex.exp (((Real.pi/2 : ℝ):ℂ)*Complex.I)=Complex.I := by
  apply Complex.ext <;> simp [Complex.exp_re,Complex.exp_im]

theorem minusWave_glide (p : PlanePoint) :
    minusWave (deckB p)=reflectionMinus.mulVec (minusWave p) := by
  have he : (((Real.pi/2*(p.2+1):ℝ):ℂ)*Complex.I)=
      (((Real.pi/2*p.2:ℝ):ℂ)*Complex.I)+(((Real.pi/2:ℝ):ℂ)*Complex.I) := by push_cast; ring
  ext i
  fin_cases i <;>
    simp [minusWave,deckB,he,Complex.exp_add,exp_half_pi,reflectionMinus,reflectionPlus,
      Matrix.mulVec,dotProduct,Fin.sum_univ_two,smul_eq_mul,mul_comm]

theorem minusWave_nonzero : minusWave (0,0) ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 2)
  norm_num [minusWave] at hh

end InfoGeometry.Topology.KleinAssociatedSpinors
