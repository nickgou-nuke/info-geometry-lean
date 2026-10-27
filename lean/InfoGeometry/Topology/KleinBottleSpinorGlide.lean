import InfoGeometry.Topology.KleinBrillouinBase
import InfoGeometry.Clifford.Cl11CliffordMapIsometryBridge
import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Twistor.TwistorKinematicTensor

/-!
# A specific spinorial lift of the actual Klein glide

The covering glide is `(x,y) -> (x+pi,-y)`, whose square is a translation,
not the identity. Its split tangent reflection is lifted by the negative
unit vector of the existing native Cl(1,1). The twisted adjoint gives the
reflection, whereas the action on spinors squares to minus identity.

This fixes a lift and its periodicity data. Nonorientability alone does not
select the lift, and a split Pin(1,1) convention is not silently renamed a
Euclidean Pin+ or Pin- structure. We construct a representation of the
existing presented Klein group and genuine equivariant sections; no smooth
associated-bundle classification or physical spin spectrum is asserted.
-/

noncomputable section
namespace InfoGeometry.Topology.KleinBottleSpinorGlide

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor
open InfoGeometry.Twistor.PerjesConventions
open KleinBrillouinBase
open scoped Matrix

/-- The actual negative Clifford generator, not a new abstract reflection. -/
def pinGenerator : CliffordAlgebra q11 := CliffordAlgebra.ι q11 (0, 1)

lemma pinGenerator_sq : pinGenerator * pinGenerator = -1 := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_neg, map_one]
  exact cl11EquivMat_iota_neg_sq

/-- Explicit inverse of the chosen Clifford lift. -/
def pinLift : (CliffordAlgebra q11)ˣ where
  val := pinGenerator
  inv := -pinGenerator
  val_inv := by rw [mul_neg, pinGenerator_sq, neg_neg]
  inv_val := by rw [neg_mul, pinGenerator_sq, neg_neg]

lemma cl11EquivMat_generator (v : Vec11) :
    cl11EquivMat (CliffordAlgebra.ι q11 v) = gen v := by
  change cl11ToMat (CliffordAlgebra.ι q11 v) = gen v
  simp [cl11ToMat]

/-- Twisted, not ordinary, Pin conjugation gives the glide's linear reflection. -/
theorem pin_twisted_adjoint (v : Vec11) :
    -pinGenerator * CliffordAlgebra.ι q11 v * (-pinGenerator) =
      CliffordAlgebra.ι q11 (splitReflection v) := by
  apply cl11EquivMat.injective
  simp only [map_mul, map_neg, pinGenerator, cl11EquivMat_iota_neg,
    cl11EquivMat_generator]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [gen, Eplus, Eminus, splitReflection, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Complex extension of the same real two-component Clifford spinor action. -/
def spinorLift : Spinor2 ≃ₗ[ℂ] Spinor2 where
  toFun := raiseSpinor
  invFun p := -raiseSpinor p
  left_inv p := by ext a; fin_cases a <;> simp [raiseSpinor]
  right_inv p := by ext a; fin_cases a <;> simp [raiseSpinor]
  map_add' p q := by ext a; fin_cases a <;> simp [raiseSpinor, add_comm]
  map_smul' c p := by ext a; fin_cases a <;> simp [raiseSpinor, smul_eq_mul]

/-- This is the existing Eminus action, not just a matrix with the right square. -/
theorem spinorLift_real_matrix (s : Fin 2 → ℝ) :
    spinorLift (fun a => (s a : ℂ)) = fun a => ((Eminus.mulVec s) a : ℂ) := by
  ext a
  fin_cases a <;> simp [spinorLift, raiseSpinor, Eminus, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

@[simp] theorem spinorLift_sq (p : Spinor2) : spinorLift (spinorLift p) = -p :=
  raiseSpinor_twice p

theorem spinorLift_four (p : Spinor2) :
    spinorLift (spinorLift (spinorLift (spinorLift p))) = p := by simp

/-- The Clifford volume/chirality matrix is exchanged by the odd lift. -/
theorem lift_reverses_clifford_chirality : Eminus * J1 = -(J1 * Eminus) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Coefficient-wise extension to the existing two-spinor twistor carrier.
This acts in the fibre over the independent Klein base, not on Minkowski points. -/
def twistorLift : Twistor4 ≃ₗ[ℂ] Twistor4 := spinorLift.prodCongr spinorLift

@[simp] theorem twistorLift_apply (Z : Twistor4) :
    twistorLift Z = (raiseSpinor Z.1, raiseSpinor Z.2) := rfl

@[simp] theorem twistorLift_sq (Z : Twistor4) : twistorLift (twistorLift Z) = -Z := by
  apply Prod.ext <;> exact raiseSpinor_twice _

theorem twistorLift_four (Z : Twistor4) :
    twistorLift (twistorLift (twistorLift (twistorLift Z))) = Z := by simp

theorem wittPair_twistorLift (Z W : Twistor4) :
    wittPair (twistorLift Z) (twistorLift W) = wittPair Z W := by
  simp [wittPair, raiseSpinor, Fin.sum_univ_two]
  ring

/-- The central sign disappears from the actual quadratic particle tensor. -/
theorem kinematic_double_lift (Z : Twistor4) :
    kinematic (twistorLift (twistorLift Z)) = kinematic Z := by simp

/-- Spinorial monodromy of the presented group for this specified lift.
The transverse cycle is assigned identity; its value is not left implicit. -/
def fibreMonodromy : KleinGroup →* Equiv.Perm Twistor4 :=
  kleinRep twistorLift.toEquiv 1 (by simp)

theorem fibreMonodromy_generators :
    fibreMonodromy (toKlein genA) = twistorLift.toEquiv ∧
    fibreMonodromy (toKlein genB) = 1 :=
  kleinRep_relator_relation _ _ _

/-- The affine glide and spinor action are joined on the actual total carrier. -/
def glideTotal : Equiv.Perm (Cover × Twistor4) where
  toFun x := (glide x.1, twistorLift x.2)
  invFun x := (glideInv x.1, twistorLift.symm x.2)
  left_inv x := Prod.ext (glide_left_inverse x.1) (twistorLift.symm_apply_apply x.2)
  right_inv x := Prod.ext (glide_right_inverse x.1) (twistorLift.apply_symm_apply x.2)

def transverseTotal : Equiv.Perm (Cover × Twistor4) where
  toFun x := (ty x.1, x.2)
  invFun x := (tyInv x.1, x.2)
  left_inv x := by apply Prod.ext <;> simp [ty, tyInv]
  right_inv x := by apply Prod.ext <;> simp [ty, tyInv]

theorem total_klein_relation :
    glideTotal * transverseTotal * glideTotal⁻¹ = transverseTotal⁻¹ := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · exact glide_conj_ty x.1
  · exact twistorLift.apply_symm_apply x.2

def totalMonodromy : KleinGroup →* Equiv.Perm (Cover × Twistor4) :=
  kleinRep glideTotal transverseTotal total_klein_relation

/-- Geometric square and spinorial square have different readouts. -/
theorem glideTotal_sq (k : Cover) (Z : Twistor4) :
    glideTotal (glideTotal (k, Z)) = (tx k, -Z) := by
  exact Prod.ext (glide_sq k) (twistorLift_sq Z)

/-- Sections obey the actual affine gluing, not a fixed-vector condition. -/
def equivariantSections : Submodule ℂ (Cover → Twistor4) where
  carrier := {f | (∀ k, f (glide k) = twistorLift (f k)) ∧ (∀ k, f (ty k) = f k)}
  zero_mem' := by constructor <;> intro k <;> simp
  add_mem' hf hg := by
    constructor
    · intro k
      simp only [Pi.add_apply, hf.1 k, hg.1 k, map_add]
    · intro k
      simp only [Pi.add_apply, hf.2 k, hg.2 k]
  smul_mem' c f hf := by
    constructor
    · intro k
      simp only [Pi.smul_apply, hf.1 k, map_smul]
    · intro k
      simp only [Pi.smul_apply, hf.2 k]

theorem section_longitudinal_antiperiodic (f : equivariantSections) (k : Cover) :
    f (tx k) = -f k := by
  rw [← glide_sq k, f.property.1, f.property.1, twistorLift_sq]

theorem section_kinematic_periodic (f : equivariantSections) (k : Cover) :
    kinematic (f (tx k)) = kinematic (f k) := by
  rw [section_longitudinal_antiperiodic, kinematic_neg]

/-- Imposing ordinary torus periodicity on these antiperiodic spinors kills the section. -/
theorem periodic_equivariant_section_zero (f : equivariantSections)
    (hperiod : ∀ k, f (tx k) = f k) : (f : Cover → Twistor4) = 0 := by
  funext k
  have h : -(f k) = f k := (section_longitudinal_antiperiodic f k).symm.trans (hperiod k)
  apply Prod.ext <;> funext a
  · have ha := congrArg (fun Z : Twistor4 => Z.1 a) h
    change -(f k).1 a = (f k).1 a at ha
    linear_combination -(1 / 2 : ℂ) * ha
  · have ha := congrArg (fun Z : Twistor4 => Z.2 a) h
    change -(f k).2 a = (f k).2 a at ha
    linear_combination -(1 / 2 : ℂ) * ha

/-- A nonzero, explicitly smooth-on-the-cover half-angle section. -/
def halfAngleSection (k : Cover) : Twistor4 :=
  (0, ![((Real.cos (k.1 / 2) : ℝ) : ℂ), -((Real.sin (k.1 / 2) : ℝ) : ℂ)])

theorem halfAngleSection_equivariant : halfAngleSection ∈ equivariantSections := by
  constructor
  · intro k
    have h : (k.1 + Real.pi) / 2 = k.1 / 2 + Real.pi / 2 := by ring
    apply Prod.ext <;> funext a <;> fin_cases a <;>
      simp [halfAngleSection, glide, twistorLift, spinorLift, raiseSpinor,
        h, Real.cos_add, Real.sin_add]
  · intro k
    rfl

theorem contDiff_halfAngleSection : ContDiff ℝ ⊤ halfAngleSection := by
  unfold halfAngleSection
  fun_prop

theorem halfAngleSection_nonzero : halfAngleSection (0, 0) ≠ 0 := by
  intro h
  have h0 := congrArg (fun Z : Twistor4 => Z.2 0) h
  norm_num [halfAngleSection] at h0

end InfoGeometry.Topology.KleinBottleSpinorGlide
