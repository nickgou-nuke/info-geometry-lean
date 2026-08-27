import InfoGeometry.Exceptional.FreudenthalSymplecticAction
import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Exceptional.SymplecticTripleSystem

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

def freudenthalOmega (D : CubicJordanDatum J) :
    FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J →ₗ[ℝ] ℝ where
  toFun X := symplecticFormLinear D X
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    exact symplecticForm_add_left D X Y Z
  map_smul' r X := by
    apply LinearMap.ext
    intro Z
    change FreudenthalCharge.symplecticForm D (r • X) Z =
      r • FreudenthalCharge.symplecticForm D X Z
    rw [symplecticForm_smul_left]
    rfl

@[simp] theorem freudenthalOmega_apply
    (D : CubicJordanDatum J) (X Y : FreudenthalCharge J) :
    freudenthalOmega D X Y = FreudenthalCharge.symplecticForm D X Y := rfl

def freudenthalTripleLeft (D : CubicJordanDatum J) (Y : FreudenthalCharge J) :
    FreudenthalCharge J →ₗ[ℝ]
      FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J where
  toFun X := symplecticRankTwo D X Y
  map_add' X X' := by
    apply LinearMap.ext
    intro Z
    change symplecticRankTwo D (X + X') Y Z =
      symplecticRankTwo D X Y Z + symplecticRankTwo D X' Y Z
    simp only [symplecticRankTwo_apply, symplecticForm_add_left]
    module
  map_smul' r X := by
    apply LinearMap.ext
    intro Z
    change symplecticRankTwo D (r • X) Y Z =
      r • symplecticRankTwo D X Y Z
    simp only [symplecticRankTwo_apply, symplecticForm_smul_left]
    module

def freudenthalTriple (D : CubicJordanDatum J) :
    FreudenthalCharge J →ₗ[ℝ]
      FreudenthalCharge J →ₗ[ℝ]
        FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J where
  toFun X := {
    toFun := fun Y => {
      toFun := fun Z => symplecticRankTwo D X Y Z
      map_add' Z Z' := by
        simp only [symplecticRankTwo_apply, symplecticForm_add_right]
        module
      map_smul' r Z := by
        change symplecticRankTwo D X Y (r • Z) =
          r • symplecticRankTwo D X Y Z
        simp only [symplecticRankTwo_apply, symplecticForm_smul_right,
          smul_add]
        module }
    map_add' Y Y' := by
      apply LinearMap.ext
      intro Z
      change symplecticRankTwo D X (Y + Y') Z =
        symplecticRankTwo D X Y Z + symplecticRankTwo D X Y' Z
      simp only [symplecticRankTwo_apply, symplecticForm_add_left,
        smul_add]
      module
    map_smul' r Y := by
      apply LinearMap.ext
      intro Z
      change symplecticRankTwo D X (r • Y) Z =
        r • symplecticRankTwo D X Y Z
      simp only [symplecticRankTwo_apply, symplecticForm_smul_left,
        smul_add]
      module }
  map_add' X X' := by
    apply LinearMap.ext
    intro Y
    apply LinearMap.ext
    intro Z
    change symplecticRankTwo D (X + X') Y Z =
      symplecticRankTwo D X Y Z + symplecticRankTwo D X' Y Z
    simp only [symplecticRankTwo_apply, symplecticForm_add_left,
      smul_add]
    module
  map_smul' r X := by
    apply LinearMap.ext
    intro Y
    apply LinearMap.ext
    intro Z
    change symplecticRankTwo D (r • X) Y Z =
      r • symplecticRankTwo D X Y Z
    simp only [symplecticRankTwo_apply, symplecticForm_smul_left,
      smul_add]
    module

@[simp] theorem freudenthalTriple_apply
    (D : CubicJordanDatum J) (X Y Z : FreudenthalCharge J) :
    freudenthalTriple D X Y Z = symplecticRankTwo D X Y Z := rfl

noncomputable def freudenthalSymplecticTripleSystem (D : CubicJordanDatum J) :
    SymplecticTripleSystemDatum (FreudenthalCharge J) where
  omega := freudenthalOmega D
  omega_alt := by
    intro x
    exact FreudenthalCharge.symplectic_form_alternating D x
  triple := freudenthalTriple D
  triple_symm₁₂ := by
    intro x y z
    exact congrArg (fun T : Module.End ℝ (FreudenthalCharge J) => T z)
      (symplecticRankTwo_swap D x y)
  triple_swap₂₃ := by
    intro x y z
    simpa only [freudenthalTriple_apply, freudenthalOmega_apply] using
      symplecticRankTwo_swap23 D x y z
  triple_derivation := by
    intro x y u v w
    have h := symplectic_rankTwo_commutator_rankTwo D x y u v
    have hw := congrArg (fun T : Module.End ℝ (FreudenthalCharge J) => T w) h
    change symplecticRankTwo D x y (symplecticRankTwo D u v w) -
        symplecticRankTwo D u v (symplecticRankTwo D x y w) = _ at hw
    simp only [LinearMap.add_apply] at hw
    change symplecticRankTwo D x y (symplecticRankTwo D u v w) = _
    calc
      symplecticRankTwo D x y (symplecticRankTwo D u v w) =
          (symplecticRankTwo D x y (symplecticRankTwo D u v w) -
            symplecticRankTwo D u v (symplecticRankTwo D x y w)) +
            symplecticRankTwo D u v (symplecticRankTwo D x y w) := by module
      _ = (symplecticRankTwo D ((symplecticRankTwo D x y) u) v) w +
          (symplecticRankTwo D u ((symplecticRankTwo D x y) v)) w +
          symplecticRankTwo D u v (symplecticRankTwo D x y w) := by
            rw [hw]
  omega_invariant := by
    intro x y u v
    simpa only [freudenthalOmega_apply, freudenthalTriple_apply] using
      symplecticRankTwo_preserves D x y u v

@[simp] theorem freudenthal_innerDerivation_eq_rankTwo
    (D : CubicJordanDatum J) (x y : FreudenthalCharge J) :
    innerDerivation (freudenthalSymplecticTripleSystem D) x y =
      symplecticRankTwo D x y := rfl

@[simp] theorem freudenthal_innerDerivation_eq_mixedBracket
    (D : CubicJordanDatum J) (x y : FreudenthalCharge J) :
    innerDerivation (freudenthalSymplecticTripleSystem D) x y =
      (mixedSymplecticBracket D x y : Module.End ℝ (FreudenthalCharge J)) := by
  rfl

end InfoGeometry.Exceptional.Freudenthal
