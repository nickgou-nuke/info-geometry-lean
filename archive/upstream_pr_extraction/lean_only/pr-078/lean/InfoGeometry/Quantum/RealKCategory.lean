import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Clifford.LogCftMonodromy

open CategoryTheory
open InfoGeometry.Clifford.LogCftMonodromy

/-!
# InfoGeometry.Quantum.RealKCategory

Categorical real/complex bridge via an internal square-minus-one operator.

`RealKVect` bundles a real vector space with a distinguished endomorphism
`K` satisfying `K^2 = -Id`. Morphisms are real-linear maps commuting with `K`.

This module provides a concrete first categorical layer:
- the category `RealKVect`;
- a derived complex action on each object from `K`;
- a functor `ModuleCat ℂ ⥤ RealKVect` (complex spaces as real spaces with `K := I•`).
-/

universe u

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Quantum.RealKCategory

/-- Real vector spaces with an internal complex axis `K^2 = -Id`. -/
structure RealKVect where
  V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℝ V]
  K : V →ₗ[ℝ] V
  K_sq : K.comp K = -(LinearMap.id : V →ₗ[ℝ] V)

attribute [instance] RealKVect.instAddCommGroup RealKVect.instModule

instance : CoeSort RealKVect (Type u) := ⟨RealKVect.V⟩

namespace RealKVect

/-- Scalar decomposition in a complex module: `z • v = re(z)•v + im(z)•(I•v)`. -/
private lemma complex_smul_eq_re_im_I_smul
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (z : ℂ) (v : V) :
    z • v = z.re • v + z.im • ((Complex.I : ℂ) • v) := by
  calc
    z • v = ((z.re : ℂ) + z.im * Complex.I) • v := by rw [Complex.re_add_im]
    _ = (z.re : ℂ) • v + (z.im * Complex.I) • v := by rw [add_smul]
    _ = z.re • v + z.im • ((Complex.I : ℂ) • v) := by
      refine congrArg (fun t => z.re • v + t) ?_
      calc
        (z.im * Complex.I) • v = (z.im : ℂ) • ((Complex.I : ℂ) • v) := by
          simpa [smul_smul]
        _ = z.im • ((Complex.I : ℂ) • v) := by
          rfl

/-- Morphisms in `RealKVect`: real-linear maps commuting with `K`. -/
@[ext] structure Hom (X Y : RealKVect) where
  hom : X →ₗ[ℝ] Y
  comm : hom.comp X.K = Y.K.comp hom

instance (X Y : RealKVect) : CoeFun (Hom X Y) (fun _ => X → Y) := ⟨fun f => f.hom⟩

noncomputable instance : Category RealKVect where
  Hom X Y := Hom X Y
  id X :=
    { hom := LinearMap.id
      comm := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      comm := by
        calc
          (g.hom.comp f.hom).comp X.K
              = g.hom.comp (f.hom.comp X.K) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.K.comp f.hom) := by rw [f.comm]
          _ = (g.hom.comp Y.K).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.K.comp g.hom).comp f.hom := by rw [g.comm]
          _ = Z.K.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc] }

@[simp] lemma hom_id (X : RealKVect) : ((𝟙 X : X ⟶ X).hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : RealKVect} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).hom) = g.hom.comp f.hom := rfl

/-- Derived real action of a complex scalar through `K`. -/
noncomputable def complexSMul (X : RealKVect) (z : ℂ) (v : X) : X :=
  z.re • v + z.im • (X.K v)

/-- Derived complex module structure on a `RealKVect` object. -/
noncomputable def complexModule (X : RealKVect) : Module ℂ X where
  smul z v := complexSMul X z v
  one_smul v := by
    change ((1 : ℂ).re • v + (1 : ℂ).im • X.K v = v)
    simp [complexSMul]
  mul_smul z w v := by
    rcases z with ⟨a, b⟩
    rcases w with ⟨c, d⟩
    have hK2 : X.K (X.K v) = -v := by
      have h := congrArg (fun T : X →ₗ[ℝ] X => T v) X.K_sq
      simpa using h
    change ((a * c - b * d) • v + (a * d + b * c) • X.K v)
      = a • (c • v + d • X.K v) + b • X.K (c • v + d • X.K v)
    calc
      (a * c - b * d) • v + (a * d + b * c) • X.K v
          = (a * c + -1 • (b * d)) • v + ((a * d) • X.K v + (b * c) • X.K v) := by
              simp [sub_eq_add_neg, add_smul, smul_add, smul_smul, mul_assoc, mul_left_comm,
                mul_comm]
      _ = (a * c) • v + ((-1 : ℝ) • (b * d) • v + ((a * d) • X.K v + (b * c) • X.K v)) := by
            simp [add_smul, add_assoc, add_left_comm, add_comm]
      _ = a • (c • v + d • X.K v) + b • X.K (c • v + d • X.K v) := by
            simp [map_add, map_smul, hK2, smul_add, smul_smul, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm]
  smul_add z v w := by
    change z.re • (v + w) + z.im • X.K (v + w)
      = (z.re • v + z.im • X.K v) + (z.re • w + z.im • X.K w)
    simp [complexSMul, map_add, smul_add, add_assoc, add_left_comm, add_comm]
  smul_zero z := by
    change z.re • (0 : X) + z.im • X.K (0 : X) = 0
    simp [complexSMul]
  add_smul z w v := by
    rcases z with ⟨a, b⟩
    rcases w with ⟨c, d⟩
    change ((a + c) • v + (b + d) • X.K v)
      = (a • v + b • X.K v) + (c • v + d • X.K v)
    simp [complexSMul, add_smul, add_assoc, add_left_comm, add_comm]
  zero_smul v := by
    change ((0 : ℂ).re • v + (0 : ℂ).im • X.K v = 0)
    simp [complexSMul]

/-- `Complex.I` acts as the internal operator `K` under the derived action. -/
lemma complexI_smul_eq_K (X : RealKVect) (v : X) :
    letI : Module ℂ X := complexModule X
    (Complex.I : ℂ) • v = X.K v := by
  change (Complex.I.re • v + Complex.I.im • X.K v = X.K v)
  simp

/-- Convert a `RealKVect` object into a complex module object. -/
noncomputable def asComplexModule (X : RealKVect) : ModuleCat ℂ := by
  letI : Module ℂ X := complexModule X
  exact ModuleCat.of ℂ X

/-- Convert a `RealKVect` morphism into a complex-linear map on derived modules. -/
noncomputable def Hom.toComplexLinear {X Y : RealKVect} (f : X ⟶ Y) :
    asComplexModule X ⟶ asComplexModule Y := by
  letI : Module ℂ X := complexModule X
  letI : Module ℂ Y := complexModule Y
  refine ModuleCat.ofHom
    { toFun := f.hom
      map_add' := by simpa using f.hom.map_add
      map_smul' := ?_ }
  intro z x
  rcases z with ⟨a, b⟩
  have hcomm : f.hom (X.K x) = Y.K (f.hom x) := by
    exact congrArg (fun T : X →ₗ[ℝ] Y => T x) f.comm
  change f.hom (a • x + b • X.K x) = a • f.hom x + b • Y.K (f.hom x)
  simp [map_add, map_smul, hcomm]

/-- Backward functor: use the derived complex action from `K`. -/
noncomputable def realKToComplex : RealKVect ⥤ ModuleCat ℂ where
  obj X := asComplexModule X
  map {X Y} f := f.toComplexLinear
  map_id X := by
    rfl
  map_comp f g := by
    rfl

/-- Forward functor: forget to real and remember `K := (I • ·)`. -/
noncomputable def complexToRealK : ModuleCat ℂ ⥤ RealKVect where
  obj W :=
    { V := W
      K :=
        { toFun := fun v => (Complex.I : ℂ) • v
          map_add' := by
            intro v w
            exact smul_add (Complex.I : ℂ) v w
          map_smul' := by
            intro r v
            simpa using (smul_comm (Complex.I : ℂ) r v) }
      K_sq := by
        ext v
        change (Complex.I : ℂ) • ((Complex.I : ℂ) • v) = -v
        simp [smul_smul, Complex.I_mul_I] }
  map {W W'} f :=
    { hom := f.hom.restrictScalars ℝ
      comm := by
        ext v
        simpa using (f.hom.map_smul (Complex.I : ℂ) v) }
  map_id W := by
    rfl
  map_comp f g := by
    rfl

/--
Unit natural isomorphism for the real/complex bridge:
`𝟭_(ModuleCat ℂ) ≅ complexToRealK ⋙ realKToComplex`.
-/
noncomputable def unitIsoComplexRealK :
    𝟭 (ModuleCat ℂ) ≅ complexToRealK ⋙ realKToComplex :=
  NatIso.ofComponents
    (fun W => by
      letI : Module ℂ (complexToRealK.obj W) := complexModule (complexToRealK.obj W)
      refine LinearEquiv.toModuleIso ?_
      refine
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl
          map_add' := by intro x y; rfl
          map_smul' := ?_ }
      intro z x
      simpa [complexSMul, complexToRealK] using
        (complex_smul_eq_re_im_I_smul (V := W) z x))
    (by
      intro X Y f
      ext x
      rfl)

noncomputable abbrev RoundTripObj (X : RealKVect) : RealKVect :=
  (realKToComplex ⋙ complexToRealK).obj X

private abbrev smulOrig (X : RealKVect) (r : ℝ) (x : X) : X := r • x

noncomputable abbrev smulRoundTrip (X : RealKVect) (r : ℝ) (x : RoundTripObj X) : RoundTripObj X :=
  complexSMul X (r : ℂ) (x : X)

private lemma roundTrip_smul_eq_smulRoundTrip (X : RealKVect) (r : ℝ) (x : RoundTripObj X) :
    (r • x : RoundTripObj X) = smulRoundTrip X r x := by
  rfl

private lemma smulRoundTrip_eq_smulOrig (X : RealKVect) (r : ℝ) (x : RoundTripObj X) :
    ((smulRoundTrip X r x : RoundTripObj X) : X) = smulOrig X r (x : X) := by
  simp [smulRoundTrip, smulOrig, complexSMul]

/--
Counit natural isomorphism for the real/complex bridge:
`realKToComplex ⋙ complexToRealK ≅ 𝟭_RealKVect`.
-/
noncomputable def counitIsoComplexRealK :
    realKToComplex ⋙ complexToRealK ≅ 𝟭 RealKVect :=
  NatIso.ofComponents
    (fun X => by
      let homX : (realKToComplex ⋙ complexToRealK).obj X ⟶ X :=
        { hom :=
            { toFun := fun x => x
              map_add' := by intro x y; rfl
              map_smul' := by
                intro r x
                rw [RingHom.id_apply]
                rw [roundTrip_smul_eq_smulRoundTrip X r x]
                change ((smulRoundTrip X r x : RoundTripObj X) : X) = smulOrig X r (x : X)
                exact smulRoundTrip_eq_smulOrig X r x }
          comm := by
            ext x
            change complexSMul X Complex.I x = X.K x
            simp [complexSMul] }
      let invX : X ⟶ (realKToComplex ⋙ complexToRealK).obj X :=
        { hom :=
            { toFun := fun x => x
              map_add' := by intro x y; rfl
              map_smul' := by
                intro r x
                rw [RingHom.id_apply]
                rw [roundTrip_smul_eq_smulRoundTrip X r (x : RoundTripObj X)]
                change smulOrig X r x = (smulRoundTrip X r (x : RoundTripObj X) : RoundTripObj X)
                exact (smulRoundTrip_eq_smulOrig X r (x : RoundTripObj X)).symm }
          comm := by
            ext x
            change X.K x = complexSMul X Complex.I x
            simp [complexSMul] }
      refine
        { hom := homX
          inv := invX
          hom_inv_id := by
            apply RealKVect.Hom.ext
            ext x
            rfl
          inv_hom_id := by
            apply RealKVect.Hom.ext
            ext x
            rfl })
    (by
      intro X Y f
      apply RealKVect.Hom.ext
      ext x
      rfl)

/--
Full categorical equivalence between complex modules and real modules equipped
with an internal square-minus-one operator.
-/
noncomputable def moduleCatComplexEquivRealKVect : ModuleCat ℂ ≌ RealKVect where
  functor := complexToRealK
  inverse := realKToComplex
  unitIso := unitIsoComplexRealK
  counitIso := counitIsoComplexRealK
  functor_unitIso_comp X := by
    apply RealKVect.Hom.ext
    ext x
    rfl

end RealKVect


/-! ## Monodromy diagonalization in `RealKVect` -/

/--
The carrier for the 2-dimensional complex monodromy space, seen as a
`RealKVect` object (ℂ² ≅ ℝ⁴ with `K = i·I`).
-/
noncomputable def monodromyCarrier : RealKVect :=
  RealKVect.complexToRealK.obj (ModuleCat.of ℂ (ℂ × ℂ))

/-! ## Real rotor and nilpotent monodromy in `RealKVect` -/

/--
The real rotor `R(θ) = cos θ·I + sin θ·K` as an endomorphism in `RealKVect`.
Commutation with `K` follows from `I` and `K` commuting with `K`.
-/
noncomputable def rotor (X : RealKVect) (θ : ℝ) : X ⟶ X :=
  let c := (Real.cos θ : ℝ)
  let s := (Real.sin θ : ℝ)
  let L : X →ₗ[ℝ] X := c • LinearMap.id + s • X.K
  { hom := L
    comm := by
      ext x
      have hKsq_x : X.K (X.K x) = -x := by
        have := congrArg (fun T : X →ₗ[ℝ] X => T x) X.K_sq
        simpa using this
      simpa [L, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hKsq_x,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      }

/--
A structured nilpotent morphism inside `RealKVect`.
Extends `RealKVect.Hom X X` with a proof that `hom ∘ hom = 0`.
-/
def NilpotentHom (X : RealKVect) : Type _ :=
  {f : RealKVect.Hom X X // f.hom.comp f.hom = 0}

namespace NilpotentHom

/-- The underlying `RealKVect` morphism of a nilpotent morphism. -/
abbrev toHom {X : RealKVect} (N : NilpotentHom X) : RealKVect.Hom X X :=
  N.1

/-- The nilpotence law carried by the morphism. -/
theorem nilpotent {X : RealKVect} (N : NilpotentHom X) :
    (toHom N).hom.comp (toHom N).hom = 0 :=
  N.2

/-- Construct a nilpotent morphism from a commuting morphism and its square-zero law. -/
def mk {X : RealKVect}
    (f : RealKVect.Hom X X)
    (h : f.hom.comp f.hom = 0) : NilpotentHom X :=
  ⟨f, h⟩

end NilpotentHom

/-- Concrete instantiation of `NilpotentHom` using the zero morphism. -/
def zeroNilpotentHom (X : RealKVect) : NilpotentHom X :=
  NilpotentHom.mk
    { hom := 0
      comm := by ext; simp }
    (by ext; simp)

/-- Commutation lemma for `rotor` and any morphism. -/
lemma rotor_comp_hom (X : RealKVect) (θ : ℝ) (f : X ⟶ X) :
    (rotor X θ).hom.comp f.hom = f.hom.comp (rotor X θ).hom := by
  ext x
  have hcomm := f.comm
  have hfK : f.hom (X.K x) = X.K (f.hom x) := by
    exact congrArg (fun T : X →ₗ[ℝ] X => T x) hcomm
  simp [rotor, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, hfK]

/-- Commutation lemma for `rotor` and `NilpotentHom`. -/
lemma rotor_comp_nilpotent (X : RealKVect) (θ : ℝ) (N : NilpotentHom X) :
    (rotor X θ).hom.comp N.toHom.hom = N.toHom.hom.comp (rotor X θ).hom :=
  rotor_comp_hom X θ N.toHom

/--
The full monodromy projection at a root-of-unity parameter.
Assembles the rotor and nilpotent parts:

    M_real(h) = R(−2πh) ∘ (I + (−2π)·K·N)
-/
noncomputable def monodromyProjection (X : RealKVect) (h : ℝ) (N : NilpotentHom X) : X ⟶ X :=
  { hom := (rotor X (-2 * Real.pi * h)).hom.comp (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom)
    comm := by
      have h_rotor_comm : (rotor X (-2 * Real.pi * h)).hom.comp X.K = X.K.comp (rotor X (-2 * Real.pi * h)).hom :=
        (rotor X (-2 * Real.pi * h)).comm
      have h_N_comm : (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom).comp X.K =
          X.K.comp (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom) := by
        ext x
        simp [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
          LinearMap.id_apply]
        have hN_comm := N.toHom.comm
        have hN_comm_x : N.toHom.hom (X.K x) = X.K (N.toHom.hom x) := by
          simpa using congrArg (fun f : X →ₗ[ℝ] X => f x) hN_comm
        rw [hN_comm_x]
      rw [LinearMap.comp_assoc, h_N_comm, ← LinearMap.comp_assoc, h_rotor_comm, LinearMap.comp_assoc] }

/--
Rotor multiplication: `R(θ₁) ∘ R(θ₂) = R(θ₁ + θ₂)`.
-/
theorem rotor_mul (X : RealKVect) (θ₁ θ₂ : ℝ) :
    (rotor X θ₁).hom.comp (rotor X θ₂).hom = (rotor X (θ₁ + θ₂)).hom := by
  ext x
  have hKsq_x : X.K (X.K x) = -x := by
    have := congrArg (fun T : X →ₗ[ℝ] X => T x) X.K_sq
    simpa using this
  simp [rotor, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, hKsq_x, Real.cos_add, Real.sin_add, smul_add, add_smul, smul_smul,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

/--
Rotor power: `R(θ)ⁿ = R(n·θ)`.
-/
theorem rotor_pow_mul (X : RealKVect) (θ : ℝ) (n : ℕ) :
    (rotor X θ).hom ^ n = (rotor X ((n : ℝ) * θ)).hom := by
  induction n with
  | zero =>
    ext x <;> simp [rotor]
  | succ n ih =>
    rw [pow_succ, ih, Module.End.mul_eq_comp]
    have hmul := rotor_mul X ((n : ℝ) * θ) θ
    have htheta : ((n : ℝ) * θ) + θ = ((n + 1 : ℕ) : ℝ) * θ := by
      rw [Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa [htheta] using hmul

/--
Nilpotent binomial expansion: `(I + c·N)ⁿ = I + (n·c)·N` when `N² = 0`.
-/
theorem nilpotent_binomial_expansion (X : RealKVect) (c : ℝ) (N : NilpotentHom X) (n : ℕ) :
    (LinearMap.id + c • N.toHom.hom) ^ n = LinearMap.id + ((n : ℝ) * c) • N.toHom.hom := by
  induction n with
  | zero =>
    ext x <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext x
    have h_nil : N.toHom.hom (N.toHom.hom x) = 0 := by
      have h := congrArg (fun T : X →ₗ[ℝ] X => T x) N.nilpotent
      simpa using h
    simpa [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      h_nil, add_smul, smul_add, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
      add_assoc, add_left_comm, sub_eq_add_neg, smul_smul, add_comm]

/--
The binomial power theorem for the monodromy at a root of unity.
Because `N² = 0`, the `n`-th power collapses to the first binomial order:

    M_real(h)ⁿ = R(−2πnh) ∘ (I + (−2πn)·K·N)
-/
theorem monodromy_power_binomial (X : RealKVect) (h : ℝ) (N : NilpotentHom X) (n : ℕ) :
    (monodromyProjection X h N).hom ^ n =
      (rotor X (-2 * Real.pi * (n : ℝ) * h)).hom.comp
        (LinearMap.id + (-2 * Real.pi * (n : ℝ)) • N.toHom.hom) := by
  have hComm : Commute (rotor X (-2 * Real.pi * h)).hom
      (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom) := by
    have hRN : (rotor X (-2 * Real.pi * h)).hom.comp N.toHom.hom =
        N.toHom.hom.comp (rotor X (-2 * Real.pi * h)).hom :=
      rotor_comp_nilpotent X (-2 * Real.pi * h) N
    have hRNc : Commute (rotor X (-2 * Real.pi * h)).hom N.toHom.hom := by
      simpa [Commute] using hRN
    exact (Commute.one_right _).add_right (hRNc.smul_right (-2 * Real.pi))
  change ((rotor X (-2 * Real.pi * h)).hom.comp
    (LinearMap.id + (-2 * Real.pi : ℝ) • N.toHom.hom)) ^ n =
      (rotor X (-2 * Real.pi * (n : ℝ) * h)).hom.comp
        (LinearMap.id + (-2 * Real.pi * (n : ℝ)) • N.toHom.hom)
  have hpow := Commute.mul_pow hComm n
  rw [rotor_pow_mul, nilpotent_binomial_expansion] at hpow
  simpa [Module.End.mul_eq_comp, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hpow

/--
The Hadjiivanov monodromy at complex `h` as an endomorphism of `monodromyCarrier`.
-/
noncomputable def hadjiivanovMonodromy_asRealK (h : ℂ) : monodromyCarrier ⟶ monodromyCarrier :=
  let M : Matrix (Fin 2) (Fin 2) ℂ := hadjiivanovMonodromy h
  let f : ℂ × ℂ → ℂ × ℂ := fun (v : ℂ × ℂ) => (M 0 0 * v.1 + M 0 1 * v.2, M 1 0 * v.1 + M 1 1 * v.2)
  have h_add : ∀ (x y : ℂ × ℂ), f (x + y) = f x + f y := by
    rintro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩; ext <;> dsimp [f] <;> ring
  have h_smul : ∀ (z : ℂ) (x : ℂ × ℂ), f (z • x) = z • f x := by
    rintro z ⟨a,b⟩; ext <;> dsimp [f, smul_add, add_smul] <;> ring
  let L : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) := { toFun := f, map_add' := h_add, map_smul' := h_smul }
  RealKVect.complexToRealK.map (ModuleCat.ofHom L)

/--
The F-matrix `F(τ,s) = [[τ,s],[s,-τ]]` as an isomorphism of `monodromyCarrier`
in `RealKVect`, given `τ²+τ=1`, `s²=τ`.  Diagonalizes the monodromy at generic `h`.
-/
noncomputable def Fmatrix_asRealK (τ s : ℂ) (hτ : τ ^ 2 + τ = 1) (hs : s ^ 2 = τ) :
    monodromyCarrier ≅ monodromyCarrier :=
  let fwd : monodromyCarrier ⟶ monodromyCarrier :=
    let f : ℂ × ℂ → ℂ × ℂ := fun (v : ℂ × ℂ) => (τ * v.1 + s * v.2, s * v.1 - τ * v.2)
    let L : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
      { toFun := f
        map_add' := by
          rintro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩; ext <;> dsimp [f] <;> ring
        map_smul' := by
          rintro z ⟨a,b⟩; ext <;> dsimp [f, smul_add, add_smul] <;> ring
      }
    RealKVect.complexToRealK.map (ModuleCat.ofHom L)
  have hF2 : τ ^ 2 + s ^ 2 = 1 := by
    calc
      τ ^ 2 + s ^ 2 = τ ^ 2 + τ := by rw [hs]
      _ = 1 := hτ
  have hF_sq_id (v : ℂ × ℂ) : (τ * (τ * v.1 + s * v.2) + s * (s * v.1 - τ * v.2),
                             s * (τ * v.1 + s * v.2) - τ * (s * v.1 - τ * v.2)) = v := by
    rcases v with ⟨a,b⟩
    have h1 : τ * (τ * a + s * b) + s * (s * a - τ * b) = a := by
      calc
        τ * (τ * a + s * b) + s * (s * a - τ * b) = (τ^2 + s^2) * a := by ring
        _ = 1 * a := by simp [hF2]
        _ = a := by simp
    have h2 : s * (τ * a + s * b) - τ * (s * a - τ * b) = b := by
      calc
        s * (τ * a + s * b) - τ * (s * a - τ * b) = (s^2 + τ^2) * b := by ring
        _ = (τ^2 + s^2) * b := by ring
        _ = 1 * b := by simp [hF2]
        _ = b := by simp
    ext <;> dsimp
    · simpa using h1
    · simpa using h2
  { hom := fwd
    inv := fwd
    hom_inv_id := by
      apply RealKVect.Hom.ext
      ext v
      exact hF_sq_id v
    inv_hom_id := by
      apply RealKVect.Hom.ext
      ext v
      exact hF_sq_id v }

end InfoGeometry.Quantum.RealKCategory
