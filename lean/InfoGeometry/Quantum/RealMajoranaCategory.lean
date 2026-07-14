import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Clifford.Grading
import InfoGeometry.Krein.Representation
import InfoGeometry.Quantum.AnticommutingInvolutionCore
import InfoGeometry.Quantum.RealKCategory

open CategoryTheory

universe u

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace RealMajoranaCategory

/-- Primitive real Majorana core object: real module + involutive operator package. -/
structure RealMajoranaCore where
  V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module ℝ V]
  J : V →ₗ[ℝ] V
  eps : V →ₗ[ℝ] V
  Pi : V →ₗ[ℝ] V
  J_sq : J.comp J = (LinearMap.id : V →ₗ[ℝ] V)
  eps_sq : eps.comp eps = (LinearMap.id : V →ₗ[ℝ] V)
  Pi_sq : Pi.comp Pi = (LinearMap.id : V →ₗ[ℝ] V)
  J_eps_anticomm : J.comp eps = -(eps.comp J)

attribute [instance] RealMajoranaCore.instAddCommGroup RealMajoranaCore.instModule

instance : CoeSort RealMajoranaCore (Type u) := ⟨RealMajoranaCore.V⟩

namespace RealMajoranaCore

/-- Forget the extra Majorana data and retain only the anticommuting involution core. -/
noncomputable def toAnticommutingInvolutionCore (X : RealMajoranaCore) :
    InfoGeometry.Quantum.AnticommutingInvolutionCore :=
  { V := X
    J := X.J
    eps := X.eps
    J_sq := X.J_sq
    eps_sq := X.eps_sq
    J_eps_anticomm := X.J_eps_anticomm }

/-- Internal square-minus-one axis derived from `(J, eps)`. -/
noncomputable def K (X : RealMajoranaCore) : X →ₗ[ℝ] X :=
  X.toAnticommutingInvolutionCore.K

/-- The derived axis squares to `-Id`. -/
lemma K_sq (X : RealMajoranaCore) :
    X.K.comp X.K = -((LinearMap.id : X →ₗ[ℝ] X)) := by
  simpa [K, toAnticommutingInvolutionCore] using
    (InfoGeometry.Quantum.AnticommutingInvolutionCore.K_sq X.toAnticommutingInvolutionCore)

/-- Morphisms preserve all primitive operators `(J, eps, Pi)`. -/
@[ext] structure Hom (X Y : RealMajoranaCore) where
  hom : X →ₗ[ℝ] Y
  comm_J : hom.comp X.J = Y.J.comp hom
  comm_eps : hom.comp X.eps = Y.eps.comp hom
  comm_Pi : hom.comp X.Pi = Y.Pi.comp hom

instance (X Y : RealMajoranaCore) : CoeFun (Hom X Y) (fun _ => X → Y) := ⟨fun f => f.hom⟩

/-- Derived `K`-commutation from primitive `J` and `eps` commutation. -/
lemma Hom.comm_K {X Y : RealMajoranaCore} (f : Hom X Y) :
    f.hom.comp X.K = Y.K.comp f.hom := by
  unfold K
  calc
    f.hom.comp (X.J.comp X.eps)
        = (f.hom.comp X.J).comp X.eps := by simp [LinearMap.comp_assoc]
    _ = (Y.J.comp f.hom).comp X.eps := by rw [f.comm_J]
    _ = Y.J.comp (f.hom.comp X.eps) := by simp [LinearMap.comp_assoc]
    _ = Y.J.comp (Y.eps.comp f.hom) := by rw [f.comm_eps]
    _ = (Y.J.comp Y.eps).comp f.hom := by simp [LinearMap.comp_assoc]

noncomputable instance : Category RealMajoranaCore where
  Hom X Y := Hom X Y
  id X :=
    { hom := LinearMap.id
      comm_J := by ext x <;> rfl
      comm_eps := by ext x <;> rfl
      comm_Pi := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { hom := g.hom.comp f.hom
      comm_J := by
        calc
          (g.hom.comp f.hom).comp X.J
              = g.hom.comp (f.hom.comp X.J) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.J.comp f.hom) := by rw [f.comm_J]
          _ = (g.hom.comp Y.J).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.J.comp g.hom).comp f.hom := by rw [g.comm_J]
          _ = Z.J.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc]
      comm_eps := by
        calc
          (g.hom.comp f.hom).comp X.eps
              = g.hom.comp (f.hom.comp X.eps) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.eps.comp f.hom) := by rw [f.comm_eps]
          _ = (g.hom.comp Y.eps).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.eps.comp g.hom).comp f.hom := by rw [g.comm_eps]
          _ = Z.eps.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc]
      comm_Pi := by
        calc
          (g.hom.comp f.hom).comp X.Pi
              = g.hom.comp (f.hom.comp X.Pi) := by simp [LinearMap.comp_assoc]
          _ = g.hom.comp (Y.Pi.comp f.hom) := by rw [f.comm_Pi]
          _ = (g.hom.comp Y.Pi).comp f.hom := by simp [LinearMap.comp_assoc]
          _ = (Z.Pi.comp g.hom).comp f.hom := by rw [g.comm_Pi]
          _ = Z.Pi.comp (g.hom.comp f.hom) := by simp [LinearMap.comp_assoc] }

@[simp] lemma hom_id (X : RealMajoranaCore) : ((𝟙 X : X ⟶ X).hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : RealMajoranaCore} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).hom) = g.hom.comp f.hom := rfl

/-- Forgetful functor to the `K`-only category `RealKVect`. -/
noncomputable def toRealKVect :
    RealMajoranaCore ⥤ InfoGeometry.Quantum.RealKCategory.RealKVect where
  obj X :=
    { V := X
      K := X.K
      K_sq := by simpa using X.K_sq }
  map {X Y} f :=
    { hom := f.hom
      comm := f.comm_K }
  map_id X := by
    apply InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.ext
    ext x
    rfl
  map_comp f g := by
    apply InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.ext
    ext x
    rfl

end RealMajoranaCore

/-- Odd-odd channel on endomorphisms of `X`. -/
def anticommutator {X : RealMajoranaCore} (A B : X →ₗ[ℝ] X) : X →ₗ[ℝ] X :=
  A * B + B * A

/-- Standard single-mode CAR witness for an odd pair `(a, a†)`. -/
def CARWitness (X : RealMajoranaCore) (a adag : X →ₗ[ℝ] X) : Prop :=
  anticommutator a a = 0 ∧
    anticommutator adag adag = 0 ∧
    anticommutator a adag = (LinearMap.id : X →ₗ[ℝ] X)

/--
Primitive (two-sorted) Majorana CAR witness:
mode space `Mode`, state space `X`.
-/
def MajoranaCARWitness (X : RealMajoranaCore) {Mode : Type*}
    [AddCommGroup Mode] [Module ℝ Mode]
    (g : Mode → Mode → ℝ) (γ : Mode → X →ₗ[ℝ] X) : Prop :=
  ∀ u v : Mode,
    anticommutator (γ u) (γ v) = (2 * g u v) • (LinearMap.id : X →ₗ[ℝ] X)

/--
Split-Clifford datum on a real core object:
representation of `Cl(Q)` into endomorphisms of the core carrier.
-/
structure SplitCliffordDatum (X : RealMajoranaCore) where
  Mode : Type u
  [instAddCommGroupMode : AddCommGroup Mode]
  [instModuleMode : Module ℝ Mode]
  Q : QuadraticForm ℝ Mode
  rho : CliffordAlgebra Q →ₐ[ℝ] (X →ₗ[ℝ] X)

attribute [instance] SplitCliffordDatum.instAddCommGroupMode
  SplitCliffordDatum.instModuleMode

namespace SplitCliffordDatum

variable {X : RealMajoranaCore}
variable (D : SplitCliffordDatum X)

/-- Primitive Majorana field from Clifford generators. -/
noncomputable def majoranaField : D.Mode → X →ₗ[ℝ] X :=
  fun u => D.rho (CliffordAlgebra.ι D.Q u)

/--
Canonical bilinear pairing induced from the split quadratic form:
`g(u,v) = polar(Q)(u,v)/2`.
-/
noncomputable def majoranaPairing (u v : D.Mode) : ℝ :=
  (QuadraticMap.polar D.Q u v) / 2

/-- Raw Clifford anticommutator identity in the represented channel. -/
theorem majoranaField_anticommutator_eq_polar (u v : D.Mode) :
    anticommutator (majoranaField D u) (majoranaField D v)
      = (QuadraticMap.polar D.Q u v) • (LinearMap.id : X →ₗ[ℝ] X) := by
  unfold anticommutator majoranaField
  calc
    D.rho (CliffordAlgebra.ι D.Q u) * D.rho (CliffordAlgebra.ι D.Q v)
        + D.rho (CliffordAlgebra.ι D.Q v) * D.rho (CliffordAlgebra.ι D.Q u)
      = D.rho
          (CliffordAlgebra.ι D.Q u * CliffordAlgebra.ι D.Q v
            + CliffordAlgebra.ι D.Q v * CliffordAlgebra.ι D.Q u) := by
            simp [map_add, map_mul]
    _ = D.rho (algebraMap ℝ (CliffordAlgebra D.Q) (QuadraticMap.polar D.Q u v)) := by
          rw [CliffordAlgebra.ι_mul_ι_add_swap]
    _ = (QuadraticMap.polar D.Q u v) • (1 : X →ₗ[ℝ] X) := by
          simp [Algebra.algebraMap_eq_smul_one]
    _ = (QuadraticMap.polar D.Q u v) • (LinearMap.id : X →ₗ[ℝ] X) := by
          rfl

/--
Primitive constructive theorem:
the represented split-Clifford generators satisfy Majorana CAR.
-/
theorem majorana_car_of_splitClifford :
    MajoranaCARWitness X (majoranaPairing D) (majoranaField D) := by
  intro u v
  rw [majoranaField_anticommutator_eq_polar, majoranaPairing]
  have htwo : (2 : ℝ) * (QuadraticMap.polar D.Q u v / 2) = QuadraticMap.polar D.Q u v := by ring
  rw [htwo]

end SplitCliffordDatum

/-- Canonical `RealMajoranaCore` on doubled space with `(J, ε, Π) = (modular_j, spectral_epsilon, spectral_epsilon)`. -/
noncomputable def cl11DoubledCore (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : RealMajoranaCore where
  V := InfoGeometry.Krein.DoubledSpace E
  J := (InfoGeometry.Krein.modular_j (E := E)).toLinearMap
  eps := (InfoGeometry.Krein.spectral_epsilon (E := E)).toLinearMap
  Pi := (InfoGeometry.Krein.spectral_epsilon (E := E)).toLinearMap
  J_sq := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.modular_j_involution E)
  eps_sq := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.spectral_epsilon_involution E)
  Pi_sq := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.spectral_epsilon_involution E)
  J_eps_anticomm := by
    exact congrArg ContinuousLinearMap.toLinearMap
      (InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute E)

/-- `Cl(1,1)` representation with codomain in linear endomorphisms (forgetting continuity). -/
noncomputable def cl11RepLinear (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    CliffordAlgebra InfoGeometry.Clifford.splitQ11 →ₐ[ℝ]
      (InfoGeometry.Krein.DoubledSpace E →ₗ[ℝ] InfoGeometry.Krein.DoubledSpace E) where
  toFun a := (InfoGeometry.Krein.cl11Rep (E := E) a).toLinearMap
  map_one' := by
    exact congrArg ContinuousLinearMap.toLinearMap ((InfoGeometry.Krein.cl11Rep (E := E)).map_one)
  map_mul' a b := by
    exact congrArg ContinuousLinearMap.toLinearMap ((InfoGeometry.Krein.cl11Rep (E := E)).map_mul a b)
  map_zero' := by
    exact congrArg ContinuousLinearMap.toLinearMap ((InfoGeometry.Krein.cl11Rep (E := E)).map_zero)
  map_add' a b := by
    exact congrArg ContinuousLinearMap.toLinearMap ((InfoGeometry.Krein.cl11Rep (E := E)).map_add a b)
  commutes' r := by
    exact congrArg ContinuousLinearMap.toLinearMap ((InfoGeometry.Krein.cl11Rep (E := E)).commutes r)

/-- Concrete split `Cl(1,1)` representation datum on the doubled Majorana core. -/
noncomputable def cl11SplitCliffordDatum (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    SplitCliffordDatum (cl11DoubledCore E) where
  Mode := ℝ × ℝ
  Q := InfoGeometry.Clifford.splitQ11
  rho := cl11RepLinear E

/-- Primitive CAR theorem specialized to the concrete doubled-space split-`Cl(1,1)` datum. -/
theorem majorana_car_of_concrete_cl11 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    MajoranaCARWitness (cl11DoubledCore E)
      (SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E))
      (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E)) := by
  simpa using
    (SplitCliffordDatum.majorana_car_of_splitClifford
      (X := cl11DoubledCore E) (D := cl11SplitCliffordDatum E))

section Cl11NullModes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The `g = polar(Q)/2` pairing for concrete split-`Cl(1,1)` is `x₁y₁ - x₂y₂`. -/
lemma cl11_majoranaPairing_apply (u v : ℝ × ℝ) :
    SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E) u v
      = u.1 * v.1 - u.2 * v.2 := by
  unfold SplitCliffordDatum.majoranaPairing cl11SplitCliffordDatum
  simp [QuadraticMap.polar, InfoGeometry.Clifford.splitQ11_apply]
  ring_nf

/-- Canonical null mode `u_- = (1/2, 1/2)`. -/
noncomputable def cl11_uMinus : (cl11SplitCliffordDatum E).Mode := ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- Canonical null mode `u_+ = (1/2, -1/2)`. -/
noncomputable def cl11_uPlus : (cl11SplitCliffordDatum E).Mode := ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))

lemma cl11_uMinus_isotropic :
    SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E) (cl11_uMinus (E := E))
      (cl11_uMinus (E := E)) = 0 := by
  simp [cl11_uMinus, cl11_majoranaPairing_apply]

lemma cl11_uPlus_isotropic :
    SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))
      (cl11_uPlus (E := E)) = 0 := by
  simp [cl11_uPlus, cl11_majoranaPairing_apply]

lemma cl11_uMinus_uPlus_pairing_half :
    SplitCliffordDatum.majoranaPairing (cl11SplitCliffordDatum E) (cl11_uMinus (E := E))
      (cl11_uPlus (E := E)) = (1 / 2 : ℝ) := by
  simp [cl11_uMinus, cl11_uPlus, cl11_majoranaPairing_apply]
  ring

end Cl11NullModes

/-- Polarization data is extra structure on top of a real Majorana core object. -/
structure Polarization (X : RealMajoranaCore) where
  Pplus : X →ₗ[ℝ] X
  Pminus : X →ₗ[ℝ] X
  plus_idem : Pplus.comp Pplus = Pplus
  minus_idem : Pminus.comp Pminus = Pminus
  cross₁ : Pplus.comp Pminus = 0
  cross₂ : Pminus.comp Pplus = 0
  sum_id : Pplus + Pminus = (LinearMap.id : X →ₗ[ℝ] X)
  comm_Pi_plus : Pplus.comp X.Pi = X.Pi.comp Pplus
  comm_Pi_minus : Pminus.comp X.Pi = X.Pi.comp Pminus

namespace Polarization

variable {X : RealMajoranaCore}

/-- Involution associated to a split polarization (`Pplus - Pminus`). -/
noncomputable def involution (P0 : Polarization X) : X →ₗ[ℝ] X :=
  P0.Pplus - P0.Pminus

/-- The polarization involution commutes with parity `Pi`. -/
theorem involution_comm_Pi (P0 : Polarization X) :
    P0.involution.comp X.Pi = X.Pi.comp P0.involution := by
  calc
    (P0.Pplus - P0.Pminus).comp X.Pi
        = P0.Pplus.comp X.Pi - P0.Pminus.comp X.Pi := by simp [LinearMap.sub_comp]
    _ = X.Pi.comp P0.Pplus - X.Pi.comp P0.Pminus := by
          rw [P0.comm_Pi_plus, P0.comm_Pi_minus]
    _ = X.Pi.comp (P0.Pplus - P0.Pminus) := by simp [LinearMap.comp_sub]

/-- The involution associated to a split polarization squares to identity. -/
theorem involution_sq (P0 : Polarization X) :
    P0.involution.comp P0.involution = (LinearMap.id : X →ₗ[ℝ] X) := by
  ext x
  have hplus : P0.Pplus (P0.Pplus x) = P0.Pplus x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : X →ₗ[ℝ] X => F x) P0.plus_idem
  have hminus : P0.Pminus (P0.Pminus x) = P0.Pminus x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : X →ₗ[ℝ] X => F x) P0.minus_idem
  have hcross₁ : P0.Pplus (P0.Pminus x) = 0 := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : X →ₗ[ℝ] X => F x) P0.cross₁
  have hcross₂ : P0.Pminus (P0.Pplus x) = 0 := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun F : X →ₗ[ℝ] X => F x) P0.cross₂
  have hsum : P0.Pplus x + P0.Pminus x = x := by
    have h := congrArg (fun F : X →ₗ[ℝ] X => F x) P0.sum_id
    simpa [LinearMap.add_apply, add_assoc, add_left_comm, add_comm] using h
  calc
    (P0.involution.comp P0.involution) x
        = P0.Pplus (P0.Pplus x) - P0.Pplus (P0.Pminus x)
            - P0.Pminus (P0.Pplus x) + P0.Pminus (P0.Pminus x) := by
              simp [involution, LinearMap.comp_apply, sub_eq_add_neg,
                add_assoc, add_left_comm, add_comm]
    _ = P0.Pplus x + P0.Pminus x := by
          simp [hplus, hminus, hcross₁, hcross₂, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
    _ = x := hsum

private lemma half_smul_add_half_smul (y : X) :
    (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y) = (1 / 2 : ℝ) • y := by
  calc
    (1 / 2 : ℝ) • ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y)
        = (1 / 2 : ℝ) • (((1 / 2 : ℝ) + (1 / 2 : ℝ)) • y) := by
            simp [add_smul]
    _ = (1 / 2 : ℝ) • y := by norm_num

/-- Construct split polarization data from an involution. -/
noncomputable def ofInvolution
    (P : X →ₗ[ℝ] X)
    (P_sq : P.comp P = (LinearMap.id : X →ₗ[ℝ] X))
    (comm_Pi : P.comp X.Pi = X.Pi.comp P) :
    Polarization X where
  Pplus := (1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) + P)
  Pminus := (1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) - P)
  plus_idem := by
    ext x
    have hPP : P (P x) = x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) P_sq
    calc
      (((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) + P)).comp
          ((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) + P))) x
          = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x + P x) + (1 / 2 : ℝ) • (x + P x)) := by
              simp [LinearMap.comp_apply, hPP, smul_add,
                add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℝ) • (x + P x) := by
            simpa using half_smul_add_half_smul (X := X) (y := x + P x)
      _ = ((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) + P)) x := by
            simp
  minus_idem := by
    ext x
    have hPP : P (P x) = x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) P_sq
    calc
      (((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) - P)).comp
          ((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) - P))) x
          = (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (x - P x) + (1 / 2 : ℝ) • (x - P x)) := by
              simp [LinearMap.comp_apply, hPP, sub_eq_add_neg,
                smul_add, smul_sub, add_assoc, add_left_comm, add_comm]
      _ = (1 / 2 : ℝ) • (x - P x) := by
            simpa using half_smul_add_half_smul (X := X) (y := x - P x)
      _ = ((1 / 2 : ℝ) • ((LinearMap.id : X →ₗ[ℝ] X) - P)) x := by
            simp [sub_eq_add_neg, smul_sub]
  cross₁ := by
    ext x
    have hPP : P (P x) = x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) P_sq
    simp [sub_eq_add_neg, hPP, smul_add, smul_sub,
      add_assoc, add_left_comm, add_comm]
  cross₂ := by
    ext x
    have hPP : P (P x) = x := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) P_sq
    simp [sub_eq_add_neg, hPP, smul_add, smul_sub,
      add_assoc, add_left_comm, add_comm]
  sum_id := by
    have hhalf (x : X) : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = x := by
      calc
        (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x
            = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • x := by simp [add_smul]
        _ = x := by norm_num
    ext x
    simpa [sub_eq_add_neg, smul_add, smul_sub, add_assoc, add_left_comm, add_comm]
      using hhalf x
  comm_Pi_plus := by
    ext x
    have hcomm : P (X.Pi x) = X.Pi (P x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) comm_Pi
    simp [hcomm, smul_add]
  comm_Pi_minus := by
    ext x
    have hcomm : P (X.Pi x) = X.Pi (P x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun F : X →ₗ[ℝ] X => F x) comm_Pi
    simp [hcomm, smul_add, smul_sub, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]

/-- Round-trip (`involution -> split -> involution`) recovers the input involution. -/
theorem involution_ofInvolution
    (P : X →ₗ[ℝ] X)
    (P_sq : P.comp P = (LinearMap.id : X →ₗ[ℝ] X))
    (comm_Pi : P.comp X.Pi = X.Pi.comp P) :
    (ofInvolution (X := X) P P_sq comm_Pi).involution = P := by
  have hhalf (y : X) : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y = y := by
    calc
      (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y
          = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • y := by simp [add_smul]
      _ = y := by norm_num
  ext x
  simpa [involution, ofInvolution, sub_eq_add_neg, smul_add, smul_sub,
    add_assoc, add_left_comm, add_comm] using hhalf (P x)

/-- Round-trip (`split -> involution -> split`) recovers `Pplus`. -/
theorem ofInvolution_involution_Pplus (P0 : Polarization X) :
    (ofInvolution (X := X) P0.involution P0.involution_sq P0.involution_comm_Pi).Pplus
      = P0.Pplus := by
  ext x
  have hsum : P0.Pplus x + P0.Pminus x = x := by
    have h := congrArg (fun F : X →ₗ[ℝ] X => F x) P0.sum_id
    simpa [LinearMap.add_apply, add_assoc, add_left_comm, add_comm] using h
  have hInv : P0.involution x = P0.Pplus x - P0.Pminus x := by
    simp [involution]
  calc
    ((ofInvolution (X := X) P0.involution P0.involution_sq P0.involution_comm_Pi).Pplus) x
        = (1 / 2 : ℝ) • (x + P0.involution x) := by
            simp [ofInvolution]
    _ = (1 / 2 : ℝ) • (x + (P0.Pplus x - P0.Pminus x)) := by rw [hInv]
    _ = (1 / 2 : ℝ) • ((P0.Pplus x + P0.Pminus x) + (P0.Pplus x - P0.Pminus x)) := by
        nth_rewrite 1 [← hsum]
        rfl
    _ = (1 / 2 : ℝ) • (P0.Pplus x + P0.Pplus x) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = P0.Pplus x := by
          calc
            (1 / 2 : ℝ) • (P0.Pplus x + P0.Pplus x)
                = (1 / 2 : ℝ) • ((2 : ℝ) • P0.Pplus x) := by simp [two_smul]
            _ = P0.Pplus x := by
                  norm_num [smul_smul]

/-- Round-trip (`split -> involution -> split`) recovers `Pminus`. -/
theorem ofInvolution_involution_Pminus (P0 : Polarization X) :
    (ofInvolution (X := X) P0.involution P0.involution_sq P0.involution_comm_Pi).Pminus
      = P0.Pminus := by
  ext x
  have hsum : P0.Pplus x + P0.Pminus x = x := by
    have h := congrArg (fun F : X →ₗ[ℝ] X => F x) P0.sum_id
    simpa [LinearMap.add_apply, add_assoc, add_left_comm, add_comm] using h
  have hInv : P0.involution x = P0.Pplus x - P0.Pminus x := by
    simp [involution]
  calc
    ((ofInvolution (X := X) P0.involution P0.involution_sq P0.involution_comm_Pi).Pminus) x
        = (1 / 2 : ℝ) • (x - P0.involution x) := by
            simp [ofInvolution]
    _ = (1 / 2 : ℝ) • (x - (P0.Pplus x - P0.Pminus x)) := by rw [hInv]
    _ = (1 / 2 : ℝ) • ((P0.Pplus x + P0.Pminus x) - (P0.Pplus x - P0.Pminus x)) := by
        nth_rewrite 1 [← hsum]
        rfl
    _ = (1 / 2 : ℝ) • (P0.Pminus x + P0.Pminus x) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = P0.Pminus x := by
          calc
            (1 / 2 : ℝ) • (P0.Pminus x + P0.Pminus x)
                = (1 / 2 : ℝ) • ((2 : ℝ) • P0.Pminus x) := by simp [two_smul]
            _ = P0.Pminus x := by
                  norm_num [smul_smul]

end Polarization

section Cl11Polarization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] lemma spectralPlusProj_apply_to_doubled (x y : E) :
    InfoGeometry.Krein.spectralPlusProj (E := E) (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled x (0 : E) := by
  have hhalf (z : E) : ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z = z := by
    calc
      ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z
          = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z := by
              simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) z).symm
      _ = z := by norm_num
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [InfoGeometry.Krein.spectralPlusProj, InfoGeometry.Krein.to_doubled,
      InfoGeometry.Krein.spectral_epsilon_apply, hhalf]

@[simp] lemma spectralMinusProj_apply_to_doubled (x y : E) :
    InfoGeometry.Krein.spectralMinusProj (E := E) (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled (0 : E) y := by
  have hhalf (z : E) : ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z = z := by
    calc
      ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z
          = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z := by
              simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) z).symm
      _ = z := by norm_num
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [InfoGeometry.Krein.spectralMinusProj, InfoGeometry.Krein.to_doubled,
      InfoGeometry.Krein.spectral_epsilon_apply, hhalf]

lemma spectralPlusProj_comp_spectralMinusProj :
    (InfoGeometry.Krein.spectralPlusProj (E := E)).comp (InfoGeometry.Krein.spectralMinusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply]

lemma spectralMinusProj_comp_spectralPlusProj :
    (InfoGeometry.Krein.spectralMinusProj (E := E)).comp (InfoGeometry.Krein.spectralPlusProj (E := E)) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply]

lemma spectralPlusProj_comm_Pi :
    (InfoGeometry.Krein.spectralPlusProj (E := E)).comp (InfoGeometry.Krein.spectral_epsilon (E := E))
      = (InfoGeometry.Krein.spectral_epsilon (E := E)).comp (InfoGeometry.Krein.spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply]

lemma spectralMinusProj_comm_Pi :
    (InfoGeometry.Krein.spectralMinusProj (E := E)).comp (InfoGeometry.Krein.spectral_epsilon (E := E))
      = (InfoGeometry.Krein.spectral_epsilon (E := E)).comp (InfoGeometry.Krein.spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
    apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
  rw [← hv]
  apply InfoGeometry.Krein.DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply]

/-- Canonical spectral polarization on the concrete doubled-space `Cl(1,1)` core. -/
noncomputable def cl11CanonicalPolarization : Polarization (cl11DoubledCore E) where
  Pplus := (InfoGeometry.Krein.spectralPlusProj (E := E)).toLinearMap
  Pminus := (InfoGeometry.Krein.spectralMinusProj (E := E)).toLinearMap
  plus_idem := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.spectralPlusProj_idempotent (E := E))
  minus_idem := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.spectralMinusProj_idempotent (E := E))
  cross₁ := by
    exact congrArg ContinuousLinearMap.toLinearMap (spectralPlusProj_comp_spectralMinusProj (E := E))
  cross₂ := by
    exact congrArg ContinuousLinearMap.toLinearMap (spectralMinusProj_comp_spectralPlusProj (E := E))
  sum_id := by
    exact congrArg ContinuousLinearMap.toLinearMap (InfoGeometry.Krein.spectralProj_sum (E := E))
  comm_Pi_plus := by
    exact congrArg ContinuousLinearMap.toLinearMap (spectralPlusProj_comm_Pi (E := E))
  comm_Pi_minus := by
    exact congrArg ContinuousLinearMap.toLinearMap (spectralMinusProj_comm_Pi (E := E))

@[simp] lemma cl11_majoranaField_uMinus_apply_to_doubled (x y : E) :
    SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uMinus (E := E))
      (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled (0 : E) x := by
  have hhalf (z : E) :
      ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  change (InfoGeometry.Krein.cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (cl11_uMinus (E := E)))
      (InfoGeometry.Krein.to_doubled x y))
    = InfoGeometry.Krein.to_doubled (0 : E) x
  rw [InfoGeometry.Krein.cl11Rep_ι_apply]
  calc
    (InfoGeometry.Krein.cl11RepLin (E := E) ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled (0 : E) ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • x) := by
          simpa [cl11_uMinus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
              (E := E) ((1 / 2 : ℝ)) ((1 / 2 : ℝ)) x y)
    _ = InfoGeometry.Krein.to_doubled (0 : E) x := by
          simpa [hhalf]

@[simp] lemma cl11_majoranaField_uPlus_apply_to_doubled (x y : E) :
    SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))
      (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled y (0 : E) := by
  have hhalf (z : E) :
      ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z) = z := by
    have hscalar : (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) = 1 := by norm_num
    simpa [hscalar]
  change (InfoGeometry.Krein.cl11Rep (E := E)
      (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (cl11_uPlus (E := E)))
      (InfoGeometry.Krein.to_doubled x y))
    = InfoGeometry.Krein.to_doubled y (0 : E)
  rw [InfoGeometry.Krein.cl11Rep_ι_apply]
  calc
    (InfoGeometry.Krein.cl11RepLin (E := E) ((1 / 2 : ℝ), (-(1 / 2 : ℝ))))
        (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.to_doubled ((((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • y) (0 : E) := by
          simpa [cl11_uPlus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (InfoGeometry.Krein.cl11RepLin_apply_to_doubled
              (E := E) ((1 / 2 : ℝ)) (-(1 / 2 : ℝ)) x y)
    _ = InfoGeometry.Krein.to_doubled y (0 : E) := by
          simpa [hhalf]

@[simp] lemma cl11_majoranaField_uPlus_add_uMinus_apply_to_doubled (x y : E) :
    (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))
        + SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uMinus (E := E)))
      (InfoGeometry.Krein.to_doubled x y)
      = InfoGeometry.Krein.modular_j (E := E) (InfoGeometry.Krein.to_doubled x y) := by
  calc
    (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))
        + SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uMinus (E := E)))
      (InfoGeometry.Krein.to_doubled x y)
        = InfoGeometry.Krein.to_doubled y (0 : E) +
            InfoGeometry.Krein.to_doubled (0 : E) x := by
              simp [LinearMap.add_apply, cl11_majoranaField_uPlus_apply_to_doubled,
                cl11_majoranaField_uMinus_apply_to_doubled]
    _ = InfoGeometry.Krein.to_doubled y x := by
          simpa [InfoGeometry.Krein.to_doubled, Prod.mk_add_mk, WithLp.add_fst, WithLp.add_snd]
            using
              (WithLp.toLp_add (p := (2 : ENNReal))
                (x := (y, (0 : E))) (y := ((0 : E), x))).symm
    _ = InfoGeometry.Krein.modular_j (E := E) (InfoGeometry.Krein.to_doubled x y) := by
          simp [InfoGeometry.Krein.modular_j_to_doubled]

end Cl11Polarization

/-- CAR ladder package: nilpotent ladders with mixed anticommutator identity. -/
structure LadderPresentation (X : RealMajoranaCore) where
  create : X →ₗ[ℝ] X
  annihil : X →ₗ[ℝ] X
  create_sq : anticommutator create create = 0
  annihil_sq : anticommutator annihil annihil = 0
  mixed : anticommutator annihil create = (LinearMap.id : X →ₗ[ℝ] X)

/-- Object-level category: Majorana core + chosen polarization. -/
structure PolarizedMajorana where
  core : RealMajoranaCore
  polarization : Polarization core

namespace PolarizedMajorana

/-- Morphisms preserve both core operators and polarization projectors. -/
@[ext] structure Hom (X Y : PolarizedMajorana) where
  homCore : X.core ⟶ Y.core
  comm_Pplus : homCore.hom.comp X.polarization.Pplus = Y.polarization.Pplus.comp homCore.hom
  comm_Pminus : homCore.hom.comp X.polarization.Pminus = Y.polarization.Pminus.comp homCore.hom

noncomputable instance : Category PolarizedMajorana where
  Hom X Y := Hom X Y
  id X :=
    { homCore := 𝟙 X.core
      comm_Pplus := by ext x <;> rfl
      comm_Pminus := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { homCore := f.homCore ≫ g.homCore
      comm_Pplus := by
        calc
          ((f.homCore ≫ g.homCore).hom).comp X.polarization.Pplus
              = (g.homCore.hom.comp f.homCore.hom).comp X.polarization.Pplus := by rfl
          _ = g.homCore.hom.comp (f.homCore.hom.comp X.polarization.Pplus) := by
                simp [LinearMap.comp_assoc]
          _ = g.homCore.hom.comp (Y.polarization.Pplus.comp f.homCore.hom) := by
                rw [f.comm_Pplus]
          _ = (g.homCore.hom.comp Y.polarization.Pplus).comp f.homCore.hom := by
                simp [LinearMap.comp_assoc]
          _ = (Z.polarization.Pplus.comp g.homCore.hom).comp f.homCore.hom := by
                rw [g.comm_Pplus]
          _ = Z.polarization.Pplus.comp (g.homCore.hom.comp f.homCore.hom) := by
                simp [LinearMap.comp_assoc]
          _ = Z.polarization.Pplus.comp ((f.homCore ≫ g.homCore).hom) := by rfl
      comm_Pminus := by
        calc
          ((f.homCore ≫ g.homCore).hom).comp X.polarization.Pminus
              = (g.homCore.hom.comp f.homCore.hom).comp X.polarization.Pminus := by rfl
          _ = g.homCore.hom.comp (f.homCore.hom.comp X.polarization.Pminus) := by
                simp [LinearMap.comp_assoc]
          _ = g.homCore.hom.comp (Y.polarization.Pminus.comp f.homCore.hom) := by
                rw [f.comm_Pminus]
          _ = (g.homCore.hom.comp Y.polarization.Pminus).comp f.homCore.hom := by
                simp [LinearMap.comp_assoc]
          _ = (Z.polarization.Pminus.comp g.homCore.hom).comp f.homCore.hom := by
                rw [g.comm_Pminus]
          _ = Z.polarization.Pminus.comp (g.homCore.hom.comp f.homCore.hom) := by
                simp [LinearMap.comp_assoc]
          _ = Z.polarization.Pminus.comp ((f.homCore ≫ g.homCore).hom) := by rfl }

@[simp] lemma hom_id (X : PolarizedMajorana) :
    ((𝟙 X : X ⟶ X).homCore.hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : PolarizedMajorana} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).homCore.hom) = g.homCore.hom.comp f.homCore.hom := rfl

/-- Forget polarization structure, keep only the core Majorana object. -/
noncomputable def forgetToCore : PolarizedMajorana ⥤ RealMajoranaCore where
  obj X := X.core
  map {X Y} f := f.homCore
  map_id X := by
    rfl
  map_comp f g := by
    rfl

/-- Forget polarization and then forget down to the `K`-only real category. -/
noncomputable def forgetToRealKVect :
    PolarizedMajorana ⥤ InfoGeometry.Quantum.RealKCategory.RealKVect :=
  forgetToCore ⋙ RealMajoranaCore.toRealKVect

end PolarizedMajorana

/-- Object-level bundle: core Majorana object plus a CAR ladder presentation. -/
structure LadderMajorana where
  core : RealMajoranaCore
  ladder : LadderPresentation core

/--
Compatibility datum tying a chosen polarization to two distinguished Majorana modes.
This is the bridge that turns the primitive Majorana CAR law into ladder CAR.
-/
structure PolarizedLadderRealization (X : PolarizedMajorana)
    (D : SplitCliffordDatum X.core) where
  uMinus : D.Mode
  uPlus : D.Mode
  minus_isotropic : SplitCliffordDatum.majoranaPairing D uMinus uMinus = 0
  plus_isotropic : SplitCliffordDatum.majoranaPairing D uPlus uPlus = 0
  mixed_half : SplitCliffordDatum.majoranaPairing D uMinus uPlus = (1 / 2 : ℝ)
  compatible_plus :
    X.polarization.Pplus
      = (SplitCliffordDatum.majoranaField D uPlus).comp
          (SplitCliffordDatum.majoranaField D uMinus)
  compatible_minus :
    X.polarization.Pminus
      = (SplitCliffordDatum.majoranaField D uMinus).comp
          (SplitCliffordDatum.majoranaField D uPlus)

/-- Build a CAR ladder presentation from polarized null modes in a split-Clifford realization. -/
noncomputable def ladderOfRealization
    (X : PolarizedMajorana) (D : SplitCliffordDatum X.core)
    (hPol : PolarizedLadderRealization X D) :
    LadderPresentation X.core := by
  refine
    { create := SplitCliffordDatum.majoranaField D hPol.uPlus
      annihil := SplitCliffordDatum.majoranaField D hPol.uMinus
      create_sq := ?_
      annihil_sq := ?_
      mixed := ?_ }
  · have hMaj := SplitCliffordDatum.majorana_car_of_splitClifford (D := D)
    simpa [hPol.plus_isotropic] using hMaj hPol.uPlus hPol.uPlus
  · have hMaj := SplitCliffordDatum.majorana_car_of_splitClifford (D := D)
    simpa [hPol.minus_isotropic] using hMaj hPol.uMinus hPol.uMinus
  · have hMaj := SplitCliffordDatum.majorana_car_of_splitClifford (D := D)
    have hScalar : (2 * SplitCliffordDatum.majoranaPairing D hPol.uMinus hPol.uPlus : ℝ) = 1 := by
      rw [hPol.mixed_half]
      norm_num
    calc
      anticommutator (SplitCliffordDatum.majoranaField D hPol.uMinus)
          (SplitCliffordDatum.majoranaField D hPol.uPlus)
          = (2 * SplitCliffordDatum.majoranaPairing D hPol.uMinus hPol.uPlus)
              • (LinearMap.id : X.core →ₗ[ℝ] X.core) := by
                simpa using hMaj hPol.uMinus hPol.uPlus
      _ = (1 : ℝ) • (LinearMap.id : X.core →ₗ[ℝ] X.core) := by rw [hScalar]
      _ = (LinearMap.id : X.core →ₗ[ℝ] X.core) := by simp

/-- Bundle the derived CAR ladder with the same underlying core object. -/
noncomputable def ladderMajoranaOfRealization
    (X : PolarizedMajorana) (D : SplitCliffordDatum X.core)
    (hPol : PolarizedLadderRealization X D) : LadderMajorana where
  core := X.core
  ladder := ladderOfRealization X D hPol

/--
Derived ladder CAR theorem from primitive split-Clifford Majorana CAR and
polarized null-mode compatibility.
-/
theorem polarized_ladder_car_of_majorana
    (X : PolarizedMajorana)
    (hCliff : SplitCliffordDatum X.core)
    (hPol : PolarizedLadderRealization X hCliff) :
    CARWitness X.core
      (ladderOfRealization X hCliff hPol).annihil
      (ladderOfRealization X hCliff hPol).create := by
  exact ⟨(ladderOfRealization X hCliff hPol).annihil_sq,
    (ladderOfRealization X hCliff hPol).create_sq,
    (ladderOfRealization X hCliff hPol).mixed⟩

section Cl11ConcreteRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Canonical polarized object on the concrete doubled-space `Cl(1,1)` core. -/
noncomputable def cl11CanonicalPolarizedMajorana : PolarizedMajorana where
  core := cl11DoubledCore E
  polarization := cl11CanonicalPolarization (E := E)

/-- Concrete `Cl(1,1)` null modes realize ladders compatible with canonical spectral polarization. -/
noncomputable def cl11_concrete_ladder_realization :
    PolarizedLadderRealization (cl11CanonicalPolarizedMajorana (E := E))
      (cl11SplitCliffordDatum E) := by
  refine
    { uMinus := cl11_uMinus (E := E)
      uPlus := cl11_uPlus (E := E)
      minus_isotropic := cl11_uMinus_isotropic (E := E)
      plus_isotropic := cl11_uPlus_isotropic (E := E)
      mixed_half := cl11_uMinus_uPlus_pairing_half (E := E)
      compatible_plus := ?_
      compatible_minus := ?_ }
  · ext v
    have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
      apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
    rw [← hv]
    have hL :
        (cl11CanonicalPolarizedMajorana (E := E)).polarization.Pplus
            (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
          = InfoGeometry.Krein.to_doubled (WithLp.fst v) (0 : E) := by
      unfold cl11CanonicalPolarizedMajorana cl11CanonicalPolarization
      change (InfoGeometry.Krein.spectralPlusProj (E := E))
          (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
        = InfoGeometry.Krein.to_doubled (WithLp.fst v) (0 : E)
      exact spectralPlusProj_apply_to_doubled (E := E) (x := WithLp.fst v) (y := WithLp.snd v)
    have hR :
        ((SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))).comp
            (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uMinus (E := E))))
          (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
          = InfoGeometry.Krein.to_doubled (WithLp.fst v) (0 : E) := by
      simp [LinearMap.comp_apply]
    exact hL.trans hR.symm
  · ext v
    have hv : InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v) = v := by
      apply InfoGeometry.Krein.DoubledSpace.ext <;> simp [InfoGeometry.Krein.to_doubled]
    rw [← hv]
    have hL :
        (cl11CanonicalPolarizedMajorana (E := E)).polarization.Pminus
            (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
          = InfoGeometry.Krein.to_doubled (0 : E) (WithLp.snd v) := by
      unfold cl11CanonicalPolarizedMajorana cl11CanonicalPolarization
      change (InfoGeometry.Krein.spectralMinusProj (E := E))
          (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
        = InfoGeometry.Krein.to_doubled (0 : E) (WithLp.snd v)
      exact spectralMinusProj_apply_to_doubled (E := E) (x := WithLp.fst v) (y := WithLp.snd v)
    have hR :
        ((SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uMinus (E := E))).comp
            (SplitCliffordDatum.majoranaField (cl11SplitCliffordDatum E) (cl11_uPlus (E := E))))
          (InfoGeometry.Krein.to_doubled (WithLp.fst v) (WithLp.snd v))
          = InfoGeometry.Krein.to_doubled (0 : E) (WithLp.snd v) := by
      simp [LinearMap.comp_apply]
    exact hL.trans hR.symm

/-- Final concrete CAR theorem: canonical spectral polarization + concrete split-`Cl(1,1)` datum. -/
theorem car_realization_of_clifford_concrete :
    CARWitness (cl11CanonicalPolarizedMajorana (E := E)).core
      (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := E))
        (cl11SplitCliffordDatum E) (cl11_concrete_ladder_realization (E := E))).annihil
      (ladderOfRealization (cl11CanonicalPolarizedMajorana (E := E))
        (cl11SplitCliffordDatum E) (cl11_concrete_ladder_realization (E := E))).create := by
  exact polarized_ladder_car_of_majorana
    (X := cl11CanonicalPolarizedMajorana (E := E))
    (hCliff := cl11SplitCliffordDatum E)
    (hPol := cl11_concrete_ladder_realization (E := E))

end Cl11ConcreteRealization

end RealMajoranaCategory
