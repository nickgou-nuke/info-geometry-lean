import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Quantum.RealKCategory

open CategoryTheory

universe u

namespace InfoGeometry.Quantum.RealMajoranaCategory

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

/-- Internal square-minus-one axis derived from `(J, eps)`. -/
noncomputable def K (X : RealMajoranaCore) : X →ₗ[ℝ] X :=
  X.J.comp X.eps

/-- The derived axis squares to `-Id`. -/
lemma K_sq (X : RealMajoranaCore) :
    X.K.comp X.K = -((LinearMap.id : X →ₗ[ℝ] X)) := by
  have hswap : X.eps.comp X.J = -(X.J.comp X.eps) := by
    have hneg : -(X.J.comp X.eps) = X.eps.comp X.J := by
      simpa using congrArg Neg.neg X.J_eps_anticomm
    simpa [eq_comm] using hneg
  unfold K
  calc
    (X.J.comp X.eps).comp (X.J.comp X.eps)
        = X.J.comp ((X.eps.comp X.J).comp X.eps) := by
            simp [LinearMap.comp_assoc]
    _ = X.J.comp ((-(X.J.comp X.eps)).comp X.eps) := by rw [hswap]
    _ = -((X.J.comp X.J).comp (X.eps.comp X.eps)) := by
          ext x
          simp [LinearMap.comp_assoc]
    _ = -((LinearMap.id : X →ₗ[ℝ] X)) := by
          simp [X.J_sq, X.eps_sq]

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

/-- Derived ladder-operator package, not primitive. -/
structure LadderPresentation (X : RealMajoranaCore) where
  create : X →ₗ[ℝ] X
  annihil : X →ₗ[ℝ] X
  split : create + annihil = (LinearMap.id : X →ₗ[ℝ] X)

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

/-- Object-level category: Majorana core + derived ladder presentation. -/
structure LadderMajorana where
  core : RealMajoranaCore
  ladder : LadderPresentation core

namespace LadderMajorana

/-- Morphisms preserve both core operators and derived ladder maps. -/
@[ext] structure Hom (X Y : LadderMajorana) where
  homCore : X.core ⟶ Y.core
  comm_create : homCore.hom.comp X.ladder.create = Y.ladder.create.comp homCore.hom
  comm_annihil : homCore.hom.comp X.ladder.annihil = Y.ladder.annihil.comp homCore.hom

noncomputable instance : Category LadderMajorana where
  Hom X Y := Hom X Y
  id X :=
    { homCore := 𝟙 X.core
      comm_create := by ext x <;> rfl
      comm_annihil := by ext x <;> rfl }
  comp {X Y Z} f g :=
    { homCore := f.homCore ≫ g.homCore
      comm_create := by
        calc
          ((f.homCore ≫ g.homCore).hom).comp X.ladder.create
              = (g.homCore.hom.comp f.homCore.hom).comp X.ladder.create := by rfl
          _ = g.homCore.hom.comp (f.homCore.hom.comp X.ladder.create) := by
                simp [LinearMap.comp_assoc]
          _ = g.homCore.hom.comp (Y.ladder.create.comp f.homCore.hom) := by
                rw [f.comm_create]
          _ = (g.homCore.hom.comp Y.ladder.create).comp f.homCore.hom := by
                simp [LinearMap.comp_assoc]
          _ = (Z.ladder.create.comp g.homCore.hom).comp f.homCore.hom := by
                rw [g.comm_create]
          _ = Z.ladder.create.comp (g.homCore.hom.comp f.homCore.hom) := by
                simp [LinearMap.comp_assoc]
          _ = Z.ladder.create.comp ((f.homCore ≫ g.homCore).hom) := by rfl
      comm_annihil := by
        calc
          ((f.homCore ≫ g.homCore).hom).comp X.ladder.annihil
              = (g.homCore.hom.comp f.homCore.hom).comp X.ladder.annihil := by rfl
          _ = g.homCore.hom.comp (f.homCore.hom.comp X.ladder.annihil) := by
                simp [LinearMap.comp_assoc]
          _ = g.homCore.hom.comp (Y.ladder.annihil.comp f.homCore.hom) := by
                rw [f.comm_annihil]
          _ = (g.homCore.hom.comp Y.ladder.annihil).comp f.homCore.hom := by
                simp [LinearMap.comp_assoc]
          _ = (Z.ladder.annihil.comp g.homCore.hom).comp f.homCore.hom := by
                rw [g.comm_annihil]
          _ = Z.ladder.annihil.comp (g.homCore.hom.comp f.homCore.hom) := by
                simp [LinearMap.comp_assoc]
          _ = Z.ladder.annihil.comp ((f.homCore ≫ g.homCore).hom) := by rfl }

@[simp] lemma hom_id (X : LadderMajorana) :
    ((𝟙 X : X ⟶ X).homCore.hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : LadderMajorana} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).homCore.hom) = g.homCore.hom.comp f.homCore.hom := rfl

/-- Forget derived ladder structure, keep only the core Majorana object. -/
noncomputable def forgetToCore : LadderMajorana ⥤ RealMajoranaCore where
  obj X := X.core
  map {X Y} f := f.homCore
  map_id X := by
    rfl
  map_comp f g := by
    rfl

/-- Forget ladder structure and then forget down to the `K`-only real category. -/
noncomputable def forgetToRealKVect :
    LadderMajorana ⥤ InfoGeometry.Quantum.RealKCategory.RealKVect :=
  forgetToCore ⋙ RealMajoranaCore.toRealKVect

end LadderMajorana

/-- Derived ladder object from a polarization choice. -/
noncomputable def ladderOfPolarization (X : PolarizedMajorana) : LadderMajorana where
  core := X.core
  ladder :=
    { create := X.polarization.Pplus
      annihil := X.polarization.Pminus
      split := X.polarization.sum_id }

/-- Categorical bridge: polarization choices induce ladder presentations. -/
noncomputable def polarizationToLadder : PolarizedMajorana ⥤ LadderMajorana where
  obj X := ladderOfPolarization X
  map {X Y} f :=
    { homCore := f.homCore
      comm_create := f.comm_Pplus
      comm_annihil := f.comm_Pminus }
  map_id X := by
    apply LadderMajorana.Hom.ext
    apply RealMajoranaCore.Hom.ext
    ext x
    rfl
  map_comp f g := by
    apply LadderMajorana.Hom.ext
    apply RealMajoranaCore.Hom.ext
    ext x
    rfl

/-- Forgetting to core commutes with the derived polarization-to-ladder functor. -/
theorem polarizationToLadder_forgetToCore_factors :
    polarizationToLadder ⋙ LadderMajorana.forgetToCore
      = PolarizedMajorana.forgetToCore := by
  rfl

/-- Forgetting to `RealKVect` commutes with the derived polarization-to-ladder functor. -/
theorem polarizationToLadder_forget_factors :
    polarizationToLadder ⋙ LadderMajorana.forgetToRealKVect
      = PolarizedMajorana.forgetToRealKVect := by
  rfl

/--
Compatibility datum tying a chosen polarization to two distinguished Majorana modes.
This is the bridge that turns the primitive Majorana CAR law into ladder CAR.
-/
structure PolarizedLadderRealization (X : PolarizedMajorana)
    (D : SplitCliffordDatum X.core) where
  uMinus : D.Mode
  uPlus : D.Mode
  annihil_eq :
    (polarizationToLadder.obj X).ladder.annihil = SplitCliffordDatum.majoranaField D uMinus
  create_eq :
    (polarizationToLadder.obj X).ladder.create = SplitCliffordDatum.majoranaField D uPlus
  minus_isotropic : SplitCliffordDatum.majoranaPairing D uMinus uMinus = 0
  plus_isotropic : SplitCliffordDatum.majoranaPairing D uPlus uPlus = 0
  mixed_half : SplitCliffordDatum.majoranaPairing D uMinus uPlus = (1 / 2 : ℝ)

/--
Derived ladder CAR theorem from primitive split-Clifford Majorana CAR and
polarization compatibility.
-/
theorem polarized_ladder_car_of_majorana
    (X : PolarizedMajorana)
    (hCliff : SplitCliffordDatum X.core)
    (hPol : PolarizedLadderRealization X hCliff) :
    CARWitness X.core
      ((polarizationToLadder.obj X).ladder.annihil)
      ((polarizationToLadder.obj X).ladder.create) := by
  rcases hPol with ⟨uMinus, uPlus, hAnn, hCreate, hMinusIso, hPlusIso, hMixed⟩
  have hMaj := SplitCliffordDatum.majorana_car_of_splitClifford (D := hCliff)
  constructor
  · rw [hAnn]
    simpa [hMinusIso] using hMaj uMinus uMinus
  constructor
  · rw [hCreate]
    simpa [hPlusIso] using hMaj uPlus uPlus
  · rw [hAnn, hCreate]
    have hScalar :
        (2 * SplitCliffordDatum.majoranaPairing hCliff uMinus uPlus : ℝ) = 1 := by
      rw [hMixed]
      norm_num
    calc
      anticommutator (SplitCliffordDatum.majoranaField hCliff uMinus)
          (SplitCliffordDatum.majoranaField hCliff uPlus)
          = (2 * SplitCliffordDatum.majoranaPairing hCliff uMinus uPlus)
              • (LinearMap.id : X.core →ₗ[ℝ] X.core) := by
                simpa using hMaj uMinus uPlus
      _ = (1 : ℝ) • (LinearMap.id : X.core →ₗ[ℝ] X.core) := by rw [hScalar]
      _ = (LinearMap.id : X.core →ₗ[ℝ] X.core) := by simp

end InfoGeometry.Quantum.RealMajoranaCategory
