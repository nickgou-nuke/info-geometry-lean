import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.Colimits
import InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity
import InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR
import InfoGeometry.OperatorAlgebra.InnerConjugation
import InfoGeometry.OperatorAlgebra.OperatorProjectiveRatio
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction

/-!
# Commutator transport to algebraic colimits

The finite-stage commutator identity is transported through the canonical
RingCat colimit injections.  This is purely categorical/algebraic: no
topological or analytic limit is introduced.
-/

namespace InfoGeometry.OperatorAlgebra

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type u} [Category.{u} J]
variable (F : J ⥤ RingCat.{u}) [HasColimit F]

theorem colimit_ι_map_quadraticCommutator
    (j : J) (x y : (F.obj j)) :
    (colimit.ι F j).hom (quadraticCommutator x y) =
      quadraticCommutator ((colimit.ι F j).hom x)
        ((colimit.ι F j).hom y) := by
  exact RingHom.map_quadraticCommutator (colimit.ι F j).hom x y

theorem colimit_ι_map_grandCanonicalOperator
    (j : J) (β H μ N μχ Q : F.obj j) :
    (colimit.ι F j).hom (grandCanonicalOperator β H μ N μχ Q) =
      grandCanonicalOperator
        ((colimit.ι F j).hom β)
        ((colimit.ι F j).hom H)
        ((colimit.ι F j).hom μ)
        ((colimit.ι F j).hom N)
        ((colimit.ι F j).hom μχ)
        ((colimit.ι F j).hom Q) := by
  exact InfoGeometry.OperatorAlgebra.RingHom.map_grandCanonicalOperator
    (colimit.ι F j).hom
    β H μ N μχ Q

theorem colimit_ι_map_thermalAnticommutator
    (j : J) (x y : (F.obj j)) :
    (colimit.ι F j).hom (thermalAnticommutator x y) =
      thermalAnticommutator ((colimit.ι F j).hom x)
        ((colimit.ι F j).hom y) := by
  exact thermalAnticommutator_map (colimit.ι F j).hom x y

theorem colimit_ι_map_innerConjugation
    (j : J) (u : (F.obj j)ˣ) (x : F.obj j) :
    (colimit.ι F j).hom (innerConjugation u x) =
      innerConjugation (Units.map (colimit.ι F j).hom u)
        ((colimit.ι F j).hom x) := by
  simp [innerConjugation]

theorem colimit_ι_map_innerConjugationNat
    (j : J) (u : (F.obj j)ˣ) (n : ℕ) (x : F.obj j) :
    (colimit.ι F j).hom (innerConjugationNat u n x) =
      innerConjugationNat (Units.map (colimit.ι F j).hom u) n
        ((colimit.ι F j).hom x) := by
  simp [innerConjugationNat, innerConjugation]

theorem colimit_ι_map_rightOperatorRatio
    (j : J) (x y : (F.obj j)ˣ) :
    (colimit.ι F j).hom (rightOperatorRatio x y) =
      rightOperatorRatio
        (Units.map (colimit.ι F j).hom x)
        (Units.map (colimit.ι F j).hom y) := by
  simp [rightOperatorRatio, Units.coe_map, Units.coe_map_inv]

theorem colimit_ι_map_operatorMobiusAction
    (j : J) (g : OperatorMatrix (F.obj j))
    (v : OperatorPair (F.obj j)) :
    (fun i => (colimit.ι F j).hom (operatorMobiusAction g v i)) =
      operatorMobiusAction
        (fun i k => (colimit.ι F j).hom (g i k))
        (fun i => (colimit.ι F j).hom (v i)) := by
  exact operatorMobiusAction_map (colimit.ι F j).hom g v

theorem colimit_ι_map_triZ2Parity
    (j : J) (gW gχ gN x : F.obj j)
    (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity
      ((colimit.ι F j).hom gW)
      ((colimit.ι F j).hom gχ)
      ((colimit.ι F j).hom gN)
      ((colimit.ι F j).hom x) εW εχ εN := by
  exact RingHom.map_triZ2Parity (colimit.ι F j).hom
    gW gχ gN x εW εχ εN hx

omit [HasColimit F] in
theorem limit_π_map_quadraticCommutator
    [HasLimit F] (j : J)
    (x y : ((limit F : RingCat.{u}) : Type u)) :
    (limit.π F j).hom (quadraticCommutator x y) =
      quadraticCommutator ((limit.π F j).hom x)
        ((limit.π F j).hom y) := by
      exact RingHom.map_quadraticCommutator (limit.π F j).hom x y

omit [HasColimit F] in
theorem limit_π_map_grandCanonicalOperator
    [HasLimit F] (j : J)
    (β H μ N μχ Q : ((limit F : RingCat.{u}) : Type u)) :
    (limit.π F j).hom (grandCanonicalOperator β H μ N μχ Q) =
      grandCanonicalOperator
        ((limit.π F j).hom β)
        ((limit.π F j).hom H)
        ((limit.π F j).hom μ)
        ((limit.π F j).hom N)
        ((limit.π F j).hom μχ)
        ((limit.π F j).hom Q) := by
  exact InfoGeometry.OperatorAlgebra.RingHom.map_grandCanonicalOperator
    (limit.π F j).hom
    β H μ N μχ Q

omit [HasColimit F] in
theorem limit_π_map_thermalAnticommutator
    [HasLimit F] (j : J)
    (x y : ((limit F : RingCat.{u}) : Type u)) :
    (limit.π F j).hom (thermalAnticommutator x y) =
      thermalAnticommutator ((limit.π F j).hom x)
        ((limit.π F j).hom y) := by
  exact thermalAnticommutator_map (limit.π F j).hom x y

omit [HasColimit F] in
theorem limit_π_map_innerConjugation
    [HasLimit F] (j : J)
    (u : (((limit F : RingCat.{u}) : Type u)ˣ))
    (x : ((limit F : RingCat.{u}) : Type u)) :
    (limit.π F j).hom (innerConjugation u x) =
      innerConjugation (Units.map (limit.π F j).hom u)
        ((limit.π F j).hom x) := by
  simp [innerConjugation]

omit [HasColimit F] in
theorem limit_π_map_innerConjugationNat
    [HasLimit F] (j : J)
    (u : (((limit F : RingCat.{u}) : Type u)ˣ)) (n : ℕ)
    (x : ((limit F : RingCat.{u}) : Type u)) :
    (limit.π F j).hom (innerConjugationNat u n x) =
      innerConjugationNat (Units.map (limit.π F j).hom u) n
        ((limit.π F j).hom x) := by
  simp [innerConjugationNat, innerConjugation]

omit [HasColimit F] in
theorem limit_π_map_rightOperatorRatio
    [HasLimit F] (j : J)
    (x y : (((limit F : RingCat.{u}) : Type u)ˣ)) :
    (limit.π F j).hom (rightOperatorRatio x y) =
      rightOperatorRatio
        (Units.map (limit.π F j).hom x)
        (Units.map (limit.π F j).hom y) := by
  simp [rightOperatorRatio, Units.coe_map, Units.coe_map_inv]

omit [HasColimit F] in
theorem limit_π_map_operatorMobiusAction
    [HasLimit F] (j : J)
    (g : OperatorMatrix ((limit F : RingCat.{u}) : Type u))
    (v : OperatorPair ((limit F : RingCat.{u}) : Type u)) :
    (fun i => (limit.π F j).hom (operatorMobiusAction g v i)) =
      operatorMobiusAction
        (fun i k => (limit.π F j).hom (g i k))
        (fun i => (limit.π F j).hom (v i)) := by
  exact operatorMobiusAction_map (limit.π F j).hom g v

omit [HasColimit F] in
theorem limit_π_map_triZ2Parity
    [HasLimit F] (j : J)
    (gW gχ gN x : ((limit F : RingCat.{u}) : Type u))
    (εW εχ εN : Fin 2)
    (hx : triZ2Parity gW gχ gN x εW εχ εN) :
    triZ2Parity
      ((limit.π F j).hom gW)
      ((limit.π F j).hom gχ)
      ((limit.π F j).hom gN)
      ((limit.π F j).hom x) εW εχ εN := by
  exact RingHom.map_triZ2Parity (limit.π F j).hom
    gW gχ gN x εW εχ εN hx

end InfoGeometry.OperatorAlgebra
