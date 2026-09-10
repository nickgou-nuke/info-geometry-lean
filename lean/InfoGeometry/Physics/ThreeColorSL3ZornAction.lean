import Mathlib
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Physics.QCDNativeZornColorRepresentation

/-!
# Conditional `SL₃` covariance of the three-colour Zorn carrier

The Zorn carrier is an explicit coordinate structure, not a bundled module
representation.  This owner records the external `SL₃` action on the colour
indices and the exact pairing/cross covariance hypotheses needed for
multiplicativity.  No claim is made that the action is automatic; the algebra
is conditional on the two covariance certificates.
-/

namespace InfoGeometry.Physics.ThreeColorSL3ZornAction

noncomputable section

open InfoGeometry.Physics.SplitOctonionBraidSU3

abbrev ColourVector := InfoGeometry.Physics.QCDNativeZornColorRepresentation.ColorLane
abbrev Zorn := SplitOctonionBraidSU3.Zorn

def colourFundamentalAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (u : ColourVector) : ColourVector :=
  (g : Matrix (Fin 3) (Fin 3) ℂ).mulVec u

@[simp] theorem colourFundamentalAction_one (u : ColourVector) :
    colourFundamentalAction 1 u = u := by
  ext i
  simp [colourFundamentalAction]

def colourFundamentalActionLinear
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : ColourVector →ₗ[ℂ] ColourVector where
  toFun := colourFundamentalAction g
  map_add' u v := by
    ext i
    simp [colourFundamentalAction, Matrix.mulVec_add]
  map_smul' c u := by
    ext i
    simp [colourFundamentalAction, Matrix.mulVec_smul]

def colourDualAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (v : ColourVector) : ColourVector :=
  ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
      Matrix (Fin 3) (Fin 3) ℂ).transpose.mulVec v

@[simp] theorem colourDualAction_one (v : ColourVector) :
    colourDualAction 1 v = v := by
  ext i
  simp [colourDualAction]

def colourDualActionLinear
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : ColourVector →ₗ[ℂ] ColourVector where
  toFun := colourDualAction g
  map_add' u v := by
    ext i
    simp [colourDualAction, Matrix.mulVec_add]
  map_smul' c u := by
    ext i
    simp [colourDualAction, Matrix.mulVec_smul]

theorem continuous_colourFundamentalAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (colourFundamentalAction g) := by
  simpa [colourFundamentalActionLinear] using
    (LinearMap.continuous_of_finiteDimensional
      (colourFundamentalActionLinear g))

theorem continuous_colourDualAction
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Continuous (colourDualAction g) := by
  simpa [colourDualActionLinear] using
    (LinearMap.continuous_of_finiteDimensional
      (colourDualActionLinear g))

def zornSL3Action
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (X : Zorn) : Zorn where
  a := X.a
  u := colourFundamentalAction g X.u
  v := colourDualAction g X.v
  b := X.b

@[simp] theorem zornSL3Action_one (X : Zorn) :
    zornSL3Action 1 X = X := by
  apply zorn_ext <;> simp [zornSL3Action]

@[simp] theorem zornSL3Action_a
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (X : Zorn) :
    (zornSL3Action g X).a = X.a := rfl

@[simp] theorem zornSL3Action_b
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (X : Zorn) :
    (zornSL3Action g X).b = X.b := rfl

def PreservesPairing
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : Prop :=
  ∀ u v, dot3 (colourFundamentalAction g u)
      (colourDualAction g v) = dot3 u v

def PreservesCrossFundamental
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : Prop :=
  ∀ u v, cross3 (colourFundamentalAction g u)
      (colourFundamentalAction g v) =
        colourDualAction g (cross3 u v)

def PreservesDualCross
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) : Prop :=
  ∀ u v, colourFundamentalAction g (cross3 u v) =
    cross3 (colourDualAction g u) (colourDualAction g v)

private theorem dot3_comm (u v : ColourVector) :
    dot3 u v = dot3 v u := by
  simp [dot3]
  ring

theorem zornSL3Action_mul_of_covariant
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hpair : PreservesPairing g)
    (hcross : PreservesCrossFundamental g)
    (hdualCross : PreservesDualCross g)
    (X Y : Zorn) :
    zornSL3Action g (zornMul X Y) =
      zornMul (zornSL3Action g X) (zornSL3Action g Y) := by
  apply SplitOctonionBraidSU3.zorn_ext
  · simpa [zornSL3Action, zornMul] using (hpair X.u Y.v).symm
  · funext i
    have hu :
        colourFundamentalAction g
            (X.a • Y.u + Y.b • X.u - cross3 X.v Y.v) =
          X.a • colourFundamentalAction g Y.u +
            Y.b • colourFundamentalAction g X.u -
              cross3 (colourDualAction g X.v)
                (colourDualAction g Y.v) := by
      simpa [colourFundamentalAction, colourDualAction, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_sub, smul_eq_mul, add_assoc,
        add_left_comm, add_comm] using hdualCross X.v Y.v
    exact congrFun hu i
  · funext i
    have hv :
        colourDualAction g
            (Y.a • X.v + X.b • Y.v + cross3 X.u Y.u) =
          Y.a • colourDualAction g X.v +
            X.b • colourDualAction g Y.v +
              cross3 (colourFundamentalAction g X.u)
                (colourFundamentalAction g Y.u) := by
      simpa [colourFundamentalAction, colourDualAction, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_sub, smul_eq_mul, add_assoc,
        add_left_comm, add_comm] using (hcross X.u Y.u).symm
    exact congrFun hv i
  · have hb :
        dot3 X.v Y.u = dot3 (colourDualAction g X.v)
          (colourFundamentalAction g Y.u) := by
      calc
        dot3 X.v Y.u = dot3 Y.u X.v := dot3_comm _ _
        _ = dot3 (colourFundamentalAction g Y.u)
            (colourDualAction g X.v) := (hpair Y.u X.v).symm
        _ = dot3 (colourDualAction g X.v)
            (colourFundamentalAction g Y.u) := dot3_comm _ _
    simp [zornSL3Action, zornMul, hb]

theorem zornSL3Action_preserves_norm_of_pairing
    (g : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hpair : PreservesPairing g) (X : Zorn) :
    zornNorm (zornSL3Action g X) = zornNorm X := by
  change X.a * X.b - dot3
      (colourFundamentalAction g X.u) (colourDualAction g X.v) =
    X.a * X.b - dot3 X.u X.v
  rw [hpair]

theorem zornSL3Action_comp
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    zornSL3Action g₂ ∘ zornSL3Action g₁ = zornSL3Action (g₂ * g₁) := by
  funext X
  apply zorn_ext
  · rfl
  · funext i
    simp [zornSL3Action, colourFundamentalAction, Matrix.mulVec_mulVec]
  · funext i
    simp [zornSL3Action, colourDualAction, Matrix.mulVec_mulVec,
      Matrix.transpose_mul]
  · rfl

end

end InfoGeometry.Physics.ThreeColorSL3ZornAction
