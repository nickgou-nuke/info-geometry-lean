import Mathlib
import InfoGeometry.Physics.MDPASJMSouriau
import InfoGeometry.Physics.MDPASJMSouriauDigest

/-!
# MDPAS/J.-M. Souriau: obstruction, symplectic, KK and quantization finite layer

This file is theorem-safe.  It formalizes finite algebraic shadows of the
remaining global story requested from Souriau's spin-particle paper:

* a cellular `S²` de Rham obstruction: the area 2-cochain is closed but not exact;
* a genuine finite symplectic carrier over `ℚ²`, with skewness and nondegeneracy;
* a finite 5D Kaluza--Klein split identity for the `(4+1)` quadratic form;
* a dependent prequantization/integrality readout, reusing the spin-half theorem;
* a named readback of the existing MDPAS finite-stage direct-limit theorem.

It does not claim smooth de Rham theory, global manifold construction, C*- or
Hilbert-space quantization, or the full Dirac equation.  Those analytic/global
objects require owner files with the relevant hypotheses.
-/

namespace InfoGeometry
namespace Physics
namespace MDPASJMSouriauGlobalObstruction

open InfoGeometry.Physics.MDPASJMSouriau
open InfoGeometry.Physics.MDPASJMSouriauDigest
open InfoGeometry.Topology.ThermodynamicGauge

/-! ## 1. Cellular de Rham obstruction for the sphere -/

/-- Cellular cochains for the minimal CW model of `S²`: one 0-cell, no 1-cells, one 2-cell. -/
abbrev C0 := Fin 1 → ℚ
abbrev C1 := Fin 0 → ℚ
abbrev C2 := Fin 1 → ℚ

/-- The cellular differential `C¹ → C²`; zero because the model has no 1-cells. -/
def d1 (_α : C1) : C2 := 0

/-- The normalized area 2-cochain. -/
def sphereArea : C2 := fun _ => 1

def Closed2 (ω : C2) : Prop := ω = ω

def Exact2 (ω : C2) : Prop := ∃ α : C1, d1 α = ω

theorem sphereArea_closed : Closed2 sphereArea := rfl

/-- The area class on the cellular `S²` model is not exact. -/
theorem sphereArea_not_exact : ¬ Exact2 sphereArea := by
  intro h
  rcases h with ⟨α, hα⟩
  have h0 : d1 α 0 = 0 := by simp [d1]
  have h1 : sphereArea 0 = 1 := rfl
  have : (0 : ℚ) = 1 := by simpa [h0, h1] using congrArg (fun f : C2 => f 0) hα
  norm_num at this

/-! ## 2. Genuine finite symplectic carrier -/

abbrev V2 := Fin 2 → ℚ

def e0 : V2 := fun i => if i = 0 then 1 else 0
def e1 : V2 := fun i => if i = 1 then 1 else 0

/-- Standard symplectic form on `ℚ²`. -/
def omega2 (v w : V2) : ℚ := v 0 * w 1 - v 1 * w 0

structure FiniteSymplecticCarrier where
  Carrier : Type
  zero : Carrier
  omega : Carrier → Carrier → ℚ
  skew : ∀ x y, omega x y = - omega y x
  nondegenerate : ∀ x, (∀ y, omega x y = 0) → x = zero

theorem omega2_skew (v w : V2) : omega2 v w = - omega2 w v := by
  simp [omega2]
  ring

theorem omega2_nondegenerate (v : V2) (h : ∀ w : V2, omega2 v w = 0) : v = 0 := by
  ext i
  fin_cases i
  · have h1 := h e1
    simp [omega2, e1] at h1
    exact h1
  · have h0 := h e0
    simp [omega2, e0] at h0
    simpa using h0

def finiteSymplecticPlane : FiniteSymplecticCarrier where
  Carrier := V2
  zero := 0
  omega := omega2
  skew := omega2_skew
  nondegenerate := omega2_nondegenerate

/-! ## 3. Finite 5D Kaluza--Klein split -/

abbrev Vec5 := Fin 5 → ℚ

def fourPart (x : Vec5) : Vec4 := fun i => x ⟨i.val, by omega⟩

def fifthPart (x : Vec5) : ℚ := x 4

def kk5Quadratic (x : Vec5) : ℚ :=
  x 0 * x 0 - x 1 * x 1 - x 2 * x 2 - x 3 * x 3 - x 4 * x 4

def kkNull (x : Vec5) : Prop := kk5Quadratic x = 0

theorem kk5_split (x : Vec5) :
    kk5Quadratic x = minkowskiDot (fourPart x) (fourPart x) - fifthPart x ^ 2 := by
  simp [kk5Quadratic, minkowskiDot, fourPart, fifthPart]
  ring

/-- A null 5D vector projects to a 4D mass-shell with mass equal to fifth momentum. -/
theorem kk5_null_implies_four_mass_shell (x : Vec5) (hx : kkNull x) :
    minkowskiDot (fourPart x) (fourPart x) = fifthPart x ^ 2 := by
  have hsplit := kk5_split x
  unfold kkNull at hx
  linarith

/-! ## 4. Prequantization/integrality readout -/

def PrequantizationIntegral (s h : ℚ) : Prop := SpinPrequantized s h

theorem spin_half_integral_prequantization (h : ℚ) :
    PrequantizationIntegral (h / 2) h :=
  spin_half_prequantized h

/-! ## 5. Direct-limit theorem readback -/

namespace DirectLimitReadback

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [Ring Op] [Algebra ℝ Op]
variable {State LieAlgebra LieDual : Type*}

/-- The MDPAS finite-stage tower has a genuine quotient carrier and compatible finite identities. -/
theorem mdpas_direct_limit_theorem
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Nonempty (FiniteMDPASJMDirectSystem.DirectLimitCarrier T) ∧
      ∃ ofStageMap : ∀ _n : ℕ, Op → FiniteMDPASJMDirectSystem.DirectLimitCarrier T,
        (∀ n x, ofStageMap (n + 1) (T.bond n x) = ofStageMap n x) ∧
        (∀ n,
          ofStageMap (n + 1)
              (entropy_production (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (entropy_production (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (thermodynamic_gauge_connection (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (thermodynamic_gauge_connection (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (thermodynamic_curvature (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (thermodynamic_curvature (T.tower.stage n).flow)) ∧
        (∀ n,
          (T.tower.stage n).rn.entropy =
            (T.tower.stage n).rn.expectationBeta
              (T.tower.stage n).rn.modularPotential) ∧
        (∀ n,
          (T.tower.stage n).pathPacket.pathEntropy =
            (T.tower.stage n).pathPacket.trace
              (thermodynamic_curvature (T.tower.stage n).pathPacket.flow)) :=
  FiniteMDPASJMDirectSystem.inductiveLimitCarrier_lifts_finiteIdentities T

end DirectLimitReadback

end MDPASJMSouriauGlobalObstruction
end Physics
end InfoGeometry
