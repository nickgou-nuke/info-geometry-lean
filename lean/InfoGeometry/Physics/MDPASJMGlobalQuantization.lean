import Mathlib
import InfoGeometry.Physics.MDPASJMSouriauDigest

/-!
# Finite MDPAS/JM Souriau global-quantization shadow

#### BUCKET 1: CLOSED FINITE THEOREMS

This file proves a finite rational corridor for:

* a graph de Rham obstruction on a 3-cycle;
* the canonical symplectic form on `ℚ⁴`;
* a symmetric 5D Kaluza--Klein block matrix;
* half-spin prequantization as an integral rational relation;
* readback of the MDPAS/JM direct-limit carrier theorem.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The direct-limit readback depends on an explicit
`FiniteMDPASJMDirectSystem`, whose bonding equations are concrete equations on
the finite flow components.

#### BUCKET 3: OPEN CLOSURE DEBT

No global smooth de Rham cohomology theorem, smooth symplectic manifold,
analytic Kaluza--Klein compactification, or full geometric quantization theorem
is claimed here.
-/

noncomputable section

namespace InfoGeometry.Physics.MDPASJMGlobalQuantization

open InfoGeometry.Physics.MDPASJMSouriauDigest

abbrev Vec3 := Fin 3 → ℚ
abbrev Vec4 := Fin 4 → ℚ

/-! ## 1. Finite de Rham obstruction on a 3-cycle -/

/-- A rational 1-cochain on the oriented cycle `0 → 1 → 2 → 0`. -/
structure TriangleOneForm where
  e01 : ℚ
  e12 : ℚ
  e20 : ℚ

/-- The cycle integral of a 1-form around `0 → 1 → 2 → 0`. -/
def cycleIntegral (A : TriangleOneForm) : ℚ :=
  A.e01 + A.e12 + A.e20

/-- Exactness means the edge values are differences of a vertex potential. -/
def IsExact (A : TriangleOneForm) : Prop :=
  ∃ φ : Vec3,
    A.e01 = φ 1 - φ 0 ∧
    A.e12 = φ 2 - φ 1 ∧
    A.e20 = φ 0 - φ 2

/-- Exact finite 1-forms have zero cycle integral. -/
theorem cycleIntegral_eq_zero_of_exact
    (A : TriangleOneForm) (hA : IsExact A) :
    cycleIntegral A = 0 := by
  rcases hA with ⟨φ, h01, h12, h20⟩
  simp [cycleIntegral, h01, h12, h20]

/-- A nonzero cycle integral obstructs exactness. -/
theorem not_exact_of_cycleIntegral_ne_zero
    (A : TriangleOneForm) (hA : cycleIntegral A ≠ 0) :
    ¬ IsExact A := by
  intro hExact
  exact hA (cycleIntegral_eq_zero_of_exact A hExact)

/-- The constant unit current around the 3-cycle has obstruction `3`. -/
def unitCycleCurrent : TriangleOneForm :=
  { e01 := 1, e12 := 1, e20 := 1 }

@[simp] theorem cycleIntegral_unitCycleCurrent :
    cycleIntegral unitCycleCurrent = 3 := by
  norm_num [unitCycleCurrent, cycleIntegral]

theorem unitCycleCurrent_not_exact :
    ¬ IsExact unitCycleCurrent := by
  exact not_exact_of_cycleIntegral_ne_zero unitCycleCurrent (by norm_num)

/-! ## 2. Finite global symplectic carrier on `ℚ⁴` -/

/-- Standard basis vector of `ℚ⁴`. -/
def basis4 (k : Fin 4) : Vec4 :=
  fun i => if i = k then 1 else 0

/-- Canonical symplectic form `dq₁∧dp₁ + dq₂∧dp₂` on `ℚ⁴`. -/
def omega4 (x y : Vec4) : ℚ :=
  x 0 * y 2 - x 2 * y 0 + x 1 * y 3 - x 3 * y 1

theorem omega4_skew (x y : Vec4) :
    omega4 x y = -omega4 y x := by
  simp [omega4]
  ring

theorem omega4_self (x : Vec4) :
    omega4 x x = 0 := by
  have h := omega4_skew x x
  linarith

theorem omega4_nondegenerate
    (x : Vec4)
    (h : ∀ y : Vec4, omega4 x y = 0) :
    x = 0 := by
  have h0 : x 0 = 0 := by
    simpa [omega4, basis4] using h (basis4 2)
  have h1 : x 1 = 0 := by
    simpa [omega4, basis4] using h (basis4 3)
  have h2 : x 2 = 0 := by
    have hx := h (basis4 0)
    simp [omega4, basis4] at hx
    linarith
  have h3 : x 3 = 0 := by
    have hx := h (basis4 1)
    simp [omega4, basis4] at hx
    linarith
  ext i
  fin_cases i <;> simp [h0, h1, h2, h3]

/-! ## 3. Finite 5D Kaluza--Klein block metric -/

/-- Flat 4D diagonal part used by the finite Kaluza--Klein block matrix. -/
def flat4Entry (i j : Fin 4) : ℚ :=
  if i = j then
    if i = 0 then 1 else -1
  else 0

/-- Explicit finite 5D Kaluza--Klein block matrix over `ℚ`. -/
def kkMetric5 (r : ℚ) (A : Vec4) : Matrix (Fin 5) (Fin 5) ℚ :=
  !![
    flat4Entry 0 0 + r * A 0 * A 0, flat4Entry 0 1 + r * A 0 * A 1,
      flat4Entry 0 2 + r * A 0 * A 2, flat4Entry 0 3 + r * A 0 * A 3, r * A 0;
    flat4Entry 1 0 + r * A 1 * A 0, flat4Entry 1 1 + r * A 1 * A 1,
      flat4Entry 1 2 + r * A 1 * A 2, flat4Entry 1 3 + r * A 1 * A 3, r * A 1;
    flat4Entry 2 0 + r * A 2 * A 0, flat4Entry 2 1 + r * A 2 * A 1,
      flat4Entry 2 2 + r * A 2 * A 2, flat4Entry 2 3 + r * A 2 * A 3, r * A 2;
    flat4Entry 3 0 + r * A 3 * A 0, flat4Entry 3 1 + r * A 3 * A 1,
      flat4Entry 3 2 + r * A 3 * A 2, flat4Entry 3 3 + r * A 3 * A 3, r * A 3;
    r * A 0, r * A 1, r * A 2, r * A 3, r
  ]

theorem kkMetric5_symmetric (r : ℚ) (A : Vec4) :
    (kkMetric5 r A).transpose = kkMetric5 r A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kkMetric5, flat4Entry] <;> ring

/-! ## 4. Finite prequantization and direct-limit readback -/

/-- Rational prequantization integrality relation. -/
def Prequantized (charge hbar : ℚ) : Prop :=
  ∃ k : ℤ, charge = k * hbar

theorem halfSpin_prequantized (hbar : ℚ) :
    Prequantized hbar hbar := by
  exact ⟨1, by ring⟩

theorem directLimitCarrier_lifts_finiteIdentities_readback
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {Op : Type*} [Ring Op] [Algebra ℝ Op]
    {State LieAlgebra LieDual : Type*}
    (T : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual) :
    Nonempty (FiniteMDPASJMDirectSystem.DirectLimitCarrier T) ∧
      ∃ ofStageMap : ∀ _n : ℕ, Op →
          FiniteMDPASJMDirectSystem.DirectLimitCarrier T,
        (∀ n x, ofStageMap (n + 1) (T.bond n x) = ofStageMap n x) ∧
        (∀ n,
          ofStageMap (n + 1)
              (InfoGeometry.Topology.ThermodynamicGauge.entropy_production
                (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (InfoGeometry.Topology.ThermodynamicGauge.entropy_production
                (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_gauge_connection
                (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_gauge_connection
                (T.tower.stage n).flow)) ∧
        (∀ n,
          ofStageMap (n + 1)
              (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_curvature
                (T.tower.stage (n + 1)).flow) =
            ofStageMap n
              (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_curvature
                (T.tower.stage n).flow)) ∧
        (∀ n,
          (T.tower.stage n).rn.entropy =
            (T.tower.stage n).rn.expectationBeta
              (T.tower.stage n).rn.modularPotential) ∧
        (∀ n,
          (T.tower.stage n).pathPacket.pathEntropy =
            (T.tower.stage n).pathPacket.trace
              (InfoGeometry.Topology.ThermodynamicGauge.thermodynamic_curvature
                (T.tower.stage n).pathPacket.flow)) := by
  exact FiniteMDPASJMDirectSystem.inductiveLimitCarrier_lifts_finiteIdentities T

end InfoGeometry.Physics.MDPASJMGlobalQuantization
