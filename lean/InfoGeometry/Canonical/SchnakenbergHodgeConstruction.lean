import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite Euclidean gradient/cycle projection for the existing thermodynamic
graph carrier.  This is a metric construction; no continuum or embedding is
implicit. -/
noncomputable section
namespace InfoGeometry.Canonical.SchnakenbergHodgeConstruction

open ThermodynamicChiralGraphCalculus
open scoped BigOperators InnerProductSpace

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
variable (G : DirectedThermoGraph V E)

def gradientEuclidean : (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ E where
  toFun φ := WithLp.toLp 2 (G.gaugeCoboundary φ)
  map_add' φ ψ := by
    ext e
    simp [DirectedThermoGraph.gaugeCoboundary,
      PiLp.add_apply]
    abel
  map_smul' c φ := by
    ext e
    simp [DirectedThermoGraph.gaugeCoboundary,
      PiLp.smul_apply]
    ring

@[simp] theorem gradientEuclidean_apply (φ : V → ℝ) (e : E) :
    gradientEuclidean G φ e = G.gaugeCoboundary φ e := rfl

def gradientSubspace : Submodule ℝ (EuclideanSpace ℝ E) :=
  LinearMap.range (gradientEuclidean G)

def gradientComponent (a : E → ℝ) : EuclideanSpace ℝ E :=
  (gradientSubspace G).starProjection (WithLp.toLp 2 a)

def cycleComponent (a : E → ℝ) : EuclideanSpace ℝ E :=
  WithLp.toLp 2 a - gradientComponent G a

theorem gradientComponent_mem (a : E → ℝ) :
    gradientComponent G a ∈ gradientSubspace G := by
  exact Submodule.starProjection_apply_mem (U := gradientSubspace G) _

theorem cycleComponent_mem (a : E → ℝ) :
    cycleComponent G a ∈ (gradientSubspace G)ᗮ := by
  unfold cycleComponent gradientComponent
  exact Submodule.sub_starProjection_mem_orthogonal _

theorem component_reconstruction (a : E → ℝ) :
    gradientComponent G a + cycleComponent G a = WithLp.toLp 2 a := by
  unfold cycleComponent
  abel

theorem gradientComponent_isGradient (a : E → ℝ) :
    G.IsGradientFlow (fun e => gradientComponent G a e) := by
  rcases gradientComponent_mem G a with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro e
  exact (congrArg (fun z : EuclideanSpace ℝ E => z e) hφ).symm

theorem steady_pair_coboundary_zero (J : E → ℝ) (hJ : G.IsCycleFlow J)
    (φ : V → ℝ) :
    ∑ e, J e * G.gaugeCoboundary φ e = 0 := by
  classical
  unfold DirectedThermoGraph.gaugeCoboundary
  have gather (endpoint : E → V) :
      (∑ v, φ v * ∑ e, if endpoint e = v then J e else 0) =
        ∑ e, φ (endpoint e) * J e := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [mul_ite, eq_comm]
  have hsplit :
      (∑ e, J e * (φ (G.dst e) - φ (G.src e))) =
        (∑ e, φ (G.dst e) * J e) - ∑ e, φ (G.src e) * J e := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_comm]
  have hdst : (∑ e, J e * φ (G.dst e)) =
      ∑ v, φ v * ∑ e, if G.dst e = v then J e else 0 := by
    simpa [mul_comm] using (gather G.dst).symm
  have hsrc : (∑ e, J e * φ (G.src e)) =
      ∑ v, φ v * ∑ e, if G.src e = v then J e else 0 := by
    simpa [mul_comm] using (gather G.src).symm
  have hzero : ∑ v, φ v * G.incidenceMap J v = 0 :=
    Finset.sum_eq_zero (fun v hv => by rw [hJ v]; simp)
  calc
    ∑ e, J e * G.gaugeCoboundary φ e =
        (∑ e, φ (G.dst e) * J e) - ∑ e, φ (G.src e) * J e := by
          simpa [DirectedThermoGraph.gaugeCoboundary, mul_comm] using hsplit
    _ = - (∑ v, φ v * G.incidenceMap J v) := by
          have hdst' : (∑ e, φ (G.dst e) * J e) =
              ∑ v, φ v * ∑ e, if G.dst e = v then J e else 0 := by
            simpa [mul_comm] using hdst
          have hsrc' : (∑ e, φ (G.src e) * J e) =
              ∑ v, φ v * ∑ e, if G.src e = v then J e else 0 := by
            simpa [mul_comm] using hsrc
          rw [hdst', hsrc']
          change
            (∑ v, φ v * ∑ e, if G.dst e = v then J e else 0) -
                (∑ v, φ v * ∑ e, if G.src e = v then J e else 0) =
              - (∑ v, φ v * ((∑ e, if G.src e = v then J e else 0) -
                ∑ e, if G.dst e = v then J e else 0))
          simp_rw [mul_sub]
          simp_rw [Finset.sum_sub_distrib]
          ring
    _ = 0 := by simpa [hzero]

theorem steady_pair_cycleComponent (J a : E → ℝ) (hJ : G.IsCycleFlow J) :
    (∑ e, J e * a e) =
      ∑ e, J e * cycleComponent G a e := by
  rcases gradientComponent_isGradient G a with ⟨φ, hφ⟩
  have hrec (e : E) : a e = G.gaugeCoboundary φ e + cycleComponent G a e := by
    have h := congrArg (fun z : EuclideanSpace ℝ E => z e)
      (component_reconstruction G a)
    calc
      a e = gradientComponent G a e + cycleComponent G a e := h.symm
      _ = G.gaugeCoboundary φ e + cycleComponent G a e := by
        simpa using congrArg (fun x => x + cycleComponent G a e) (hφ e)
  simp_rw [hrec, mul_add]
  rw [Finset.sum_add_distrib, steady_pair_coboundary_zero G J hJ φ, zero_add]

end InfoGeometry.Canonical.SchnakenbergHodgeConstruction
