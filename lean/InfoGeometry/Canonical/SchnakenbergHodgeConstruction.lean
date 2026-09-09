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

theorem coboundary_incidence_pairing (phi : V → ℝ) (J : E → ℝ) :
    (∑ e, G.gaugeCoboundary phi e * J e) =
      -(∑ v, phi v * G.incidenceMap J v) := by
  classical
  have gather (endpoint : E → V) :
      (∑ v, phi v * ∑ e, if endpoint e = v then J e else 0) =
        ∑ e, phi (endpoint e) * J e := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp [mul_ite, eq_comm]
  calc
    (∑ e, G.gaugeCoboundary phi e * J e) =
        (∑ e, phi (G.dst e) * J e) - ∑ e, phi (G.src e) * J e := by
      simp only [DirectedThermoGraph.gaugeCoboundary, sub_mul,
        Finset.sum_sub_distrib]
    _ = -((∑ v, phi v * ∑ e, if G.src e = v then J e else 0) -
        ∑ v, phi v * ∑ e, if G.dst e = v then J e else 0) := by
      rw [gather G.src, gather G.dst]
      ring
    _ = -(∑ v, phi v * G.incidenceMap J v) := by
      simp only [DirectedThermoGraph.incidenceMap, mul_sub,
        Finset.sum_sub_distrib]

theorem mem_gradientSubspace_iff (a : EuclideanSpace ℝ E) :
    a ∈ gradientSubspace G ↔ G.IsGradientFlow (fun e => a e) := by
  constructor
  · rintro ⟨phi, hphi⟩
    refine ⟨phi, ?_⟩
    intro e
    exact (congrArg (fun z : EuclideanSpace ℝ E => z e) hphi).symm
  · rintro ⟨phi, hphi⟩
    refine ⟨phi, ?_⟩
    ext e
    exact (hphi e).symm

theorem gradient_inner_incidence (phi : V → ℝ) (J : EuclideanSpace ℝ E) :
    ⟪gradientEuclidean G phi, J⟫_ℝ =
      -(∑ v, phi v * G.incidenceMap (fun e => J e) v) := by
  simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using
    coboundary_incidence_pairing G phi (fun e => J e)

/-- The orthogonal complement is proved equal to the owner's cycle-flow predicate. -/
theorem mem_orthogonal_gradient_iff (J : EuclideanSpace ℝ E) :
    J ∈ (gradientSubspace G)ᗮ ↔ G.IsCycleFlow (fun e => J e) := by
  classical
  constructor
  · intro hJ v
    let phi : V → ℝ := fun u => if u = v then 1 else 0
    have hinner : ⟪gradientEuclidean G phi, J⟫_ℝ = 0 :=
      ((gradientSubspace G).mem_orthogonal J).mp hJ _ ⟨phi, rfl⟩
    rw [gradient_inner_incidence] at hinner
    have hsum : (∑ u, phi u * G.incidenceMap (fun e => J e) u) =
        G.incidenceMap (fun e => J e) v := by
      simp [phi]
    rw [hsum] at hinner
    exact neg_eq_zero.mp hinner
  · intro hJ
    apply ((gradientSubspace G).mem_orthogonal J).mpr
    rintro a ⟨phi, rfl⟩
    rw [gradient_inner_incidence]
    have hz : (∑ v, phi v * G.incidenceMap (fun e => J e) v) = 0 := by
      have hzero : ∀ v, G.incidenceMap (fun e => J e) v = 0 := hJ
      simp_rw [hzero, mul_zero, Finset.sum_const_zero]
    rw [hz, neg_zero]

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

/-- Uniqueness is a consequence of the two orthogonal subspaces, not input data. -/
theorem component_unique (a B C : E → ℝ)
    (hB : G.IsGradientFlow B) (hC : G.IsCycleFlow C)
    (hrec : ∀ e, a e = B e + C e) :
    B = (fun e => gradientComponent G a e) ∧
      C = (fun e => cycleComponent G a e) := by
  let b : EuclideanSpace ℝ E := WithLp.toLp 2 B
  let c : EuclideanSpace ℝ E := WithLp.toLp 2 C
  have hb : b ∈ gradientSubspace G :=
    (mem_gradientSubspace_iff G b).mpr hB
  have hc : c ∈ (gradientSubspace G)ᗮ :=
    (mem_orthogonal_gradient_iff G c).mpr hC
  have ha : WithLp.toLp 2 a = b + c := by
    ext e
    exact hrec e
  have hdiff : b - gradientComponent G a = cycleComponent G a - c := by
    rw [cycleComponent, ha]
    abel
  have hm : b - gradientComponent G a ∈
      gradientSubspace G ⊓ (gradientSubspace G)ᗮ := by
    constructor
    · exact (gradientSubspace G).sub_mem hb (gradientComponent_mem G a)
    · rw [hdiff]
      exact ((gradientSubspace G)ᗮ).sub_mem (cycleComponent_mem G a) hc
  have hz : b - gradientComponent G a = 0 := by
    simpa only [(gradientSubspace G).inf_orthogonal_eq_bot,
      Submodule.mem_bot] using hm
  have hbEq : b = gradientComponent G a := sub_eq_zero.mp hz
  have hcEq : c = cycleComponent G a := by
    rw [cycleComponent, ha, hbEq]
    abel
  constructor
  · funext e
    exact congrArg (fun z : EuclideanSpace ℝ E => z e) hbEq
  · funext e
    exact congrArg (fun z : EuclideanSpace ℝ E => z e) hcEq

/-- A construction of the existing record, with every law discharged. -/
def schnakenbergHodge (a : E → ℝ) : G.SchnakenbergDecomposition a where
  gradientPart := fun e => gradientComponent G a e
  cyclePart := fun e => cycleComponent G a e
  gradient_certificate := gradientComponent_isGradient G a
  cycle_certificate := (mem_orthogonal_gradient_iff G _).mp (cycleComponent_mem G a)
  reconstruct e := by
    have h := congrArg (fun z : EuclideanSpace ℝ E => z e) (component_reconstruction G a)
    exact h.symm
  unique B C hB hC hrec := component_unique G a B C hB hC hrec

/-- The owner theorem now applies without a supplied decomposition packet. -/
theorem schnakenberg_exists_unique (a : E → ℝ) :
    ∃! P : (E → ℝ) × (E → ℝ),
      G.IsGradientFlow P.1 ∧ G.IsCycleFlow P.2 ∧
        ∀ e, a e = P.1 e + P.2 e := by
  exact G.schnakenberg_decomposition a (schnakenbergHodge G a)

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

theorem steady_pair_gauge_shift (J a : E → ℝ) (hJ : G.IsCycleFlow J)
    (phi : V → ℝ) :
    (∑ e, J e * (a e + G.gaugeCoboundary phi e)) = ∑ e, J e * a e := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [steady_pair_coboundary_zero G J hJ phi, add_zero]

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
