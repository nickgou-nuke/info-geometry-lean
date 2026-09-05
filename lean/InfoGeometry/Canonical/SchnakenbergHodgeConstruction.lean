import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Construct the existing finite Schnakenberg decomposition

The graph, incidence, coboundary, and decomposition record belong to
`ThermodynamicChiralGraphCalculus`. Only the missing construction is added.
The metric used for this constructor is the positive Euclidean edge pairing.
The owner's incidence is outgoing minus incoming, hence minus the adjoint
of its target-minus-source coboundary. No spacetime or embedding is needed.
-/

noncomputable section
namespace InfoGeometry.Canonical.SchnakenbergHodgeConstruction

open ThermodynamicChiralGraphCalculus
open scoped BigOperators InnerProductSpace

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
variable (G : DirectedThermoGraph V E)

/-- Integration by parts for the already owned coboundary and incidence. -/
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

/-- The owner's coboundary, bundled into Mathlib's finite Hilbert space. -/
def gradientEuclidean : (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ E where
  toFun phi := WithLp.toLp 2 (G.gaugeCoboundary phi)
  map_add' phi psi := by
    ext e
    change (phi (G.dst e) + psi (G.dst e)) - (phi (G.src e) + psi (G.src e)) =
      (phi (G.dst e) - phi (G.src e)) + (psi (G.dst e) - psi (G.src e))
    ring
  map_smul' c phi := by
    ext e
    change c * phi (G.dst e) - c * phi (G.src e) =
      c * (phi (G.dst e) - phi (G.src e))
    ring

@[simp] theorem gradientEuclidean_apply (phi : V → ℝ) (e : E) :
    gradientEuclidean G phi e = G.gaugeCoboundary phi e := rfl

/-- Native exact-edge subspace, without imposing connectedness. -/
def gradientSubspace : Submodule ℝ (EuclideanSpace ℝ E) :=
  LinearMap.range (gradientEuclidean G)

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
    simp [hJ]

/-- Orthogonal projection is available because the edge space is finite-dimensional. -/
def gradientComponent (a : E → ℝ) : EuclideanSpace ℝ E :=
  (gradientSubspace G).starProjection (WithLp.toLp 2 a)

/-- Residual after the exact projection, still using the same edge coordinates. -/
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
  gradient_property := (mem_gradientSubspace_iff G _).mp (gradientComponent_mem G a)
  cycle_property := (mem_orthogonal_gradient_iff G _).mp (cycleComponent_mem G a)
  reconstruct e := by
    change a e = gradientComponent G a e + (a e - gradientComponent G a e)
    ring
  unique B C hB hC hrec := component_unique G a B C hB hC hrec

/-- The owner theorem now applies without a supplied decomposition packet. -/
theorem schnakenberg_exists_unique (a : E → ℝ) :
    ∃! P : (E → ℝ) × (E → ℝ),
      G.IsGradientFlow P.1 ∧ G.IsCycleFlow P.2 ∧
        ∀ e, a e = P.1 e + P.2 e := by
  exact G.schnakenberg_decomposition a (schnakenbergHodge G a)

/-- A steady current annihilates every exact affinity. No detailed balance is required. -/
theorem steady_pair_coboundary_zero (J : E → ℝ) (hJ : G.IsCycleFlow J)
    (phi : V → ℝ) : ∑ e, J e * G.gaugeCoboundary phi e = 0 := by
  have h := coboundary_incidence_pairing G phi J
  simpa [hJ, mul_comm] using h

/-- Exact gauge shifts preserve steady current-affinity pairing. -/
theorem steady_pair_gauge_shift (J a : E → ℝ) (hJ : G.IsCycleFlow J)
    (phi : V → ℝ) :
    (∑ e, J e * (a e + G.gaugeCoboundary phi e)) = ∑ e, J e * a e := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [steady_pair_coboundary_zero G J hJ phi, add_zero]

/-- Only the constructed cycle component contributes to steady production. -/
theorem steady_pair_cycleComponent (J a : E → ℝ) (hJ : G.IsCycleFlow J) :
    (∑ e, J e * a e) = ∑ e, J e * cycleComponent G a e := by
  rcases (schnakenbergHodge G a).gradient_property with ⟨phi, hphi⟩
  have hrec (e : E) : a e = G.gaugeCoboundary phi e + cycleComponent G a e := by
    have h := (schnakenbergHodge G a).reconstruct e
    rw [hphi e] at h
    exact h
  simp_rw [hrec, mul_add]
  rw [Finset.sum_add_distrib, steady_pair_coboundary_zero G J hJ phi, zero_add]

end InfoGeometry.Canonical.SchnakenbergHodgeConstruction
