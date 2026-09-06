import Mathlib
import InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors

/-!
# Topological cyclotomic charge on the native chiral Zorn carrier

This owner lifts the canonical cubic charge and its three Peirce projectors
to the product topology transported through the native Zorn coordinates.
It does not add any new algebraic identities; it only proves continuity and
the induced order-three homeomorphism on the coordinate carrier.
-/

namespace InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological

open InfoGeometry.Canonical
open ZornMatrix

noncomputable section

abbrev Zorn := ZornMatrix ℂ

abbrev ZornCoords :=
  (ℂ × ℂ) × ((Fin 3 → ℂ) × (Fin 3 → ℂ))

/-- The native coordinate chart for the chiral Zorn carrier. -/
def zornCoords : Zorn → ZornCoords :=
  fun Z => ((Z.a, Z.b), (Z.x, Z.y))

instance : TopologicalSpace Zorn :=
  TopologicalSpace.induced zornCoords inferInstance

theorem continuous_zornCoords : Continuous zornCoords :=
  continuous_induced_dom

theorem continuous_zorn_a : Continuous (fun Z : Zorn => Z.a) :=
  continuous_fst.comp (continuous_fst.comp continuous_zornCoords)

theorem continuous_zorn_b : Continuous (fun Z : Zorn => Z.b) :=
  continuous_snd.comp (continuous_fst.comp continuous_zornCoords)

theorem continuous_zorn_x : Continuous (fun Z : Zorn => Z.x) :=
  continuous_fst.comp (continuous_snd.comp continuous_zornCoords)

theorem continuous_zorn_y : Continuous (fun Z : Zorn => Z.y) :=
  continuous_snd.comp (continuous_snd.comp continuous_zornCoords)

private theorem continuous_cubicCharge_x (ω : ℂ) :
    Continuous (fun Z : Zorn => ω • Z.x) := by
  apply continuous_pi
  intro i
  exact
    Continuous.smul
      (continuous_const : Continuous fun _ : Zorn => (ω : ℂ))
      ((continuous_apply i).comp continuous_zorn_x)

private theorem continuous_cubicCharge_y (ω : ℂ) :
    Continuous (fun Z : Zorn => (ω ^ 2) • Z.y) := by
  apply continuous_pi
  intro i
  exact
    Continuous.smul
      (continuous_const : Continuous fun _ : Zorn => ((ω ^ 2) : ℂ))
      ((continuous_apply i).comp continuous_zorn_y)

/-- The cubic charge is continuous on the topological Zorn carrier. -/
theorem continuous_cubicCharge (ω : ℂ) :
    Continuous (cubicCharge ω : Zorn → Zorn) := by
  have hcoord : Continuous (fun Z : Zorn => zornCoords (cubicCharge ω Z)) := by
    have ha : Continuous (fun Z : Zorn => Z.a) := continuous_zorn_a
    have hb : Continuous (fun Z : Zorn => Z.b) := continuous_zorn_b
    have hx : Continuous (fun Z : Zorn => ω • Z.x) := continuous_cubicCharge_x ω
    have hy : Continuous (fun Z : Zorn => (ω ^ 2) • Z.y) := continuous_cubicCharge_y ω
    simpa [zornCoords, cubicCharge] using (ha.prodMk hb).prodMk (hx.prodMk hy)
  exact (continuous_induced_rng).2 hcoord

private theorem continuous_cubicProjectorZero_coords :
    Continuous (fun Z : Zorn => zornCoords (cubicProjectorZero Z)) := by
  have ha : Continuous (fun Z : Zorn => Z.a) := continuous_zorn_a
  have hb : Continuous (fun Z : Zorn => Z.b) := continuous_zorn_b
  have hz : Continuous (fun _ : Zorn => (0 : Fin 3 → ℂ)) := by
    simpa using (continuous_const : Continuous fun _ : Zorn => (0 : Fin 3 → ℂ))
  simpa [zornCoords, cubicProjectorZero] using (ha.prodMk hb).prodMk (hz.prodMk hz)

private theorem continuous_cubicProjectorPlus_coords :
    Continuous (fun Z : Zorn => zornCoords (cubicProjectorPlus Z)) := by
  have hx : Continuous (fun Z : Zorn => Z.x) := continuous_zorn_x
  have hz : Continuous (fun _ : Zorn => (0 : Fin 3 → ℂ)) := by
    simpa using (continuous_const : Continuous fun _ : Zorn => (0 : Fin 3 → ℂ))
  have h0 : Continuous (fun _ : Zorn => (0 : ℂ)) := by
    simpa using (continuous_const : Continuous fun _ : Zorn => (0 : ℂ))
  simpa [zornCoords, cubicProjectorPlus] using (h0.prodMk h0).prodMk (hx.prodMk hz)

private theorem continuous_cubicProjectorMinus_coords :
    Continuous (fun Z : Zorn => zornCoords (cubicProjectorMinus Z)) := by
  have hy : Continuous (fun Z : Zorn => Z.y) := continuous_zorn_y
  have hz : Continuous (fun _ : Zorn => (0 : Fin 3 → ℂ)) := by
    simpa using (continuous_const : Continuous fun _ : Zorn => (0 : Fin 3 → ℂ))
  have h0 : Continuous (fun _ : Zorn => (0 : ℂ)) := by
    simpa using (continuous_const : Continuous fun _ : Zorn => (0 : ℂ))
  simpa [zornCoords, cubicProjectorMinus] using (h0.prodMk h0).prodMk (hz.prodMk hy)

/-- The diagonal projector is continuous. -/
theorem continuous_cubicProjectorZero :
    Continuous (cubicProjectorZero : Zorn →ₗ[ℂ] Zorn) := by
  exact (continuous_induced_rng).2 continuous_cubicProjectorZero_coords

/-- The color projector is continuous. -/
theorem continuous_cubicProjectorPlus :
    Continuous (cubicProjectorPlus : Zorn →ₗ[ℂ] Zorn) := by
  exact (continuous_induced_rng).2 continuous_cubicProjectorPlus_coords

/-- The anticolor projector is continuous. -/
theorem continuous_cubicProjectorMinus :
    Continuous (cubicProjectorMinus : Zorn →ₗ[ℂ] Zorn) := by
  exact (continuous_induced_rng).2 continuous_cubicProjectorMinus_coords

/-- The cubic charge is an order-three topological automorphism when `ω^3 = 1`. -/
noncomputable def cubicChargeHomeomorph (ω : ℂ) (hω : ω ^ 3 = 1) : Zorn ≃ₜ Zorn where
  toFun := cubicCharge ω
  invFun := cubicCharge (ω ^ 2)
  left_inv := by
    intro Z
    ext
    · simp [cubicCharge]
    · simp [cubicCharge]
    ·
      simp [cubicCharge]
      ring_nf
      rw [hω, one_mul]
    ·
      have hω6 : ω ^ 6 = 1 := by
        calc
          ω ^ 6 = (ω ^ 3) ^ 2 := by
            rw [show 6 = 3 * 2 by norm_num, pow_mul]
          _ = 1 := by rw [hω]; norm_num
      simp [cubicCharge]
      ring_nf
      rw [hω6, one_mul]
  right_inv := by
    intro Z
    ext
    · simp [cubicCharge]
    · simp [cubicCharge]
    ·
      simp [cubicCharge]
      ring_nf
      rw [hω, one_mul]
    ·
      have hω6 : ω ^ 6 = 1 := by
        calc
          ω ^ 6 = (ω ^ 3) ^ 2 := by
            rw [show 6 = 3 * 2 by norm_num, pow_mul]
          _ = 1 := by rw [hω]; norm_num
      simp [cubicCharge]
      ring_nf
      rw [hω6, one_mul]
  continuous_toFun := continuous_cubicCharge ω
  continuous_invFun := continuous_cubicCharge (ω ^ 2)

@[simp] theorem cubicChargeHomeomorph_apply (ω : ℂ) (hω : ω ^ 3 = 1) (Z : Zorn) :
    cubicChargeHomeomorph ω hω Z = cubicCharge ω Z := rfl

end

end InfoGeometry.Topology.ThreeColorCyclotomicChargeTopological
