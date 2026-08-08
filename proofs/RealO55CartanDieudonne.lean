import proofs.Q55OrthogonalGeometry

/-! # Constructive Cartan--Dieudonne for the concrete split form `Q55`

The proof fixes the ten anisotropic orthogonal coordinate basis vectors in
order.  At each stage the one-vector correction contributes one or two
anisotropic reflections and preserves every coordinate fixed earlier.
-/

noncomputable section
namespace RealO55CartanDieudonne

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open RealPin55QuadraticRepresentation
open RealPin55ReflectionGenerators
open RealO55CartanDieudonneStep
open Q55OrthogonalGeometry
open V55Fin10Coordinates

def oqReflection (a : V55) (ha : Q55 a ≠ 0) : OQ55 :=
  fullPinToOQ55 (anisotropicPinLift a ha)

@[simp] theorem oqReflection_apply (a : V55) (ha : Q55 a ≠ 0) (v : V55) :
    (oqReflection a ha).1 v = anisotropicReflection a v := by
  exact anisotropicPinLift_action a ha v

def reflectionGeneratedOQ55 : Subgroup OQ55 :=
  Subgroup.closure {r | ∃ (a : V55) (ha : Q55 a ≠ 0), r = oqReflection a ha}

theorem oqReflection_mem_generated (a : V55) (ha : Q55 a ≠ 0) :
    oqReflection a ha ∈ reflectionGeneratedOQ55 := by
  apply Subgroup.subset_closure
  exact ⟨a, ha, rfl⟩

theorem B55_map (f : OQ55) (u v : V55) :
    B55 (f.1 u) (f.1 v) = B55 u v := by
  rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply]
  congr 1
  exact polar_map f u v

theorem polar_eq_two_smul_B55 (u v : V55) :
    QuadraticMap.polar Q55 u v = 2 • B55 u v := by
  have h := congrArg (fun F : LinearMap.BilinMap ℝ V55 ℝ => F u v)
    (QuadraticMap.two_nsmul_associated ℝ Q55)
  change 2 • B55 u v = QuadraticMap.polar Q55 u v at h
  exact h.symm

theorem anisotropicReflection_eq_self_of_ortho {a v : V55}
    (ha : Q55 a ≠ 0) (hav : B55 a v = 0) :
    anisotropicReflection a v = v := by
  unfold anisotropicReflection
  rw [polar_eq_two_smul_B55, hav]
  simp

theorem correction_normal_ortho_of_fixed (g : OQ55) {x w : V55}
    (hw : g.1 w = w) (hxw : B55 x w = 0) :
    B55 (g.1 x - x) w = 0 ∧ B55 (g.1 x + x) w = 0 := by
  have hmap : B55 (g.1 x) w = B55 x w := by
    calc
      B55 (g.1 x) w = B55 (g.1 x) (g.1 w) := by rw [hw]
      _ = B55 x w := B55_map g x w
  constructor <;> simp [map_sub, map_add, hmap, hxw]

private abbrev basis55 (i : Fin 10) : V55 := fin10Basis55 i

theorem basis55_ortho_of_lt {i : Fin 10} {k : ℕ} (hik : i.val < k)
    (hk : k < 10) : B55 (basis55 ⟨k, hk⟩) (basis55 i) = 0 := by
  apply fin10Basis55_orthogonal
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- Up to the first `k` coordinate directions, every split isometry admits a
left correction belonging to the reflection-generated subgroup. -/
theorem exists_generated_correction_fixing_first :
    ∀ k : ℕ, k ≤ 10 → ∀ f : OQ55,
      ∃ q : OQ55, q ∈ reflectionGeneratedOQ55 ∧
        ∀ i : Fin 10, i.val < k → (q * f).1 (basis55 i) = basis55 i := by
  intro k
  induction k with
  | zero =>
      intro hk f
      exact ⟨1, reflectionGeneratedOQ55.one_mem, by simp⟩
  | succ k ih =>
      intro hk f
      have hk10 : k < 10 := by omega
      rcases ih (by omega) f with ⟨q, hq, hfix⟩
      let g : OQ55 := q * f
      let x : V55 := basis55 ⟨k, hk10⟩
      have hx : Q55 x ≠ 0 := fin10Basis55_anisotropic ⟨k, hk10⟩
      rcases anisotropic_sub_or_add g hx with hsub | hadd
      · let a : V55 := g.1 x - x
        let c : OQ55 := oqReflection a hsub
        refine ⟨c * q, reflectionGeneratedOQ55.mul_mem
          (oqReflection_mem_generated a hsub) hq, ?_⟩
        intro i hi
        by_cases hik : i.val < k
        · have hgi : g.1 (basis55 i) = basis55 i := hfix i hik
          have haorth : B55 a (basis55 i) = 0 :=
            (correction_normal_ortho_of_fixed g hgi
              (basis55_ortho_of_lt hik hk10)).1
          change c.1 (g.1 (basis55 i)) = basis55 i
          rw [hgi, oqReflection_apply,
            anisotropicReflection_eq_self_of_ortho hsub haorth]
        · have hieq : i = ⟨k, hk10⟩ := by
            apply Fin.eq_of_val_eq
            have hiv : i.val = k := by omega
            exact hiv
          subst i
          change c.1 (g.1 x) = x
          rw [oqReflection_apply]
          exact reflection_sub_maps_image g hsub
      · let a : V55 := g.1 x + x
        let c₁ : OQ55 := oqReflection a hadd
        let c₂ : OQ55 := oqReflection x hx
        refine ⟨(c₂ * c₁) * q,
          reflectionGeneratedOQ55.mul_mem
            (reflectionGeneratedOQ55.mul_mem
              (oqReflection_mem_generated x hx)
              (oqReflection_mem_generated a hadd)) hq, ?_⟩
        intro i hi
        by_cases hik : i.val < k
        · have hgi : g.1 (basis55 i) = basis55 i := hfix i hik
          have horth := correction_normal_ortho_of_fixed g hgi
            (basis55_ortho_of_lt hik hk10)
          have haorth : B55 a (basis55 i) = 0 := horth.2
          have hxorth : B55 x (basis55 i) = 0 :=
            basis55_ortho_of_lt hik hk10
          change c₂.1 (c₁.1 (g.1 (basis55 i))) = basis55 i
          rw [hgi]
          rw [show c₁.1 (basis55 i) = anisotropicReflection a (basis55 i) from
            oqReflection_apply a hadd (basis55 i)]
          rw [anisotropicReflection_eq_self_of_ortho hadd haorth]
          rw [show c₂.1 (basis55 i) = anisotropicReflection x (basis55 i) from
            oqReflection_apply x hx (basis55 i)]
          exact anisotropicReflection_eq_self_of_ortho hx hxorth
        · have hieq : i = ⟨k, hk10⟩ := by
            apply Fin.eq_of_val_eq
            have hiv : i.val = k := by omega
            exact hiv
          subst i
          change c₂.1 (c₁.1 (g.1 x)) = x
          rw [show c₁.1 (g.1 x) = anisotropicReflection a (g.1 x) from
            oqReflection_apply a hadd (g.1 x)]
          rw [reflection_add_maps_image g hadd]
          rw [show c₂.1 (-x) = anisotropicReflection x (-x) from
            oqReflection_apply x hx (-x)]
          have hinv := anisotropicReflection_involutive hx x
          rw [anisotropicReflection_self hx] at hinv
          exact hinv

theorem reflectionGeneratedOQ55_eq_top : reflectionGeneratedOQ55 = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro f
  rcases exists_generated_correction_fixing_first 10 le_rfl f with
    ⟨q, hq, hfix⟩
  have hqf : q * f = 1 := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply fin10Basis55.ext
    intro i
    simpa using hfix i i.isLt
  have hf : f = q⁻¹ := by
    calc
      f = 1 * f := by simp
      _ = (q⁻¹ * q) * f := by rw [inv_mul_cancel]
      _ = q⁻¹ * (q * f) := by rw [mul_assoc]
      _ = q⁻¹ := by rw [hqf, mul_one]
  rw [hf]
  exact reflectionGeneratedOQ55.inv_mem hq

theorem reflectionGeneratedOQ55_le_pinRange :
    reflectionGeneratedOQ55 ≤ MonoidHom.range fullPinToOQ55 := by
  rw [reflectionGeneratedOQ55, Subgroup.closure_le]
  intro r hr
  rcases hr with ⟨a, ha, rfl⟩
  exact ⟨anisotropicPinLift a ha, rfl⟩

/-- Constructive indefinite Cartan--Dieudonne gives surjectivity of the full
real Pin action onto the native quadratic orthogonal group. -/
theorem fullPinToOQ55_surjective : Function.Surjective fullPinToOQ55 := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← reflectionGeneratedOQ55_eq_top]
  exact reflectionGeneratedOQ55_le_pinRange

end RealO55CartanDieudonne
end noncomputable section
