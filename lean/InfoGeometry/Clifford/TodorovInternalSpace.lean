import InfoGeometry.Cartan.Involution
import Mathlib

/-!
# Todorov octonion internal-space projector calculus

This module extracts a theorem-safe algebraic fragment from Ivan Todorov,
"Octonion Internal Space Algebra for the Standard Model", Universe 9 (2023),
222, DOI `10.3390/universe9050222`.

The paper uses the `Cl₆` volume form `ω₆` to define the particle projector
`P = 1/2 (1 - iω₆)` on the complex spinor space.  Rather than asserting the
full Standard Model identification, Pati--Salam stabilizer theorem, Higgs mass
formula, or octonionic classification, this file proves the underlying linear
algebra used by that construction:

* a complex-linear volume operator `Ω` with `Ω² = -1` gives an involution
  `K = iΩ`;
* every involution `K² = 1` gives complementary idempotent projectors
  `1/2(1 - K)` and `1/2(1 + K)`, reusing the Cartan projector owner;
* maps commuting with `K` preserve both projectors;
* the stabilizer of a distinguished vector is a subgroup of the ambient linear
  equivalence group.

Thus the physics words "particle projector", "antiparticle projector", and
"sterile-neutrino stabilizer" are represented here only by explicit hypotheses
and kernel-checked algebraic consequences.
-/

noncomputable section

namespace InfoGeometry.Clifford.TodorovInternalSpace

variable (S : Type*) [AddCommGroup S] [Module ℂ S]

/-- Complex-linear endomorphisms of the spinor carrier. -/
abbrev SpinorEnd := Module.End ℂ S

/-- Todorov's `iω₆` axis, abstracted from a volume operator `Ω` with `Ω² = -1`. -/
def complexVolumeInvolution (Ω : SpinorEnd S) : SpinorEnd S :=
  Complex.I • Ω

/-- If the volume operator squares to `-1`, then multiplication by `i` turns it
into an involution. -/
theorem complexVolumeInvolution_sq (Ω : SpinorEnd S) (hΩ : Ω * Ω = -1) :
    complexVolumeInvolution S Ω * complexVolumeInvolution S Ω = 1 := by
  ext x
  have hΩx := LinearMap.congr_fun hΩ x
  simp [complexVolumeInvolution] at hΩx ⊢
  rw [hΩx]
  rw [← mul_smul]
  simp [Complex.I_mul_I]

/-- The `-1` spectral projector `1/2(1-K)`, matching Todorov's particle projector
when `K = iω₆`.  This is the Cartan `Pminus` projector with Todorov naming. -/
abbrev particleProjector (K : SpinorEnd S) : SpinorEnd S :=
  InfoGeometry.Cartan.Pminus K

/-- The complementary `+1` spectral projector `1/2(1+K)`.  This is the Cartan
`Pplus` projector with Todorov naming. -/
abbrev antiparticleProjector (K : SpinorEnd S) : SpinorEnd S :=
  InfoGeometry.Cartan.Pplus K

/-- The two projectors add to the identity. -/
theorem particleProjector_add_antiparticleProjector (K : SpinorEnd S) :
    particleProjector S K + antiparticleProjector S K = 1 := by
  rw [particleProjector, antiparticleProjector, add_comm]
  exact InfoGeometry.Cartan.Pplus_add_Pminus_eq_id K

/-- The particle projector is idempotent under the involution hypothesis. -/
theorem particleProjector_idempotent (K : SpinorEnd S) (hK : K * K = 1) :
    particleProjector S K * particleProjector S K = particleProjector S K := by
  exact InfoGeometry.Cartan.Pminus_idempotent K hK

/-- The antiparticle projector is idempotent under the involution hypothesis. -/
theorem antiparticleProjector_idempotent (K : SpinorEnd S) (hK : K * K = 1) :
    antiparticleProjector S K * antiparticleProjector S K = antiparticleProjector S K := by
  exact InfoGeometry.Cartan.Pplus_idempotent K hK

/-- The two Todorov projectors annihilate in one order. -/
theorem particle_antiparticle_orthogonal (K : SpinorEnd S) (hK : K * K = 1) :
    particleProjector S K * antiparticleProjector S K = 0 := by
  exact InfoGeometry.Cartan.Pminus_comp_Pplus K hK

/-- The two Todorov projectors annihilate in the opposite order. -/
theorem antiparticle_particle_orthogonal (K : SpinorEnd S) (hK : K * K = 1) :
    antiparticleProjector S K * particleProjector S K = 0 := by
  exact InfoGeometry.Cartan.Pplus_comp_Pminus K hK

/-- The involution acts by eigenvalue `-1` on the particle projector. -/
theorem involution_mul_particleProjector (K : SpinorEnd S) (hK : K * K = 1) :
    K * particleProjector S K = -particleProjector S K := by
  ext x
  have hKx := LinearMap.congr_fun hK x
  simp [particleProjector, InfoGeometry.Cartan.Pminus, sub_eq_add_neg] at hKx ⊢
  rw [hKx]

/-- The involution acts by eigenvalue `+1` on the antiparticle projector. -/
theorem involution_mul_antiparticleProjector (K : SpinorEnd S) (hK : K * K = 1) :
    K * antiparticleProjector S K = antiparticleProjector S K := by
  ext x
  have hKx := LinearMap.congr_fun hK x
  simp [antiparticleProjector, InfoGeometry.Cartan.Pplus] at hKx ⊢
  rw [hKx]
  module

/-- Pointwise particle-eigenspace readout. -/
theorem particleProjector_apply_eigen (K : SpinorEnd S) (hK : K * K = 1) (x : S) :
    K (particleProjector S K x) = -particleProjector S K x := by
  exact LinearMap.congr_fun (involution_mul_particleProjector S K hK) x

/-- Pointwise antiparticle-eigenspace readout. -/
theorem antiparticleProjector_apply_eigen (K : SpinorEnd S) (hK : K * K = 1) (x : S) :
    K (antiparticleProjector S K x) = antiparticleProjector S K x := by
  exact LinearMap.congr_fun (involution_mul_antiparticleProjector S K hK) x

/-- A linear equivalence commutes with an internal-space axis. -/
def CommutesWithEnd (K : SpinorEnd S) (g : S ≃ₗ[ℂ] S) : Prop :=
  ∀ x : S, g (K x) = K (g x)

/-- The subgroup preserving the internal-space axis `K`.  This is an abstract
version of the "preserves the volume-form/complex-structure" condition. -/
def linearCentralizer (K : SpinorEnd S) : Subgroup (S ≃ₗ[ℂ] S) where
  carrier := {g | CommutesWithEnd S K g}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro g h hg hh x
    calc
      (g * h) (K x) = g (h (K x)) := rfl
      _ = g (K (h x)) := by rw [hh]
      _ = K (g (h x)) := hg (h x)
      _ = K ((g * h) x) := rfl
  inv_mem' := by
    intro g hg x
    apply g.injective
    calc
      g (g⁻¹ (K x)) = K x := by simp
      _ = K (g (g⁻¹ x)) := by simp
      _ = g (K (g⁻¹ x)) := by rw [hg]

/-- Membership in the centralizer subgroup is exactly commutation with `K`. -/
theorem mem_linearCentralizer_iff (K : SpinorEnd S) (g : S ≃ₗ[ℂ] S) :
    g ∈ linearCentralizer S K ↔ CommutesWithEnd S K g :=
  Iff.rfl

/-- A symmetry commuting with `K` preserves the particle projector. -/
theorem commutesWithEnd_particleProjector (K : SpinorEnd S) (g : S ≃ₗ[ℂ] S)
    (hg : CommutesWithEnd S K g) (x : S) :
    g (particleProjector S K x) = particleProjector S K (g x) := by
  simp [particleProjector, InfoGeometry.Cartan.Pminus, sub_eq_add_neg]
  exact hg x

/-- A symmetry commuting with `K` preserves the antiparticle projector. -/
theorem commutesWithEnd_antiparticleProjector (K : SpinorEnd S) (g : S ≃ₗ[ℂ] S)
    (hg : CommutesWithEnd S K g) (x : S) :
    g (antiparticleProjector S K x) = antiparticleProjector S K (g x) := by
  simp [antiparticleProjector, InfoGeometry.Cartan.Pplus]
  exact hg x

/-- The stabilizer of a distinguished spinor, abstracting the paper's
"sterile-neutrino/Fock-vacuum stabilizer" condition without identifying it with
any concrete Standard Model gauge group.  This reuses Mathlib's group-action
stabilizer. -/
abbrev linearStabilizer (v : S) : Subgroup (S ≃ₗ[ℂ] S) :=
  MulAction.stabilizer (S ≃ₗ[ℂ] S) v

/-- Membership in the distinguished-spinor stabilizer. -/
theorem mem_linearStabilizer_iff (v : S) (g : S ≃ₗ[ℂ] S) :
    g ∈ linearStabilizer S v ↔ g v = v := by
  simp [linearStabilizer, MulAction.mem_stabilizer_iff]

/-- A compact packet for the Todorov projector algebra. -/
theorem todorov_projector_packet (K : SpinorEnd S) (hK : K * K = 1) :
    particleProjector S K + antiparticleProjector S K = 1 ∧
      particleProjector S K * particleProjector S K = particleProjector S K ∧
      antiparticleProjector S K * antiparticleProjector S K = antiparticleProjector S K ∧
      particleProjector S K * antiparticleProjector S K = 0 ∧
      antiparticleProjector S K * particleProjector S K = 0 := by
  exact ⟨particleProjector_add_antiparticleProjector S K,
    particleProjector_idempotent S K hK,
    antiparticleProjector_idempotent S K hK,
    particle_antiparticle_orthogonal S K hK,
    antiparticle_particle_orthogonal S K hK⟩

end InfoGeometry.Clifford.TodorovInternalSpace
