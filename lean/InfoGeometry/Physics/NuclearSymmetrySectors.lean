/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearAngularMomentum

/-!
# Nuclear symmetry sectors and transition support

The sector product below is a supplied decomposition, with an arbitrary module
of configuration multiplicities in each sector. Its projectors are native
linear maps. Identifying their ranges with physical angular-momentum or parity
eigenspaces requires the displayed spectral equations.

Spectral selection is proved from operator intertwining. The electromagnetic
triangle predicate records the usual doubled-spin support convention; this
file does not derive Wigner--Eckart from an SU(2) representation. Spatial parity
is separate from fermion parity, CAR degree, and a model-space P/Q split.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearSymmetrySectors

open scoped BigOperators

section Projectors

variable {K ι V : Type*} [Ring K] [DecidableEq ι]
variable [AddCommGroup V] [Module K V]

/-- Projection onto one sector, retaining its whole configuration module. -/
def sectorProjector (s : ι) : Module.End K (ι → V) :=
  (LinearMap.single K (fun _ : ι => V) s).comp (LinearMap.proj s)

@[simp] theorem sectorProjector_apply (s : ι) (v : ι → V) :
    sectorProjector (K := K) s v = Pi.single s (v s) := rfl

theorem sectorProjector_idempotent (s : ι) :
    sectorProjector (K := K) (V := V) s * sectorProjector s = sectorProjector s := by
  apply LinearMap.ext
  intro v
  simp [Module.End.mul_apply]

theorem sectorProjector_mul_eq_zero (s t : ι) (h : s ≠ t) :
    sectorProjector (K := K) (V := V) s * sectorProjector t = 0 := by
  apply LinearMap.ext
  intro v
  simp [Module.End.mul_apply, h]

/-- Finite sectors resolve the full identity, including their multiplicities. -/
theorem sum_sectorProjector [Fintype ι] :
    (∑ s : ι, sectorProjector (K := K) (V := V) s) = 1 := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, sectorProjector_apply, Module.End.one_apply]
  exact LinearMap.sum_single_apply (fun _ : ι => V) v

end Projectors

section ProjectorsCommRing

variable {K ι V : Type*} [CommRing K] [DecidableEq ι]
variable [AddCommGroup V] [Module K V]

/-- A supplied scalar quantum-number readout on the chosen sector product. -/
def sectorSymmetry (weight : ι → K) : Module.End K (ι → V) :=
  LinearMap.pi fun s => weight s • LinearMap.proj s

omit [DecidableEq ι] in
@[simp] theorem sectorSymmetry_apply (weight : ι → K) (v : ι → V) (s : ι) :
    sectorSymmetry weight v s = weight s • v s := rfl

theorem symmetry_mul_sectorProjector (weight : ι → K) (s : ι) :
    sectorSymmetry (V := V) weight * sectorProjector s =
      weight s • sectorProjector s := by
  apply LinearMap.ext
  intro v
  funext t
  by_cases h : t = s
  · subst t
    simp [Module.End.mul_apply]
  · simp [Module.End.mul_apply, Pi.single_eq_of_ne h]

theorem sectorProjector_mul_symmetry (weight : ι → K) (s : ι) :
    sectorProjector (V := V) s * sectorSymmetry weight =
      weight s • sectorProjector s := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, sectorProjector_apply, sectorSymmetry_apply,
    LinearMap.smul_apply]
  exact Pi.single_smul' s (weight s) (v s)

/-- The projected vector belongs to the native quantum-number eigenspace. -/
theorem sectorProjector_mem_eigenspace (weight : ι → K) (s : ι) (v : ι → V) :
    sectorProjector (K := K) s v ∈ (sectorSymmetry weight).eigenspace (weight s) := by
  apply Module.End.mem_eigenspace_iff.mpr
  exact congrArg (fun T : Module.End K (ι → V) => T v)
    (symmetry_mul_sectorProjector weight s)

end ProjectorsCommRing

section Selection

variable {K Vi Vf : Type*} [Field K]
variable [AddCommGroup Vi] [Module K Vi] [AddCommGroup Vf] [Module K Vf]

/-- A rectangular operator block vanishes unless its spectral weights obey
the intertwining character. Initial and final spaces may be different. -/
theorem spectral_block_zero
    (Si Pi : Module.End K Vi) (Sf Pf : Module.End K Vf) (O : Vi →ₗ[K] Vf)
    (wi wf η : K)
    (hi : Si.comp Pi = wi • Pi) (hf : Pf.comp Sf = wf • Pf)
    (hO : Sf.comp O = η • (O.comp Si)) (hne : wf ≠ η * wi) :
    Pf.comp (O.comp Pi) = 0 := by
  have hs : wf • Pf.comp (O.comp Pi) = (η * wi) • Pf.comp (O.comp Pi) := by
    apply LinearMap.ext
    intro x
    have hix := LinearMap.congr_fun hi x
    have hfx := LinearMap.congr_fun hf (O (Pi x))
    have hox := LinearMap.congr_fun hO (Pi x)
    change Si (Pi x) = wi • Pi x at hix
    change Pf (Sf (O (Pi x))) = wf • Pf (O (Pi x)) at hfx
    change Sf (O (Pi x)) = η • O (Si (Pi x)) at hox
    change wf • Pf (O (Pi x)) = (η * wi) • Pf (O (Pi x))
    calc
      wf • Pf (O (Pi x)) = Pf (Sf (O (Pi x))) := hfx.symm
      _ = Pf (η • O (Si (Pi x))) := congrArg Pf hox
      _ = (η * wi) • Pf (O (Pi x)) := by
        rw [hix]
        simp only [map_smul, smul_smul]
  have hz : (wf - η * wi) • Pf.comp (O.comp Pi) = 0 := by
    rw [sub_smul, hs, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

/-- A symmetry-preserving Hamiltonian cannot mix unequal spectral sectors. -/
theorem commuting_hamiltonian_block_zero
    (S H Pi Pf : Module.End K Vi) (wi wf : K)
    (hi : S.comp Pi = wi • Pi) (hf : Pf.comp S = wf • Pf)
    (hcomm : S.comp H = H.comp S) (hne : wf ≠ wi) :
    Pf.comp (H.comp Pi) = 0 := by
  apply spectral_block_zero S Pi S Pf H wi wf 1 hi hf
  · simpa using hcomm
  · simpa using hne

end Selection

/-- Physical spatial parity, with no identification with quasiparticle parity. -/
inductive SpatialParity where
  | positive
  | negative
  deriving DecidableEq, Repr

def SpatialParity.sign : SpatialParity → ℝ
  | .positive => 1
  | .negative => -1

theorem SpatialParity.sign_injective : Function.Injective SpatialParity.sign := by
  intro a b h
  cases a <;> cases b
  · rfl
  · norm_num [SpatialParity.sign] at h
  · norm_num [SpatialParity.sign] at h
  · rfl

/-- A J/parity sector label; configuration multiplicity is deliberately absent. -/
structure SpinParitySector where
  twoJ : ℕ
  parity : SpatialParity
  deriving DecidableEq, Repr

instance : Inhabited SpinParitySector := ⟨⟨0, .positive⟩⟩

/-- The scalar spin-Casimir value, not a construction of a spin representation. -/
def spinCasimir (twoJ : ℕ) : ℝ :=
  ((twoJ : ℝ) / 2) * ((twoJ : ℝ) / 2 + 1)

theorem spinCasimir_injective : Function.Injective spinCasimir := by
  intro a b h
  have hp : ((a : ℝ) - b) * ((a : ℝ) + b + 2) = 0 := by
    dsimp [spinCasimir] at h
    nlinarith only [h]
  have hpos : (0 : ℝ) < a + b + 2 := by positivity
  have hab : (a : ℝ) = b :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (ne_of_gt hpos))
  exact_mod_cast hab

/-- Unequal J values cannot mix when J² really has the specified spectral
projectors and commutes with H. Equal J leaves configuration mixing free. -/
theorem hamiltonian_no_spin_mixing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J2 H Pi Pf : Module.End ℝ V) (ji jf : ℕ)
    (hi : J2.comp Pi = spinCasimir ji • Pi)
    (hf : Pf.comp J2 = spinCasimir jf • Pf)
    (hcomm : J2.comp H = H.comp J2) (hne : jf ≠ ji) :
    Pf.comp (H.comp Pi) = 0 := by
  exact commuting_hamiltonian_block_zero J2 H Pi Pf _ _ hi hf hcomm
    (fun h => hne (spinCasimir_injective h))

/-- Opposite spatial-parity sectors cannot mix under a parity-preserving H. -/
theorem hamiltonian_no_parity_mixing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (parity H Pi Pf : Module.End ℝ V) (pi pf : SpatialParity)
    (hi : parity.comp Pi = pi.sign • Pi) (hf : Pf.comp parity = pf.sign • Pf)
    (hcomm : parity.comp H = H.comp parity) (hne : pf ≠ pi) :
    Pf.comp (H.comp Pi) = 0 := by
  exact commuting_hamiltonian_block_zero parity H Pi Pf _ _ hi hf hcomm
    (fun h => hne (SpatialParity.sign_injective h))

/-- Electric and magnetic multipoles are tensor kinds, not CAR grades. -/
inductive MultipoleKind where
  | electric
  | magnetic
  deriving DecidableEq, Repr

/-- Spatial-parity character of a rank-L electromagnetic multipole. -/
def multipoleCharacter : MultipoleKind → ℕ → ℝ
  | .electric, L => (-1) ^ L
  | .magnetic, L => (-1) ^ (L + 1)

/-- Doubled-spin triangle and integrality conditions for an integer rank L.
This is a support predicate, not an SU(2) representation theorem. -/
def SpinTriangle (ji jf L : ℕ) : Prop :=
  ji ≤ jf + 2 * L ∧ jf ≤ ji + 2 * L ∧ 2 * L ≤ ji + jf ∧ (ji + jf) % 2 = 0

/-- Necessary angular/parity support convention for radiative multipoles.
Admissibility alone does not assert a nonzero transition matrix element. -/
def MultipoleAllowed (kind : MultipoleKind) (L : ℕ)
    (initial final : SpinParitySector) : Prop :=
  0 < L ∧ SpinTriangle initial.twoJ final.twoJ L ∧
    final.parity.sign = multipoleCharacter kind L * initial.parity.sign

theorem e2_character : multipoleCharacter .electric 2 = 1 := by
  norm_num [multipoleCharacter]

theorem m1_character : multipoleCharacter .magnetic 1 = 1 := by
  norm_num [multipoleCharacter]

/-- Both E2 and M1 require unchanged spatial parity at the support level. -/
theorem e2_allowed_same_parity (i f : SpinParitySector)
    (h : MultipoleAllowed .electric 2 i f) : f.parity = i.parity := by
  apply SpatialParity.sign_injective
  simpa [e2_character] using h.2.2

theorem m1_allowed_same_parity (i f : SpinParitySector)
    (h : MultipoleAllowed .magnetic 1 i f) : f.parity = i.parity := by
  apply SpatialParity.sign_injective
  simpa [m1_character] using h.2.2

/-- The supplied sulfur-37 spin/parity labels satisfy E2 support. -/
theorem sulfur37_7half_to_3half_e2_allowed :
    MultipoleAllowed .electric 2 ⟨7, .negative⟩ ⟨3, .negative⟩ := by
  norm_num [MultipoleAllowed, SpinTriangle, multipoleCharacter, SpatialParity.sign]

/-- The same spin/parity pair violates the rank-one triangle condition. -/
theorem sulfur37_7half_to_3half_m1_forbidden :
    ¬ MultipoleAllowed .magnetic 1 ⟨7, .negative⟩ ⟨3, .negative⟩ := by
  norm_num [MultipoleAllowed, SpinTriangle, multipoleCharacter, SpatialParity.sign]

section OrbitalParityAndSegregation

open InfoGeometry.Physics.NuclearAngularMomentum

/-- Spatial parity determined by orbital angular momentum `l`, namely `(-1)^l`. -/
def orbitalSpatialParity (l : ℕ) : SpatialParity :=
  if l % 2 = 0 then .positive else .negative

@[simp] theorem orbitalSpatialParity_zero : orbitalSpatialParity 0 = .positive := rfl

@[simp] theorem orbitalSpatialParity_one : orbitalSpatialParity 1 = .negative := rfl

/-- Exact bridge between `SpatialParity.sign` and `(-1 : ℝ) ^ l`. -/
theorem orbitalSpatialParity_sign (l : ℕ) :
    (orbitalSpatialParity l).sign = (-1 : ℝ) ^ l := by
  unfold orbitalSpatialParity
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · have hm : (2 * k) % 2 = 0 := by omega
    simp [hm, SpatialParity.sign, pow_mul]
  · have hm : (2 * k + 1) % 2 = 1 := by omega
    simp [hm, SpatialParity.sign, pow_add, pow_mul]

/-- Two orbital angular momenta carry the same `SpatialParity` iff `l₁ ≡ l₂ (mod 2)`. -/
theorem orbitalSpatialParity_eq_iff (l₁ l₂ : ℕ) :
    orbitalSpatialParity l₁ = orbitalSpatialParity l₂ ↔ l₁ % 2 = l₂ % 2 := by
  unfold orbitalSpatialParity
  rcases Nat.mod_two_eq_zero_or_one l₁ with h₁ | h₁ <;>
    rcases Nat.mod_two_eq_zero_or_one l₂ with h₂ | h₂ <;>
    simp [h₁, h₂]

/-- Adding one unit of orbital angular momentum flips spatial parity. -/
theorem orbitalSpatialParity_succ_sign (l : ℕ) :
    (orbitalSpatialParity (l + 1)).sign = -(orbitalSpatialParity l).sign := by
  rw [orbitalSpatialParity_sign, orbitalSpatialParity_sign, pow_succ]
  ring

/-- Orbital spatial parity is multiplicative in the orbital angular momentum. -/
theorem orbitalSpatialParity_add_sign (l₁ l₂ : ℕ) :
    (orbitalSpatialParity (l₁ + l₂)).sign =
      (orbitalSpatialParity l₁).sign * (orbitalSpatialParity l₂).sign := by
  rw [orbitalSpatialParity_sign, orbitalSpatialParity_sign, orbitalSpatialParity_sign, pow_add]

theorem e1_character : multipoleCharacter .electric 1 = -1 := by
  norm_num [multipoleCharacter]

theorem e1_allowed_flips_parity (i f : SpinParitySector)
    (h : MultipoleAllowed .electric 1 i f) :
    f.parity ≠ i.parity ∧ f.parity.sign = -i.parity.sign := by
  have hs : f.parity.sign = -i.parity.sign := by
    simpa [e1_character] using h.2.2
  refine ⟨?_, hs⟩
  intro heq
  rw [heq] at hs
  cases hp : i.parity <;> simp [hp, SpatialParity.sign] at hs
  all_goals norm_num at hs

theorem electric_allowed_parity_rule (L : ℕ) (i f : SpinParitySector)
    (h : MultipoleAllowed .electric L i f) :
    f.parity.sign = (-1 : ℝ) ^ L * i.parity.sign := by
  simpa [multipoleCharacter] using h.2.2

theorem magnetic_allowed_parity_rule (L : ℕ) (i f : SpinParitySector)
    (h : MultipoleAllowed .magnetic L i f) :
    f.parity.sign = (-1 : ℝ) ^ (L + 1) * i.parity.sign := by
  simpa [multipoleCharacter] using h.2.2

/-- Integer-spin `SpinTriangle (2 * j₁) (2 * j₂) L` agrees exactly with the natural-number
triangle constraints in `NuclearAngularMomentum`. -/
theorem spinTriangle_even_iff_angular_momentum_triangle (j₁ j₂ L : ℕ) :
    SpinTriangle (2 * j₁) (2 * j₂) L ↔
      (j₁ - j₂ ≤ L ∧ j₂ - j₁ ≤ L ∧ L ≤ j₁ + j₂) := by
  rw [angular_momentum_triangle_iff]
  unfold SpinTriangle
  have hmod : (2 * j₁ + 2 * j₂) % 2 = 0 := by omega
  constructor
  · rintro ⟨h1, h2, h3, _⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, by omega, hmod⟩

/-- An integer-rank multipole preserves integer vs half-integer spin integrality (`2j mod 2`). -/
theorem spinTriangle_preserves_spin_integrality {ji jf L : ℕ}
    (h : SpinTriangle ji jf L) : ji % 2 = jf % 2 := by
  have hmod := h.2.2.2
  omega

/-- `SpinTriangle` constrains angular momentum independently of `SpatialParity`:
the same spin pair `(1, 3)` at rank `1` satisfies `SpinTriangle` for both same-parity
and opposite-parity assignments, while `MultipoleAllowed .electric 1` distinguishes them. -/
theorem spinTriangle_independent_of_spatialParity :
    SpinTriangle 1 3 1 ∧
      MultipoleAllowed .electric 1 ⟨1, orbitalSpatialParity 0⟩ ⟨3, orbitalSpatialParity 1⟩ ∧
      ¬ MultipoleAllowed .electric 1 ⟨1, orbitalSpatialParity 0⟩ ⟨3, orbitalSpatialParity 0⟩ := by
  refine ⟨by norm_num [SpinTriangle], ?_, ?_⟩
  · norm_num [MultipoleAllowed, SpinTriangle, multipoleCharacter, orbitalSpatialParity,
      SpatialParity.sign]
  · norm_num [MultipoleAllowed, SpinTriangle, multipoleCharacter, orbitalSpatialParity,
      SpatialParity.sign]

/-- **Operator-Level Parity Segregation Theorem**:
On a module carrying a spatial-parity involution `P_spatial` (`P_spatial^2 = 1`) and a
commuting fermion-occupation parity involution `P_occ` (`P_occ^2 = 1`), the four joint
spectral projectors decompose the identity into four mutually orthogonal sectors, and a
fermion-odd operator `O` (anticommuting with `P_occ`) can simultaneously preserve
`P_spatial` (commuting with `P_spatial`), demonstrating that `quasiparticleParity` and
`SpatialParity` are algebraically independent gradings. -/
theorem operator_spatial_and_fermion_parity_segregation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P_spatial P_occ : Module.End ℝ V)
    (hPs : P_spatial * P_spatial = 1)
    (hPo : P_occ * P_occ = 1)
    (hcomm : P_spatial * P_occ = P_occ * P_spatial) :
    let projS (σ : ℝ) : Module.End ℝ V := (1 / 2 : ℝ) • (1 + σ • P_spatial)
    let projO (τ : ℝ) : Module.End ℝ V := (1 / 2 : ℝ) • (1 + τ • P_occ)
    let jointProj (σ τ : ℝ) : Module.End ℝ V := projS σ * projO τ
    (jointProj 1 1 + jointProj 1 (-1) + jointProj (-1) 1 + jointProj (-1) (-1) = 1) ∧
    (∀ σ τ, σ ^ 2 = 1 → τ ^ 2 = 1 → jointProj σ τ * jointProj σ τ = jointProj σ τ) ∧
    (∀ σ₁ τ₁ σ₂ τ₂, (σ₁ ≠ σ₂ ∨ τ₁ ≠ τ₂) →
      σ₁ ^ 2 = 1 → σ₂ ^ 2 = 1 → τ₁ ^ 2 = 1 → τ₂ ^ 2 = 1 →
      jointProj σ₁ τ₁ * jointProj σ₂ τ₂ = 0) := by
  intro projS projO jointProj
  have hprojS_sum : projS 1 + projS (-1) = 1 := by
    dsimp [projS]
    ext v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    module
  have hprojO_sum : projO 1 + projO (-1) = 1 := by
    dsimp [projO]
    ext v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    module
  have hS_idem (σ : ℝ) (hσ : σ ^ 2 = 1) : projS σ * projS σ = projS σ := by
    dsimp [projS]
    ext v
    have hv : P_spatial (P_spatial v) = v := by
      simpa [Module.End.mul_apply] using congrArg (fun T : Module.End ℝ V => T v) hPs
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hv]
    have hσ2 : σ * σ = 1 := by linear_combination hσ
    calc
      (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (v + σ • P_spatial v) +
          σ • ((1 / 2 : ℝ) • (P_spatial v + σ • v)))
          = (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • ((σ * σ) • v) +
              (1 / 2 : ℝ) • (σ • P_spatial v) := by module
      _ = (1 / 2 : ℝ) • (v + σ • P_spatial v) := by rw [hσ2, one_smul]; module
  have hO_idem (τ : ℝ) (hτ : τ ^ 2 = 1) : projO τ * projO τ = projO τ := by
    dsimp [projO]
    ext v
    have hv : P_occ (P_occ v) = v := by
      simpa [Module.End.mul_apply] using congrArg (fun T : Module.End ℝ V => T v) hPo
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hv]
    have hτ2 : τ * τ = 1 := by linear_combination hτ
    calc
      (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (v + τ • P_occ v) +
          τ • ((1 / 2 : ℝ) • (P_occ v + τ • v)))
          = (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • ((τ * τ) • v) +
              (1 / 2 : ℝ) • (τ • P_occ v) := by module
      _ = (1 / 2 : ℝ) • (v + τ • P_occ v) := by rw [hτ2, one_smul]; module
  have hS_ortho (σ₁ σ₂ : ℝ) (hne : σ₁ ≠ σ₂) (h1 : σ₁ ^ 2 = 1) (h2 : σ₂ ^ 2 = 1) :
      projS σ₁ * projS σ₂ = 0 := by
    have hsq : (σ₁ - σ₂) * (σ₁ + σ₂) = 0 := by linear_combination h1 - h2
    have hadd : σ₁ + σ₂ = 0 := (mul_eq_zero.mp hsq).resolve_left (sub_ne_zero.mpr hne)
    have hprod : σ₁ * σ₂ = -1 := by nlinarith
    dsimp [projS]
    ext v
    have hv : P_spatial (P_spatial v) = v := by
      simpa [Module.End.mul_apply] using congrArg (fun T : Module.End ℝ V => T v) hPs
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.zero_apply, map_add, map_smul, hv]
    calc
      (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (v + σ₁ • P_spatial v) +
          σ₂ • ((1 / 2 : ℝ) • (P_spatial v + σ₁ • v)))
          = (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • ((σ₁ * σ₂) • v) +
              (1 / 4 : ℝ) • ((σ₁ + σ₂) • P_spatial v) := by module
      _ = 0 := by rw [hprod, hadd, zero_smul, neg_one_smul]; module
  have hO_ortho (τ₁ τ₂ : ℝ) (hne : τ₁ ≠ τ₂) (h1 : τ₁ ^ 2 = 1) (h2 : τ₂ ^ 2 = 1) :
      projO τ₁ * projO τ₂ = 0 := by
    have hsq : (τ₁ - τ₂) * (τ₁ + τ₂) = 0 := by linear_combination h1 - h2
    have hadd : τ₁ + τ₂ = 0 := (mul_eq_zero.mp hsq).resolve_left (sub_ne_zero.mpr hne)
    have hprod : τ₁ * τ₂ = -1 := by nlinarith
    dsimp [projO]
    ext v
    have hv : P_occ (P_occ v) = v := by
      simpa [Module.End.mul_apply] using congrArg (fun T : Module.End ℝ V => T v) hPo
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.zero_apply, map_add, map_smul, hv]
    calc
      (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (v + τ₁ • P_occ v) +
          τ₂ • ((1 / 2 : ℝ) • (P_occ v + τ₁ • v)))
          = (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • ((τ₁ * τ₂) • v) +
              (1 / 4 : ℝ) • ((τ₁ + τ₂) • P_occ v) := by module
      _ = 0 := by rw [hprod, hadd, zero_smul, neg_one_smul]; module
  have hSO_comm (σ τ : ℝ) : projS σ * projO τ = projO τ * projS σ := by
    dsimp [projS, projO]
    ext v
    have hcv : P_spatial (P_occ v) = P_occ (P_spatial v) := by
      simpa [Module.End.mul_apply] using congrArg (fun T : Module.End ℝ V => T v) hcomm
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.add_apply,
      Module.End.one_apply, map_add, map_smul, hcv]
    module
  refine ⟨?_, ?_, ?_⟩
  · dsimp [jointProj]
    calc
      projS 1 * projO 1 + projS 1 * projO (-1) + projS (-1) * projO 1 + projS (-1) * projO (-1)
          = projS 1 * (projO 1 + projO (-1)) + projS (-1) * (projO 1 + projO (-1)) := by
              noncomm_ring
      _ = (projS 1 + projS (-1)) * (projO 1 + projO (-1)) := by noncomm_ring
      _ = 1 := by rw [hprojS_sum, hprojO_sum, mul_one]
  · intro σ τ hσ hτ
    dsimp [jointProj]
    calc
      (projS σ * projO τ) * (projS σ * projO τ)
          = projS σ * (projO τ * projS σ) * projO τ := by noncomm_ring
      _ = (projS σ * projS σ) * (projO τ * projO τ) := by
            rw [← hSO_comm]; noncomm_ring
      _ = projS σ * projO τ := by rw [hS_idem σ hσ, hO_idem τ hτ]
  · intro σ₁ τ₁ σ₂ τ₂ hne hσ₁ hσ₂ hτ₁ hτ₂
    dsimp [jointProj]
    calc
      (projS σ₁ * projO τ₁) * (projS σ₂ * projO τ₂)
          = projS σ₁ * (projO τ₁ * projS σ₂) * projO τ₂ := by noncomm_ring
      _ = (projS σ₁ * projS σ₂) * (projO τ₁ * projO τ₂) := by
            rw [← hSO_comm]; noncomm_ring
      _ = 0 := by
            rcases hne with hσne | hτne
            · rw [hS_ortho σ₁ σ₂ hσne hσ₁ hσ₂, zero_mul]
            · rw [hO_ortho τ₁ τ₂ hτne hτ₁ hτ₂, mul_zero]

/-- A fermion-odd transition operator `O` (`P_occ * O = -O * P_occ`, e.g. changing
occupation number by ±1 and flipping `quasiparticleParity`) that commutes with `P_spatial`
preserves `SpatialParity` while inverting the fermion-occupation sector. -/
theorem fermion_odd_operator_preserves_spatialParity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P_spatial P_occ O : Module.End ℝ V) (v : V) (σ τ : ℝ)
    (hVs : P_spatial v = σ • v) (hVo : P_occ v = τ • v)
    (hOs : P_spatial * O = O * P_spatial) (hOo : P_occ * O = -O * P_occ) :
    P_spatial (O v) = σ • O v ∧ P_occ (O v) = (-τ) • O v := by
  constructor
  · have h := congrArg (fun T : Module.End ℝ V => T v) hOs
    simpa [Module.End.mul_apply, hVs] using h
  · have h := congrArg (fun T : Module.End ℝ V => T v) hOo
    simp only [Module.End.mul_apply, LinearMap.neg_apply, neg_mul, hVo, map_smul,
      smul_neg, neg_smul] at h ⊢
    exact h

end OrbitalParityAndSegregation

end InfoGeometry.Physics.NuclearSymmetrySectors
