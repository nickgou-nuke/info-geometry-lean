/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

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

variable {K ι V : Type*} [Field K] [DecidableEq ι]
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

end Projectors

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

end InfoGeometry.Physics.NuclearSymmetrySectors
