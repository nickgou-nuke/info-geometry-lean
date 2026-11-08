import InfoGeometry.Canonical.V4GroupFourierTransform
import InfoGeometry.Thermo.Gibbs
import Mathlib.Tactic

open scoped BigOperators

/-!
# V₄ character resolution and gauge-normalized Gibbs weights

This bridge combines the native four-character Fourier transform on `V₄`
with the finite Gibbs owner.  The Fourier projectors resolve the identity on
real-valued functions on `V₄`; normalized Gibbs masses decompose in that same
character basis.  An additive energy shift is the log-coordinate form of a
positive Weyl rescaling of unnormalized Boltzmann weights.

The operator resolution here is the regular-function-space Fourier
resolution.  It is not identified with the separate Cuntz cylinder
resolution; no intertwiner between those two operator families is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.V4CharacterGibbsPoUBridge

open InfoGeometry.Canonical.V4GroupFourierTransform
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Topology.V4RootSystem.V4Group
open InfoGeometry.Thermo

/-! ## The order-four gauge factor -/

/-- The order of the native Klein four group, used as the Fourier gauge factor. -/
theorem v4_card : Fintype.card V4Group = 4 := by
  calc
    Fintype.card V4Group = Fintype.card (Fin 4) := Fintype.card_congr v4EquivFin.symm
    _ = 4 := Fintype.card_fin 4

/-- The Fourier normalization `1/4` is exactly `|V₄|⁻¹`. -/
theorem v4_card_inv : (1 / 4 : ℝ) = (Fintype.card V4Group : ℝ)⁻¹ := by
  rw [v4_card]
  norm_num

private theorem v4Fourier_add (k : Fin 4) (f h : V4Group → ℝ) :
    v4Fourier k (f + h) = v4Fourier k f + v4Fourier k h := by
  rw [v4Fourier_expansion k (f + h), v4Fourier_expansion k f,
    v4Fourier_expansion k h]
  simp only [Pi.add_apply]
  ring

private theorem v4Fourier_smul (k : Fin 4) (c : ℝ) (f : V4Group → ℝ) :
    v4Fourier k (c • f) = c * v4Fourier k f := by
  rw [v4Fourier_expansion k (c • f), v4Fourier_expansion k f]
  simp only [Pi.smul_apply]
  ring

/-- The normalized character projector on the regular function carrier. -/
def characterProjector (k : Fin 4) :
    (V4Group → ℝ) →ₗ[ℝ] (V4Group → ℝ) where
  toFun f g := (1 / 4 : ℝ) * v4Character k g * v4Fourier k f
  map_add' f h := by
    funext g
    change (1 / 4 : ℝ) * v4Character k g * v4Fourier k (f + h) = _
    rw [v4Fourier_add]
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext g
    change (1 / 4 : ℝ) * v4Character k g * v4Fourier k (c • f) = _
    rw [v4Fourier_smul]
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

/-- Pointwise formula displaying the group-order normalization of each
character projector. -/
theorem characterProjector_apply (k : Fin 4) (f : V4Group → ℝ) (g : V4Group) :
    characterProjector k f g =
      (Fintype.card V4Group : ℝ)⁻¹ * v4Character k g * v4Fourier k f := by
  change (1 / 4 : ℝ) * v4Character k g * v4Fourier k f = _
  rw [← v4_card_inv]

/-- Fourier transform of one character projector is diagonal in the character
basis, by the repository's character orthogonality theorem. -/
private theorem v4Fourier_characterProjector
    (k l : Fin 4) (f : V4Group → ℝ) :
    v4Fourier k (characterProjector l f) =
      if k = l then v4Fourier l f else 0 := by
  unfold v4Fourier characterProjector
  calc
    (∑ g : V4Group, v4Character k g *
        ((1 / 4 : ℝ) * v4Character l g * v4Fourier l f)) =
        ((1 / 4 : ℝ) * v4Fourier l f) *
          ∑ g : V4Group, v4Character k g * v4Character l g := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g hg
            ring
    _ = if k = l then v4Fourier l f else 0 := by
      rw [v4Character_pairwise_orthogonality]
      by_cases h : k = l
      · simp [h]
        ring
      · simp [h]

/-- Distinct character projectors are orthogonal; each projector is
idempotent. -/
theorem characterProjector_comp (k l : Fin 4) :
    (characterProjector k).comp (characterProjector l) =
      if k = l then characterProjector k else 0 := by
  apply LinearMap.ext
  intro f
  funext g
  change (1 / 4 : ℝ) * v4Character k g *
      v4Fourier k (characterProjector l f) = _
  rw [v4Fourier_characterProjector]
  by_cases h : k = l <;> simp [h, characterProjector]

/-- Each normalized character map is a projection. -/
theorem characterProjector_idempotent (k : Fin 4) :
    (characterProjector k).comp (characterProjector k) = characterProjector k := by
  rw [characterProjector_comp]
  simp

/-- Distinct normalized character maps have zero product. -/
theorem characterProjector_orthogonal {k l : Fin 4} (h : k ≠ l) :
    (characterProjector k).comp (characterProjector l) = 0 := by
  rw [characterProjector_comp]
  simp [h]

/-- The four character projectors sum to the identity operator. -/
theorem characterProjectors_sum_eq_id :
    (∑ k : Fin 4, characterProjector k) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext g
  change (∑ k : Fin 4,
      (1 / 4 : ℝ) * v4Character k g * v4Fourier k f) = f g
  calc
    _ = (1 / 4 : ℝ) *
        (∑ k : Fin 4, v4Character k g * v4Fourier k f) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
  _ = f g := v4Fourier_inversion f g

/-! ## Gibbs partition function in the character basis -/

/-- The finite Gibbs partition function on the four group elements. -/
def v4Partition (E : V4Group → ℝ) (ε : ℝ) : ℝ := Z E ε

/-- The normalized Gibbs mass on the four group elements. -/
def v4GibbsMass (E : V4Group → ℝ) (ε : ℝ) (g : V4Group) : ℝ :=
  gibbsProb E ε g

/-- Character coefficient of the normalized Gibbs distribution. -/
def gibbsCharacterCoefficient (E : V4Group → ℝ) (ε : ℝ) (k : Fin 4) : ℝ :=
  v4Fourier k (v4GibbsMass E ε)

/-- Character coefficient of the unnormalized Boltzmann weights. -/
def boltzmannCharacterCoefficient
    (E : V4Group → ℝ) (ε : ℝ) (k : Fin 4) : ℝ :=
  v4Fourier k (weight E ε)

/-- The partition function is the trivial-character coefficient of the
unnormalized Boltzmann weights. -/
theorem v4Partition_eq_trivialCharacterCoefficient
    (E : V4Group → ℝ) (ε : ℝ) :
    v4Partition E ε = boltzmannCharacterCoefficient E ε 0 := by
  unfold v4Partition boltzmannCharacterCoefficient v4Fourier Z weight
  simp [v4Character]

/-- Character decomposition reconstructs each unnormalized Boltzmann weight
with the reciprocal group-order factor. -/
theorem boltzmannWeight_character_expansion
    (E : V4Group → ℝ) (ε : ℝ) (g : V4Group) :
    weight E ε g = (Fintype.card V4Group : ℝ)⁻¹ *
      ∑ k : Fin 4, v4Character k g * boltzmannCharacterCoefficient E ε k := by
  rw [← v4_card_inv]
  symm
  exact v4Fourier_inversion (weight E ε) g

/-- Gibbs masses are a probability partition of unity on `V₄`. -/
theorem v4GibbsMass_sum_one (E : V4Group → ℝ) (ε : ℝ) :
    ∑ g : V4Group, v4GibbsMass E ε g = 1 :=
  gibbsProb_sum_one E ε

/-- Character inversion reconstructs each Gibbs mass from its four Fourier modes. -/
theorem v4GibbsMass_character_expansion
    (E : V4Group → ℝ) (ε : ℝ) (g : V4Group) :
    v4GibbsMass E ε g =
      (1 / 4 : ℝ) * ∑ k : Fin 4,
        v4Character k g * gibbsCharacterCoefficient E ε k := by
  symm
  exact v4Fourier_inversion (v4GibbsMass E ε) g

/-- Adding a constant to every energy scales the partition function by its
Boltzmann factor. -/
theorem v4Partition_add_constant (E : V4Group → ℝ) (c ε : ℝ) :
    v4Partition (fun g => E g + c) ε =
      Real.exp (-c / ε) * v4Partition E ε :=
  Z_add_constant E c ε

/-- The normalized Gibbs distribution is invariant under a common energy
offset, the finite Gibbs form of Weyl gauge invariance. -/
theorem v4GibbsMass_add_constant_invariant
    (E : V4Group → ℝ) (c ε : ℝ) (hε : ε ≠ 0) (g : V4Group) :
    v4GibbsMass (fun h => E h + c) ε g = v4GibbsMass E ε g :=
  gibbsProb_add_constant_invariant E c ε hε g

/-- The uniform, zero-energy ensemble has partition function `|V₄| = 4`. -/
theorem zeroEnergy_partition_eq_card :
    v4Partition (fun _ : V4Group => 0) 1 = (Fintype.card V4Group : ℝ) := by
  classical
  unfold v4Partition Z weight
  calc
    (∑ g : V4Group, Real.exp (-(0 : ℝ) / 1)) =
        ∑ _g : V4Group, (1 : ℝ) := by simp
    _ = (Fintype.card V4Group : ℝ) := by simp

/-- At zero energy, each group element receives the reciprocal group-order
weight, and the four weights sum to one. -/
theorem zeroEnergy_gibbsMass_eq_inv_card (g : V4Group) :
    v4GibbsMass (fun _ : V4Group => 0) 1 g =
      (Fintype.card V4Group : ℝ)⁻¹ := by
  rw [show v4GibbsMass (fun _ : V4Group => 0) 1 g =
      Real.exp (-(0 : ℝ) / 1) / v4Partition (fun _ : V4Group => 0) 1 by
        simp [v4GibbsMass, gibbsProb, weight, v4Partition]]
  rw [zeroEnergy_partition_eq_card]
  norm_num

/-- The uniform Gibbs mass is exactly the inverse group order. -/
theorem zeroEnergy_gibbsMass_eq_one_fourth (g : V4Group) :
    v4GibbsMass (fun _ : V4Group => 0) 1 g = 1 / 4 := by
  rw [zeroEnergy_gibbsMass_eq_inv_card, v4_card]
  norm_num

/-- Combined finite PoU: character operators resolve the identity, and the
gauge-fixed Gibbs vector has total mass one. -/
theorem character_resolution_and_gibbs_normalization
    (E : V4Group → ℝ) (ε : ℝ) :
    (∑ k : Fin 4, characterProjector k) = LinearMap.id ∧
      ∑ g : V4Group, v4GibbsMass E ε g = 1 :=
  ⟨characterProjectors_sum_eq_id, v4GibbsMass_sum_one E ε⟩

end InfoGeometry.Canonical.V4CharacterGibbsPoUBridge

end noncomputable section
