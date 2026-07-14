/-
InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean

Chiral packing energy for crossover residue audits.

This module formalizes the admissible mathematical content:

* chirality has a sign;
* same-chirality bonds have lower pair energy than opposite-chirality bonds
  when the packing coupling is positive;
* curvature coupling changes sign under chirality flip;
* a finite Hawking-point divisor can be audited against a global orientation;
* a formal reorientation operation preserves the projective ray and weight while
  changing the chiral label.

No claim is made that biological membranes contain literal Majorana zero modes.
No Navier-Stokes regularity theorem is asserted.
No ethical claim is encoded.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.CrossoverResidue
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace ChiralPackingEnergy

open InfoGeometry.OperatorAlgebra.CrossoverResidue
open InfoGeometry.OperatorAlgebra.ConformalCrossover

/-! ## 1. Real sign of chirality -/

/-- Real-valued chiral sign. This is useful for energy functionals. -/
def chiralityRealSign (χ : Chirality) : ℝ :=
  (Chirality.sign χ : ℝ)

@[simp]
theorem chiralityRealSign_left :
    chiralityRealSign Chirality.left = 1 := by
  norm_num [chiralityRealSign, Chirality.sign]

@[simp]
theorem chiralityRealSign_right :
    chiralityRealSign Chirality.right = -1 := by
  norm_num [chiralityRealSign, Chirality.sign]

@[simp]
theorem chiralityRealSign_flip
    (χ : Chirality) :
    chiralityRealSign (Chirality.flip χ) = -chiralityRealSign χ := by
  cases χ <;> norm_num [chiralityRealSign, Chirality.sign, Chirality.flip]

@[simp]
theorem chiralityRealSign_sq
    (χ : Chirality) :
    chiralityRealSign χ * chiralityRealSign χ = 1 := by
  cases χ <;> norm_num [chiralityRealSign, Chirality.sign]

@[simp]
theorem chiralityRealSign_mul_flip
    (χ : Chirality) :
    chiralityRealSign χ * chiralityRealSign (Chirality.flip χ) = -1 := by
  cases χ <;> norm_num [chiralityRealSign, Chirality.sign, Chirality.flip]

/-! ## 2. Chiral packing Hamiltonian -/

/--
A finite chiral packing Hamiltonian.

`Site` is an abstract lattice/site type. No metric structure is required unless
a later geometric model needs distances.

The energy terms are:

* exchange packing: `-J χᵢχⱼ`;
* curvature coupling: `Γ κᵢ χᵢ`.

The topological/quench condition is represented by `thermalNoise < couplingJ`.
-/
structure ChiralPackingHamiltonian
    (Site : Type*) where
  /-- Like-chirality packing strength. -/
  couplingJ : ℝ
  /-- Curvature/chirality coupling. -/
  curvatureCoupling : ℝ
  /-- Effective local curvature or geometric bias. -/
  curvature : Site → ℝ
  /-- Thermal/noise scale opposing chiral ordering. -/
  thermalNoise : ℝ
  /-- Preferred global orientation for the quench. -/
  globalOrientation : Chirality

namespace ChiralPackingHamiltonian

variable {Site : Type*}
variable (H : ChiralPackingHamiltonian Site)

/-- Pair packing energy: `E_pair(χᵢ,χⱼ) = -J χᵢ χⱼ`. -/
def pairEnergy
    (chiI chiJ : Chirality) : ℝ :=
  -H.couplingJ * chiralityRealSign chiI * chiralityRealSign chiJ

/-- Local curvature energy: `E_curv(i,χ) = Γ κ(i) χ`. -/
def curvatureEnergy
    (i : Site)
    (χ : Chirality) : ℝ :=
  H.curvatureCoupling * H.curvature i * chiralityRealSign χ

/-- The quench/topological ordering condition. -/
def IsTopologicalPhase : Prop :=
  H.thermalNoise < H.couplingJ

/--
If thermal noise is nonnegative and the system is in the topological phase,
then the same-chirality coupling is positive.
-/
theorem couplingJ_pos_of_topological
    (hnoise : 0 ≤ H.thermalNoise)
    (hphase : H.IsTopologicalPhase) :
    0 < H.couplingJ := by
  unfold IsTopologicalPhase at hphase
  linarith

/-- Same-chirality pair energy is `-J`. -/
theorem pairEnergy_same
    (χ : Chirality) :
    H.pairEnergy χ χ = -H.couplingJ := by
  cases χ <;> simp [pairEnergy, chiralityRealSign, Chirality.sign]

/-- Opposite-chirality pair energy is `J`. -/
theorem pairEnergy_opposite
    (χ : Chirality) :
    H.pairEnergy χ (Chirality.flip χ) = H.couplingJ := by
  cases χ <;>
    simp [pairEnergy, chiralityRealSign, Chirality.sign, Chirality.flip]

/--
Positive packing coupling makes same-chirality neighbors energetically cheaper
than opposite-chirality neighbors.
-/
theorem same_chirality_energy_lt_opposite
    (hJ : 0 < H.couplingJ)
    (χ : Chirality) :
    H.pairEnergy χ χ <
      H.pairEnergy χ (Chirality.flip χ) := by
  rw [H.pairEnergy_same χ, H.pairEnergy_opposite χ]
  linarith

/-- Curvature energy changes sign under chirality flip. -/
theorem curvatureEnergy_flip
    (i : Site)
    (χ : Chirality) :
    H.curvatureEnergy i (Chirality.flip χ) =
      -H.curvatureEnergy i χ := by
  cases χ <;>
    simp [curvatureEnergy, chiralityRealSign, Chirality.sign, Chirality.flip]

end ChiralPackingHamiltonian

/-! ## 3. Finite lattice bonds and configurations -/

/-- A finite nearest-neighbor or interaction bond. -/
structure ChiralBond
    (Site : Type*) where
  left : Site
  right : Site

/-- A chiral configuration on a lattice. -/
abbrev ChiralConfiguration
    (Site : Type*) :=
  Site → Chirality

namespace ChiralPackingHamiltonian

variable {Site : Type*}
variable (H : ChiralPackingHamiltonian Site)

/-- Bond energy induced by a chiral configuration. -/
def bondEnergy
    (σ : ChiralConfiguration Site)
    (b : ChiralBond Site) : ℝ :=
  H.pairEnergy (σ b.left) (σ b.right)

/-- Total finite packing energy over a finite list of bonds. -/
def totalBondEnergy
    (bonds : List (ChiralBond Site))
    (σ : ChiralConfiguration Site) : ℝ :=
  (bonds.map (fun b => H.bondEnergy σ b)).sum

/-- If a bond is aligned, its bond energy is `-J`. -/
theorem bondEnergy_aligned
    (σ : ChiralConfiguration Site)
    (b : ChiralBond Site)
    (halign : σ b.right = σ b.left) :
    H.bondEnergy σ b = -H.couplingJ := by
  unfold bondEnergy
  rw [halign]
  exact H.pairEnergy_same (σ b.left)

/-- If a bond is anti-aligned by chirality flip, its bond energy is `J`. -/
theorem bondEnergy_antialigned
    (σ : ChiralConfiguration Site)
    (b : ChiralBond Site)
    (hanti : σ b.right = Chirality.flip (σ b.left)) :
    H.bondEnergy σ b = H.couplingJ := by
  unfold bondEnergy
  rw [hanti]
  exact H.pairEnergy_opposite (σ b.left)

/-- For positive coupling, an aligned bond has lower energy than a flipped bond. -/
theorem aligned_bond_energy_lt_antialigned
    (hJ : 0 < H.couplingJ)
    (χ : Chirality) :
    H.pairEnergy χ χ <
      H.pairEnergy χ (Chirality.flip χ) :=
  H.same_chirality_energy_lt_opposite hJ χ

end ChiralPackingHamiltonian

/-! ## 4. Residue orientation audit -/

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}

/--
A residue is benign relative to a chosen global orientation when its chirality
matches that orientation.
-/
def IsBenign
    (R : HawkingPointResidue C)
    (orientation : Chirality) : Prop :=
  R.chirality = orientation

/--
A residue is misaligned when it fails the chosen orientation audit.

This is only an orientation mismatch. It is not a physical or ethical claim.
-/
def IsMisaligned
    (R : HawkingPointResidue C)
    (orientation : Chirality) : Prop :=
  R.chirality ≠ orientation

/-- Reorient a residue while preserving its projective ray and integer weight. -/
def reorient
    (R : HawkingPointResidue C)
    (orientation : Chirality) :
    HawkingPointResidue C where
  ray := R.ray
  weight := R.weight
  chirality := orientation

@[simp]
theorem reorient_weight
    (R : HawkingPointResidue C)
    (orientation : Chirality) :
    (reorient R orientation).weight = R.weight :=
  rfl

@[simp]
theorem reorient_chirality
    (R : HawkingPointResidue C)
    (orientation : Chirality) :
    (reorient R orientation).chirality = orientation :=
  rfl

/-- Reorientation preserves the projective ray exactly. -/
theorem sameRay_reorient
    (R : HawkingPointResidue C)
    (orientation : Chirality) :
    ProjectiveNullRay.SameRay
      (reorient R orientation).ray
      R.ray :=
  rfl

/-- Reorientation makes the residue benign for the chosen orientation. -/
theorem isBenign_reorient
    (R : HawkingPointResidue C)
    (orientation : Chirality) :
    IsBenign (reorient R orientation) orientation :=
  rfl

/-- Reorient every residue in a finite divisor to a chosen global orientation. -/
def reorientAll
    (D : HawkingPointDivisor C)
    (orientation : Chirality) :
    HawkingPointDivisor C where
  residues := D.residues.map (fun R => reorient R orientation)

/-- All residues in the reoriented divisor pass the orientation audit. -/
theorem all_residues_benign_reorientAll
    (D : HawkingPointDivisor C)
    (orientation : Chirality)
    {R : HawkingPointResidue C}
    (hR : R ∈ (reorientAll D orientation).residues) :
    IsBenign R orientation := by
  unfold reorientAll at hR
  rcases List.mem_map.mp hR with ⟨R₀, _hR₀, hEq⟩
  rw [← hEq]
  exact isBenign_reorient R₀ orientation

/-- Reorientation preserves the finite support cardinality. -/
theorem supportCard_reorientAll
    (D : HawkingPointDivisor C)
    (orientation : Chirality) :
    (reorientAll D orientation).supportCard = D.supportCard := by
  simp [reorientAll, HawkingPointDivisor.supportCard]

/-- Reorientation preserves total unsigned integer weight. -/
theorem totalWeight_reorientAll
    (D : HawkingPointDivisor C)
    (orientation : Chirality) :
    (reorientAll D orientation).totalWeight = D.totalWeight := by
  cases D with
  | mk residues =>
      have hmap :
          List.map
              ((fun R : HawkingPointResidue C => R.weight) ∘
                fun R => reorient R orientation)
              residues =
            List.map (fun R : HawkingPointResidue C => R.weight) residues := by
        induction residues with
        | nil =>
            simp
        | cons R Rs ih =>
            simp [reorient]
      simpa [reorientAll, HawkingPointDivisor.totalWeight] using congrArg List.sum hmap

/-! ## 5. Chiral packing audit -/

/--
A chiral packing audit for a Hawking-point divisor.

The audit records:

* the chosen global orientation;
* the packing Hamiltonian;
* a proof that thermal noise is nonnegative;
* a proof that the Hamiltonian is in the topological ordering phase.
-/
structure ChiralPackingAudit
    {Site V : Type*}
    [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}
    (D : HawkingPointDivisor C) where
  H : ChiralPackingHamiltonian Site
  thermalNoise_nonneg : 0 ≤ H.thermalNoise
  topological_phase : H.IsTopologicalPhase

namespace ChiralPackingAudit

variable
    {Site V : Type*}
    [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}
    {D : HawkingPointDivisor C}

variable (A : ChiralPackingAudit (Site := Site) D)

/-- The audit supplies positive packing coupling. -/
theorem couplingJ_pos :
    0 < A.H.couplingJ :=
  A.H.couplingJ_pos_of_topological A.thermalNoise_nonneg A.topological_phase

/-- Under the audit, same-chirality bonds are cheaper than opposite-chirality bonds. -/
theorem same_chirality_preferred
    (χ : Chirality) :
    A.H.pairEnergy χ χ <
      A.H.pairEnergy χ (Chirality.flip χ) :=
  A.H.same_chirality_energy_lt_opposite A.couplingJ_pos χ

/-- The divisor after audit-level reorientation has the same support cardinality. -/
theorem reoriented_supportCard_eq :
    (reorientAll D A.H.globalOrientation).supportCard =
      D.supportCard :=
  supportCard_reorientAll D A.H.globalOrientation

/-- The divisor after audit-level reorientation has the same total weight. -/
theorem reoriented_totalWeight_eq :
    (reorientAll D A.H.globalOrientation).totalWeight =
      D.totalWeight :=
  totalWeight_reorientAll D A.H.globalOrientation

/--
Every residue in the reoriented divisor is benign relative to the audit
orientation.
-/
theorem every_reoriented_residue_benign
    {R : HawkingPointResidue C}
    (hR : R ∈ (reorientAll D A.H.globalOrientation).residues) :
    IsBenign R A.H.globalOrientation :=
  all_residues_benign_reorientAll D A.H.globalOrientation hR

end ChiralPackingAudit

/-! ## 6. Owner theorem -/

/--
A successful audit proves:

* positive coupling;
* same-chirality pair preference;
* reorientation preserves finite support and total divisor weight.
-/
theorem chiralPackingAuditOwnerTarget :
  ∀ (Site V : Type*)
    [AddCommGroup V] [Module ℝ V],
  ∀ C : ConformalCrossoverDatum V,
  ∀ D : HawkingPointDivisor C,
  ∀ A : ChiralPackingAudit (Site := Site) D,
    0 < A.H.couplingJ ∧
    (∀ χ : Chirality,
      A.H.pairEnergy χ χ <
        A.H.pairEnergy χ (Chirality.flip χ)) ∧
    (reorientAll D A.H.globalOrientation).supportCard =
      D.supportCard ∧
    (reorientAll D A.H.globalOrientation).totalWeight =
      D.totalWeight := by
  intro Site V _ _ C D A
  refine ⟨A.couplingJ_pos, ?_, ?_, ?_⟩
  · intro χ
    exact A.same_chirality_preferred χ
  · exact ChiralPackingAudit.reoriented_supportCard_eq A
  · exact ChiralPackingAudit.reoriented_totalWeight_eq A

/-- Readout packet for one successful chiral packing audit. -/
theorem chiralPackingAudit_packet
    {Site V : Type*}
    [AddCommGroup V] [Module ℝ V]
    {C : ConformalCrossoverDatum V}
    {D : HawkingPointDivisor C}
    (A : ChiralPackingAudit (Site := Site) D) :
    0 < A.H.couplingJ ∧
      (∀ χ : Chirality,
        A.H.pairEnergy χ χ <
          A.H.pairEnergy χ (Chirality.flip χ)) ∧
      (reorientAll D A.H.globalOrientation).supportCard =
        D.supportCard ∧
      (reorientAll D A.H.globalOrientation).totalWeight =
        D.totalWeight :=
  chiralPackingAuditOwnerTarget Site V C D A

end ChiralPackingEnergy
