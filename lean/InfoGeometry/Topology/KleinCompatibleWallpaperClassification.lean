import Mathlib
import InfoGeometry.Topology.WallpaperSymmetry
import InfoGeometry.Topology.KANWallpaperIsomorphism
import InfoGeometry.Topology.WallpaperToWeylBridge
import InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge

/-!
# Klein-compatible wallpaper classification boundary

This module records the theorem-honest finite part of the current
`O(5,5)`/`D₅` Weyl-to-wallpaper projection.

Closed finite content:

* every nonzero projection of a finite `D₅` root `±eᵢ ± eⱼ` to the first two
  coordinates lands in the eight-root wallpaper cross-section
  `{±e₁, ±e₂, ±(e₁-e₂), ±(e₁+e₂)}`;
* the current kernel-backed wallpaper-group presentation is `pg`, through the
  owner `InfoGeometry.Topology.WallpaperSymmetry`;
* `pg`, `pmg`, and `pgg` have finite affine candidate corridors whose displayed
  normals lie in the projected `D₅` cross-section.

This file does **not** prove a full crystallographic classification of all
Klein-bottle-compatible wallpaper groups, and it does not identify the finite
affine representatives below with full quotient orbifold presentations.
-/

noncomputable section

namespace InfoGeometry.Topology.KleinCompatibleWallpaperClassification

open InfoGeometry.Topology.Wallpaper

abbrev Root2Q := Fin 2 → ℚ
abbrev Root5Q := Fin 5 → ℚ

instance : DecidableEq Root2Q :=
  Fintype.decidablePiFintype

/-! ## Projected `D₅` root cross-section -/

/-- The two signs used in the finite `D₅` root enumeration. -/
def signQ : Fin 2 → ℚ
  | 0 => 1
  | 1 => -1

/-- A `D₅` root `sᵢeᵢ + sⱼeⱼ`. -/
def d5RootOf (i j : Fin 5) (si sj : Fin 2) : Root5Q :=
  fun k => if k = i then signQ si else if k = j then signQ sj else 0

/-- Projection to the first two wallpaper coordinates. -/
def projectRoot2 (r : Root5Q) : Root2Q :=
  ![r 0, r 1]

/-- The eight nonzero signed roots seen in the wallpaper plane. -/
def projectedD5Root : Fin 8 → Root2Q
  | 0 => ![-1, -1]
  | 1 => ![-1, 0]
  | 2 => ![-1, 1]
  | 3 => ![0, -1]
  | 4 => ![0, 1]
  | 5 => ![1, -1]
  | 6 => ![1, 0]
  | 7 => ![1, 1]

/-- Membership in the displayed finite projected `D₅` cross-section. -/
def IsProjectedD5Root (r : Root2Q) : Prop :=
  ∃ k : Fin 8, r = projectedD5Root k

instance (r : Root2Q) : Decidable (IsProjectedD5Root r) := by
  unfold IsProjectedD5Root
  infer_instance

/-- An index chooser for the displayed eight-root cross-section. -/
def projectedD5RootIndex (r : Root2Q) : Fin 8 :=
  if r = ![-1, -1] then 0
  else if r = ![-1, 0] then 1
  else if r = ![-1, 1] then 2
  else if r = ![0, -1] then 3
  else if r = ![0, 1] then 4
  else if r = ![1, -1] then 5
  else if r = ![1, 0] then 6
  else 7

/-- Negation preserves the displayed projected root set. -/
theorem projectedD5Root_neg_mem (r : Root2Q)
    (hr : IsProjectedD5Root r) :
    IsProjectedD5Root (-r) := by
  rcases hr with ⟨k, rfl⟩
  fin_cases k
  · exact ⟨7, by decide⟩
  · exact ⟨6, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

/--
Every nonzero projection of a finite `D₅` root to the wallpaper plane lands in
the eight-root cross-section.
-/
theorem nonzero_projected_d5_root_mem
    (i j : Fin 5) (si sj : Fin 2)
    (hne : i ≠ j)
    (hnz : projectRoot2 (d5RootOf i j si sj) ≠ 0) :
    IsProjectedD5Root (projectRoot2 (d5RootOf i j si sj)) := by
  refine ⟨projectedD5RootIndex (projectRoot2 (d5RootOf i j si sj)), ?_⟩
  fin_cases i <;> fin_cases j <;> fin_cases si <;> fin_cases sj
  all_goals
    simp [projectRoot2, d5RootOf, signQ, projectedD5RootIndex,
      projectedD5Root] at hne hnz ⊢
  all_goals
    try contradiction
    norm_num

/-- Root directions modulo sign in the projected `D₅` wallpaper plane. -/
inductive ProjectedD5Direction where
  | e1
  | e2
  | e1SubE2
  | e1AddE2
  deriving DecidableEq, Repr

/-- Canonical positive representative of an unoriented projected direction. -/
def directionRoot : ProjectedD5Direction → Root2Q
  | .e1 => ![1, 0]
  | .e2 => ![0, 1]
  | .e1SubE2 => ![1, -1]
  | .e1AddE2 => ![1, 1]

/-- Each named projected direction is represented by a root in the finite cross-section. -/
theorem directionRoot_mem (d : ProjectedD5Direction) :
    IsProjectedD5Root (directionRoot d) := by
  cases d
  · exact ⟨6, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨7, rfl⟩

/-- The displayed projected set contains `e₂`, the normal in the `pg` chart. -/
theorem e2_pg_chart_mem :
    IsProjectedD5Root (![0, 1] : Root2Q) :=
  directionRoot_mem ProjectedD5Direction.e2

/-- The displayed projected set contains `e₁-e₂`, the Weyl-projection chart normal. -/
theorem e1_sub_e2_weyl_chart_mem :
    IsProjectedD5Root (![1, -1] : Root2Q) :=
  directionRoot_mem ProjectedD5Direction.e1SubE2

/-- The current finite chart treats these as the verified `pg` Klein corridor normals. -/
def IsCurrentPgKleinCorridorRoot (r : Root2Q) : Prop :=
  r = ![0, 1] ∨ r = ![0, -1] ∨ r = ![1, -1] ∨ r = ![-1, 1]

/-- Current `pg` Klein corridor roots are all in the projected `D₅` cross-section. -/
theorem current_pg_klein_corridor_roots_mem
    (r : Root2Q)
    (hr : IsCurrentPgKleinCorridorRoot r) :
    IsProjectedD5Root r := by
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨4, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨2, rfl⟩

/-! ## Wallpaper classes and finite candidate corridors -/

/-- Named wallpaper classes relevant to the Klein-bottle classification agenda. -/
inductive WallpaperClass
  | pg
  | pmg
  | pgg
  deriving DecidableEq, Repr

/--
The theorem-honest compatibility status currently proved as a wallpaper-group
presentation in this repository.  Only `pg` is closed here; `pmg` and `pgg`
remain classification targets.
-/
def IsCurrentlyVerifiedKleinClass (c : WallpaperClass) : Prop :=
  c = WallpaperClass.pg

instance (c : WallpaperClass) : Decidable (IsCurrentlyVerifiedKleinClass c) := by
  unfold IsCurrentlyVerifiedKleinClass
  infer_instance

/-- The verified wallpaper-group class is `pg`. -/
theorem pg_is_currently_verified :
    IsCurrentlyVerifiedKleinClass WallpaperClass.pg := by
  rfl

/-- `pmg` is an explicit open target in this module, not a proved wallpaper-group class. -/
theorem pmg_not_currently_verified :
    ¬ IsCurrentlyVerifiedKleinClass WallpaperClass.pmg := by
  intro h
  cases h

/-- `pgg` is an explicit open target in this module, not a proved wallpaper-group class. -/
theorem pgg_not_currently_verified :
    ¬ IsCurrentlyVerifiedKleinClass WallpaperClass.pgg := by
  intro h
  cases h

/-- The current verified status is exactly `pg`. -/
theorem current_verified_class_iff_pg (c : WallpaperClass) :
    IsCurrentlyVerifiedKleinClass c ↔ c = WallpaperClass.pg := by
  rfl

/-- Mirror in the `x` direction, used as a finite `pmg` representative generator. -/
def mirrorX : Lattice2D ≃ Lattice2D where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- A second glide, used as a finite `pgg` representative generator. -/
def glideY : Lattice2D ≃ Lattice2D where
  toFun p := (-p.1, p.2 + (1 / 2 : ℝ))
  invFun p := (-p.1, p.2 - (1 / 2 : ℝ))
  left_inv p := by
    ext <;> simp
  right_inv p := by
    ext <;> simp

/-- The finite `pmg` mirror representative is involutive. -/
theorem mirrorX_involutive (p : Lattice2D) :
    mirrorX (mirrorX p) = p := by
  ext <;> simp [mirrorX]

/-- The second glide squares to the `y` translation. -/
theorem glideY_squared_eq_y_translation (p : Lattice2D) :
    glideY (glideY p) = T_y p := by
  ext
  · simp [glideY, T_y]
  · simp [glideY, T_y]
    ring

/-- The second glide inverts the transverse `x` translation. -/
theorem glideY_x_translation_commutation (p : Lattice2D) :
    glideY (T_x p) = T_x.symm (glideY p) := by
  ext
  · simp [glideY, T_x]
    ring
  · simp [glideY, T_x]

/--
Finite affine candidate corridor carried by a named class.

This is deliberately weaker than `IsCurrentlyVerifiedKleinClass`: it records
explicit finite generators that exhibit the local Klein glide relation, without
asserting a full wallpaper-group classification theorem.
-/
def HasFiniteAffineKleinCandidate : WallpaperClass → Prop
  | .pg =>
      ∀ p : Lattice2D, concretePG.G (concretePG.T_y p) =
        concretePG.T_y.symm (concretePG.G p)
  | .pmg =>
      (∀ p : Lattice2D, mirrorX (mirrorX p) = p) ∧
        ∀ p : Lattice2D, concretePG.G (concretePG.T_y p) =
          concretePG.T_y.symm (concretePG.G p)
  | .pgg =>
      (∀ p : Lattice2D, concretePG.G (concretePG.G p) = concretePG.T_x p) ∧
        (∀ p : Lattice2D, glideY (glideY p) = T_y p) ∧
          (∀ p : Lattice2D, concretePG.G (concretePG.T_y p) =
            concretePG.T_y.symm (concretePG.G p)) ∧
            ∀ p : Lattice2D, glideY (T_x p) = T_x.symm (glideY p)

/-- The three named classes have finite affine candidate corridors. -/
theorem finite_affine_candidate_readout (c : WallpaperClass) :
    HasFiniteAffineKleinCandidate c := by
  cases c
  · exact concrete_pg_generates_klein_bottle_relation
  · exact ⟨mirrorX_involutive, concrete_pg_generates_klein_bottle_relation⟩
  · exact ⟨concretePG.h_glide_squared, glideY_squared_eq_y_translation,
      concrete_pg_generates_klein_bottle_relation, glideY_x_translation_commutation⟩

/--
Candidate root directions attached to the finite affine representatives.

For `pg`, the repo currently uses the `e₂` chart and the `e₁-e₂`
Weyl-projection chart.  For `pmg`/`pgg`, this records only finite representative
normals; it is not a full classification theorem for those wallpaper groups.
-/
def CandidateKleinDirection : WallpaperClass → ProjectedD5Direction → Prop
  | .pg, d => d = .e2 ∨ d = .e1SubE2
  | .pmg, d => d = .e1 ∨ d = .e2
  | .pgg, d => d = .e1 ∨ d = .e2

/-- Every finite candidate direction lies in the projected `D₅` root cross-section. -/
theorem candidate_direction_is_projected_d5_root
    (c : WallpaperClass) (d : ProjectedD5Direction)
    (_h : CandidateKleinDirection c d) :
    IsProjectedD5Root (directionRoot d) :=
  directionRoot_mem d

/-- Finite `pg` readout in the direct `e₂` chart. -/
theorem pg_e2_finite_readout :
    HasFiniteAffineKleinCandidate .pg ∧
      CandidateKleinDirection .pg .e2 ∧
      IsProjectedD5Root (directionRoot .e2) := by
  exact ⟨finite_affine_candidate_readout .pg, Or.inl rfl, directionRoot_mem .e2⟩

/-- Finite `pg` readout in the Weyl-projection `e₁-e₂` chart. -/
theorem pg_e1SubE2_finite_readout :
    HasFiniteAffineKleinCandidate .pg ∧
      CandidateKleinDirection .pg .e1SubE2 ∧
      IsProjectedD5Root (directionRoot .e1SubE2) := by
  exact ⟨finite_affine_candidate_readout .pg, Or.inr rfl,
    directionRoot_mem .e1SubE2⟩

/-- Finite `pmg` representative readout in the `e₁` mirror chart. -/
theorem pmg_e1_representative_readout :
    HasFiniteAffineKleinCandidate .pmg ∧
      CandidateKleinDirection .pmg .e1 ∧
      IsProjectedD5Root (directionRoot .e1) := by
  exact ⟨finite_affine_candidate_readout .pmg, Or.inl rfl, directionRoot_mem .e1⟩

/-- Finite `pgg` representative readout in the `e₂` glide chart. -/
theorem pgg_e2_representative_readout :
    HasFiniteAffineKleinCandidate .pgg ∧
      CandidateKleinDirection .pgg .e2 ∧
      IsProjectedD5Root (directionRoot .e2) := by
  exact ⟨finite_affine_candidate_readout .pgg, Or.inr rfl, directionRoot_mem .e2⟩

/--
The `pg` Lean owner supplies the Klein-bottle glide relation, and the two
currently used chart normals are projected `D₅` roots.
-/
theorem pg_relation_with_current_d5_normals (p : Lattice2D) :
    concretePG.G (concretePG.T_y p) =
        concretePG.T_y.symm (concretePG.G p) ∧
      IsProjectedD5Root ![0, 1] ∧
      IsProjectedD5Root ![1, -1] := by
  exact ⟨concrete_pg_generates_klein_bottle_relation p,
    e2_pg_chart_mem, e1_sub_e2_weyl_chart_mem⟩

/-- Matrix-side `pg` KAN readout from the existing projective owner. -/
theorem kan_pg_matrix_readout :
    InfoGeometry.Topology.KANWallpaper.G * InfoGeometry.Topology.KANWallpaper.G =
        InfoGeometry.Topology.KANWallpaper.T_x ∧
      InfoGeometry.Topology.KANWallpaper.n * InfoGeometry.Topology.KANWallpaper.n = 0 := by
  exact ⟨InfoGeometry.Topology.KANWallpaper.glide_squared_is_translation,
    InfoGeometry.Topology.KANWallpaper.translation_is_nilpotent_horizon⟩

/-- Coordinate-level affine Weyl `D₅` readout from the canonical bridge owner. -/
theorem affine_weyl_d5_coordinate_bridge_readout
    (t : InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.Z2) :
    (InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t 0 +
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t 1 +
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t 2 +
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t 3 +
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t 4 = 0) ∧
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.matVec5
          InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.sigmaXMatrix
          (InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t) =
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed
          (InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.sigmaX t) ∧
      InfoGeometry.Canonical.WallpaperPin55RootCrossSection.matVec5
          InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.sigmaDMatrix
          (InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed t) =
        InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.latticeEmbed
          (InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.sigmaD t) :=
  InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge.wallpaper_to_affine_weyl_d5_packet t

end InfoGeometry.Topology.KleinCompatibleWallpaperClassification

end noncomputable section
