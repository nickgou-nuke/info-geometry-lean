import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.Physics.B3PresentedGroup

/-!
# InfoGeometry.Canonical.BraidedCubicCompressionBridge

Generic abstract braided compression theorem on a unital StarRing A.

For any projection H (with P₀ = 1 - H) and unitary braid generators b₁, b₂
satisfying the Artin braid relation b₁ b₂ b₁ = b₂ b₁ b₂ and excitation preservation [H, bᵢ] = 0:

- Coxeter braid C = b₂ b₁.
- Garside braid element Δ = b₁ b₂ b₁.
- Full twist Z = C³ = Δ².
- Compressed braided charge Q_br = H C H.

Proves:
1. Genuine group representation ρ : B₃ →* Aˣ of the presented Artin braid group B₃.
2. Full twist Z is central in the braid group image: ∀ x ∈ B₃, Commute (ρ(Z)) (ρ(x)).
3. Q_br³ = Z H = H Z (compressed full-twist closure).
4. Normal partial unitarity: Q_br* Q_br = H and Q_br Q_br* = H.
5. Automatic vacuum annihilation: Q_br P₀ = P₀ Q_br = 0.
-/

noncomputable section

namespace InfoGeometry.Canonical.BraidedCubicCompressionBridge

/-- Data for an abstract braided excitation structure on a unital StarRing A. -/
structure BraidedProjectionData (A : Type*) [Ring A] [StarRing A] where
  H : A
  b1 : A
  b2 : A
  H_sq : H * H = H
  H_star : star H = H
  b1_u_left : star b1 * b1 = 1
  b1_u_right : b1 * star b1 = 1
  b2_u_left : star b2 * b2 = 1
  b2_u_right : b2 * star b2 = 1
  artin : b1 * b2 * b1 = b2 * b1 * b2
  H_comm_b1 : H * b1 = b1 * H
  H_comm_b2 : H * b2 = b2 * H

/-!
The following theorem is the owner-level statement.  It does not require a
record of hypotheses: the projection, braid words, and their compatibility
laws are explicit theorem arguments.  `BraidedProjectionData` below remains a
convenience carrier for the unitary/group-representation API.
-/
theorem braided_cubic_compression_cube_of
    {A : Type*} [Ring A]
    (H b1 b2 Z : A)
    (hH : H * H = H)
    (hHb1 : H * b1 = b1 * H)
    (hHb2 : H * b2 = b2 * H)
    (hZ : (b2 * b1) * (b2 * b1) * (b2 * b1) = Z)
    (hZH : Z * H = H * Z) :
    (H * (b2 * b1) * H) * (H * (b2 * b1) * H) *
        (H * (b2 * b1) * H) = Z * H := by
  have hC : H * (b2 * b1) = (b2 * b1) * H := by
    calc
      H * (b2 * b1) = (H * b2) * b1 := by noncomm_ring
      _ = (b2 * H) * b1 := by rw [hHb2]
      _ = b2 * (H * b1) := by noncomm_ring
      _ = b2 * (b1 * H) := by rw [hHb1]
      _ = (b2 * b1) * H := by noncomm_ring
  have hQ : H * (b2 * b1) * H = H * (b2 * b1) := by
    calc
      H * (b2 * b1) * H = (b2 * b1) * H * H := by rw [hC]
      _ = (b2 * b1) * (H * H) := by noncomm_ring
      _ = (b2 * b1) * H := by rw [hH]
      _ = H * (b2 * b1) := hC.symm
  rw [hQ]
  have hComm : Commute H (b2 * b1) := hC
  have hH3 : H ^ 3 = H := by
    rw [pow_three, hH, hH]
  have hC3 : (b2 * b1) ^ 3 = Z := by
    rw [pow_three]
    simpa only [mul_assoc] using hZ
  calc
    (H * (b2 * b1)) * (H * (b2 * b1)) * (H * (b2 * b1)) =
        (H * (b2 * b1)) ^ 3 := by rw [pow_three]; noncomm_ring
    _ = H ^ 3 * (b2 * b1) ^ 3 := hComm.mul_pow 3
    _ = H * Z := by rw [hH3, hC3]
    _ = Z * H := hZH.symm

namespace BraidedProjectionData

variable {A : Type*} [Ring A] [StarRing A]
variable (D : BraidedProjectionData A)

/-- The first braid generator as a Mathlib unitary element. -/
def braid1Unitary : unitary A :=
  ⟨D.b1, ⟨D.b1_u_left, D.b1_u_right⟩⟩

/-- The second braid generator as a Mathlib unitary element. -/
def braid2Unitary : unitary A :=
  ⟨D.b2, ⟨D.b2_u_left, D.b2_u_right⟩⟩

/-- The first braid generator as an element of the ambient unit group. -/
def braid1Unit : Aˣ := Unitary.toUnits (D.braid1Unitary)

/-- The second braid generator as an element of the ambient unit group. -/
def braid2Unit : Aˣ := Unitary.toUnits (D.braid2Unitary)

theorem braid1Unit_coe : (D.braid1Unit : A) = D.b1 := rfl

theorem braid2Unit_coe : (D.braid2Unit : A) = D.b2 := rfl

theorem braidUnits_artin :
    D.braid1Unit * D.braid2Unit * D.braid1Unit =
      D.braid2Unit * D.braid1Unit * D.braid2Unit := by
  apply Units.ext
  exact D.artin

/-- The generator map used to instantiate Mathlib's presented `B₃`. -/
def b3UnitMap : InfoGeometry.Physics.B3PresentedGroup.B3Gen → Aˣ
  | .sig0 => D.braid1Unit
  | .sig1 => D.braid2Unit

theorem b3UnitRelation :
    FreeGroup.lift D.b3UnitMap InfoGeometry.Physics.B3PresentedGroup.b3Relation = 1 := by
  simp only [InfoGeometry.Physics.B3PresentedGroup.b3Relation, map_mul, map_inv,
    FreeGroup.lift_apply_of, b3UnitMap]
  rw [braidUnits_artin D]
  group

/-- Genuine group representation of the presented Artin braid group in `Aˣ`. -/
def b3Representation :
    InfoGeometry.Physics.B3PresentedGroup.B3 →* Aˣ :=
  PresentedGroup.toGroup (f := D.b3UnitMap)
    (rels := InfoGeometry.Physics.B3PresentedGroup.b3Relations) (by
      intro r hr
      simp [InfoGeometry.Physics.B3PresentedGroup.b3Relations] at hr
      subst r
      exact b3UnitRelation D)

theorem b3Representation_sig0 :
    D.b3Representation
        (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig0) =
      D.braid1Unit := by
  change PresentedGroup.toGroup (f := D.b3UnitMap)
      (rels := InfoGeometry.Physics.B3PresentedGroup.b3Relations) _
      (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig0) = _
  rw [PresentedGroup.toGroup.of]
  rfl

theorem b3Representation_sig1 :
    D.b3Representation
        (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig1) =
      D.braid2Unit := by
  change PresentedGroup.toGroup (f := D.b3UnitMap)
      (rels := InfoGeometry.Physics.B3PresentedGroup.b3Relations) _
      (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig1) = _
  rw [PresentedGroup.toGroup.of]
  rfl

/-- **Apex Representation Theorem**: Existence of a genuine group homomorphism ρ : B₃ →* Aˣ
mapping Artin generators (σ₀, σ₁) to the unit generators (braid1Unit, braid2Unit). -/
theorem exists_b3_unit_representation :
    ∃ ρ : InfoGeometry.Physics.B3PresentedGroup.B3 →* Aˣ,
      ρ (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig0) = D.braid1Unit ∧
      ρ (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig1) = D.braid2Unit :=
  ⟨D.b3Representation, D.b3Representation_sig0, D.b3Representation_sig1⟩

/-- Vacuum / defect projection P₀ = 1 - H. -/
def P0 : A := 1 - D.H

/-- Garside braid element Δ = b₁ b₂ b₁. -/
def garsideElement : A := D.b1 * D.b2 * D.b1

/-- Coxeter braid C = b₂ b₁. -/
def coxeterBraid : A := D.b2 * D.b1

/-- Full twist Z = C³ = (b₂ b₁)³. -/
def fullTwist : A := D.coxeterBraid * D.coxeterBraid * D.coxeterBraid

/-- Compressed braided charge Q_br = H C H = H b₂ b₁ H. -/
def Qbr : A := D.H * D.coxeterBraid * D.H

/-- Full twist word in presented B₃: Δ² = (σ₁ σ₀)³. -/
def fullTwistWord : InfoGeometry.Physics.B3PresentedGroup.B3 :=
  (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig1 *
   PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig0) ^ 3

theorem fullTwist_val :
    ((D.b3Representation fullTwistWord : Aˣ) : A) = D.fullTwist := by
  dsimp [fullTwistWord, b3Representation]
  simp only [map_pow, map_mul, PresentedGroup.toGroup.of, b3UnitMap]
  rw [pow_three]
  simp only [Units.val_mul, braid2Unit_coe, braid1Unit_coe]
  dsimp [fullTwist, coxeterBraid]
  noncomm_ring

/-! ## Commutation and Centrality Theorems -/

theorem H_comm_coxeter : D.H * D.coxeterBraid = D.coxeterBraid * D.H := by
  dsimp [coxeterBraid]
  have h1 : D.H * (D.b2 * D.b1) = (D.H * D.b2) * D.b1 := by noncomm_ring
  have h2 : (D.H * D.b2) * D.b1 = (D.b2 * D.H) * D.b1 := by rw [D.H_comm_b2]
  have h3 : (D.b2 * D.H) * D.b1 = D.b2 * (D.H * D.b1) := by noncomm_ring
  have h4 : D.b2 * (D.H * D.b1) = D.b2 * (D.b1 * D.H) := by rw [D.H_comm_b1]
  have h5 : D.b2 * (D.b1 * D.H) = (D.b2 * D.b1) * D.H := by noncomm_ring
  rw [h1, h2, h3, h4, h5]

theorem Qbr_eq_H_mul_coxeter : D.Qbr = D.H * D.coxeterBraid := by
  dsimp [Qbr]
  have h1 : D.H * D.coxeterBraid * D.H = D.coxeterBraid * D.H * D.H := by rw [H_comm_coxeter D]
  have h2 : D.coxeterBraid * D.H * D.H = D.coxeterBraid * (D.H * D.H) := by noncomm_ring
  have h3 : D.coxeterBraid * (D.H * D.H) = D.coxeterBraid * D.H := by rw [D.H_sq]
  have h4 : D.coxeterBraid * D.H = D.H * D.coxeterBraid := by rw [H_comm_coxeter D]
  rw [h1, h2, h3, h4]

theorem Qbr_eq_coxeter_mul_H : D.Qbr = D.coxeterBraid * D.H := by
  dsimp [Qbr]
  have h1 : D.H * D.coxeterBraid * D.H = D.coxeterBraid * D.H * D.H := by rw [H_comm_coxeter D]
  have h2 : D.coxeterBraid * D.H * D.H = D.coxeterBraid * (D.H * D.H) := by noncomm_ring
  have h3 : D.coxeterBraid * (D.H * D.H) = D.coxeterBraid * D.H := by rw [D.H_sq]
  rw [h1, h2, h3]

theorem garside_b1 : D.garsideElement * D.b1 = D.b2 * D.garsideElement := by
  dsimp [garsideElement]
  have h2 : (D.b1 * D.b2 * D.b1) * D.b1 = (D.b2 * D.b1 * D.b2) * D.b1 := by rw [D.artin]
  have h3 : (D.b2 * D.b1 * D.b2) * D.b1 = D.b2 * (D.b1 * D.b2 * D.b1) := by noncomm_ring
  have h1 : D.b1 * D.b2 * D.b1 * D.b1 = (D.b1 * D.b2 * D.b1) * D.b1 := by noncomm_ring
  rw [h1, h2, h3]

theorem garside_b2 : D.garsideElement * D.b2 = D.b1 * D.garsideElement := by
  dsimp [garsideElement]
  have h2 : D.b1 * (D.b2 * D.b1 * D.b2) = D.b1 * (D.b1 * D.b2 * D.b1) := by rw [← D.artin]
  have h1 : D.b1 * D.b2 * D.b1 * D.b2 = D.b1 * (D.b2 * D.b1 * D.b2) := by noncomm_ring
  rw [h1, h2]

theorem fullTwist_eq_garside_sq : D.fullTwist = D.garsideElement * D.garsideElement := by
  dsimp [fullTwist, coxeterBraid, garsideElement]
  calc
    (D.b2 * D.b1) * (D.b2 * D.b1) * (D.b2 * D.b1) =
        (D.b2 * D.b1 * D.b2) * (D.b1 * D.b2 * D.b1) := by noncomm_ring
    _ = (D.b1 * D.b2 * D.b1) * (D.b1 * D.b2 * D.b1) := by rw [D.artin]

theorem fullTwist_comm_b1 : D.fullTwist * D.b1 = D.b1 * D.fullTwist := by
  rw [fullTwist_eq_garside_sq D]
  have h2 : D.garsideElement * (D.garsideElement * D.b1) = D.garsideElement * (D.b2 * D.garsideElement) := by rw [garside_b1 D]
  have h4 : (D.garsideElement * D.b2) * D.garsideElement = (D.b1 * D.garsideElement) * D.garsideElement := by rw [garside_b2 D]
  have h1 : D.garsideElement * D.garsideElement * D.b1 = D.garsideElement * (D.garsideElement * D.b1) := by noncomm_ring
  have h3 : D.garsideElement * (D.b2 * D.garsideElement) = (D.garsideElement * D.b2) * D.garsideElement := by noncomm_ring
  have h5 : (D.b1 * D.garsideElement) * D.garsideElement = D.b1 * (D.garsideElement * D.garsideElement) := by noncomm_ring
  rw [h1, h2, h3, h4, h5]

theorem fullTwist_comm_b2 : D.fullTwist * D.b2 = D.b2 * D.fullTwist := by
  rw [fullTwist_eq_garside_sq D]
  have h2 : D.garsideElement * (D.garsideElement * D.b2) = D.garsideElement * (D.b1 * D.garsideElement) := by rw [garside_b2 D]
  have h4 : (D.garsideElement * D.b1) * D.garsideElement = (D.b2 * D.garsideElement) * D.garsideElement := by rw [garside_b1 D]
  have h1 : D.garsideElement * D.garsideElement * D.b2 = D.garsideElement * (D.garsideElement * D.b2) := by noncomm_ring
  have h3 : D.garsideElement * (D.b1 * D.garsideElement) = (D.garsideElement * D.b1) * D.garsideElement := by noncomm_ring
  have h5 : (D.b2 * D.garsideElement) * D.garsideElement = D.b2 * (D.garsideElement * D.garsideElement) := by noncomm_ring
  rw [h1, h2, h3, h4, h5]

theorem fullTwist_comm_H : D.fullTwist * D.H = D.H * D.fullTwist := by
  dsimp [fullTwist, coxeterBraid]
  have h_c : D.b2 * D.b1 * D.H = D.H * (D.b2 * D.b1) := (H_comm_coxeter D).symm
  have h1 : (D.b2 * D.b1 * (D.b2 * D.b1) * (D.b2 * D.b1)) * D.H =
            D.b2 * D.b1 * (D.b2 * D.b1) * (D.b2 * D.b1 * D.H) := by noncomm_ring
  have h2 : D.b2 * D.b1 * (D.b2 * D.b1) * (D.b2 * D.b1 * D.H) =
            D.b2 * D.b1 * (D.b2 * D.b1) * (D.H * (D.b2 * D.b1)) := by rw [h_c]
  have h3 : D.b2 * D.b1 * (D.b2 * D.b1) * (D.H * (D.b2 * D.b1)) =
            D.b2 * D.b1 * (D.b2 * D.b1 * D.H) * (D.b2 * D.b1) := by noncomm_ring
  have h4 : D.b2 * D.b1 * (D.b2 * D.b1 * D.H) * (D.b2 * D.b1) =
            D.b2 * D.b1 * (D.H * (D.b2 * D.b1)) * (D.b2 * D.b1) := by rw [h_c]
  have h5 : D.b2 * D.b1 * (D.H * (D.b2 * D.b1)) * (D.b2 * D.b1) =
            (D.b2 * D.b1 * D.H) * (D.b2 * D.b1) * (D.b2 * D.b1) := by noncomm_ring
  have h6 : (D.b2 * D.b1 * D.H) * (D.b2 * D.b1) * (D.b2 * D.b1) =
            (D.H * (D.b2 * D.b1)) * (D.b2 * D.b1) * (D.b2 * D.b1) := by rw [h_c]
  have h7 : (D.H * (D.b2 * D.b1)) * (D.b2 * D.b1) * (D.b2 * D.b1) =
            D.H * (D.b2 * D.b1 * (D.b2 * D.b1) * (D.b2 * D.b1)) := by noncomm_ring
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- The centralizer subgroup in `B₃` of `D.b3Representation fullTwistWord`. -/
def b3CentralizerSubgroup : Subgroup InfoGeometry.Physics.B3PresentedGroup.B3 where
  carrier := {x | Commute (D.b3Representation fullTwistWord) (D.b3Representation x)}
  mul_mem' {x y} hx hy := by
    change Commute (D.b3Representation fullTwistWord) (D.b3Representation (x * y))
    rw [map_mul]
    exact Commute.mul_right hx hy
  one_mem' := Commute.one_right _
  inv_mem' {x} hx := by
    change Commute (D.b3Representation fullTwistWord) (D.b3Representation (x⁻¹))
    rw [map_inv]
    exact Commute.inv_right hx

theorem b3CentralizerSubgroup_contains_generators (j : InfoGeometry.Physics.B3PresentedGroup.B3Gen) :
    PresentedGroup.of j ∈ D.b3CentralizerSubgroup := by
  cases j with
  | sig0 =>
    change Commute (D.b3Representation fullTwistWord)
      (D.b3Representation (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig0))
    apply Units.ext
    simp only [Units.val_mul, fullTwist_val D, b3Representation_sig0 D, braid1Unit_coe D]
    exact fullTwist_comm_b1 D
  | sig1 =>
    change Commute (D.b3Representation fullTwistWord)
      (D.b3Representation (PresentedGroup.of InfoGeometry.Physics.B3PresentedGroup.B3Gen.sig1))
    apply Units.ext
    simp only [Units.val_mul, fullTwist_val D, b3Representation_sig1 D, braid2Unit_coe D]
    exact fullTwist_comm_b2 D

/-- **Centrality Theorem**: Full twist image ρ(fullTwistWord) is central in the B₃ representation image. -/
theorem fullTwist_is_central_in_b3_image :
    ∀ x : InfoGeometry.Physics.B3PresentedGroup.B3,
      Commute (D.b3Representation fullTwistWord) (D.b3Representation x) := fun x =>
  PresentedGroup.generated_by
    InfoGeometry.Physics.B3PresentedGroup.b3Relations
    D.b3CentralizerSubgroup
    (D.b3CentralizerSubgroup_contains_generators)
    x

/-! ## Apex Cubic Closure & Unitarity Theorems -/

/-- **Apex Theorem 1**: Compressed Full-Twist Cubic Closure Q_br³ = ρ(Δ²) H. -/
theorem braidedCubicSupercharge_cube : D.Qbr * D.Qbr * D.Qbr = (D.b3Representation fullTwistWord : A) * D.H := by
  have h_q1 : D.Qbr = D.H * D.coxeterBraid := Qbr_eq_H_mul_coxeter D
  have h_c : D.H * D.coxeterBraid = D.coxeterBraid * D.H := H_comm_coxeter D
  have h2 : D.H * (D.coxeterBraid * D.coxeterBraid) =
      (D.coxeterBraid * D.coxeterBraid) * D.H := by
    calc
      D.H * (D.coxeterBraid * D.coxeterBraid) =
          (D.H * D.coxeterBraid) * D.coxeterBraid := by noncomm_ring
      _ = (D.coxeterBraid * D.H) * D.coxeterBraid := by rw [h_c]
      _ = D.coxeterBraid * (D.H * D.coxeterBraid) := by noncomm_ring
      _ = D.coxeterBraid * (D.coxeterBraid * D.H) := by rw [h_c]
      _ = (D.coxeterBraid * D.coxeterBraid) * D.H := by noncomm_ring
  have h3 : D.H * (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) =
      (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) * D.H := by
    calc
      D.H * (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) =
          (D.H * (D.coxeterBraid * D.coxeterBraid)) * D.coxeterBraid := by
            noncomm_ring
      _ = ((D.coxeterBraid * D.coxeterBraid) * D.H) * D.coxeterBraid := by
            rw [h2]
      _ = (D.coxeterBraid * D.coxeterBraid) *
            (D.H * D.coxeterBraid) := by noncomm_ring
      _ = (D.coxeterBraid * D.coxeterBraid) *
            (D.coxeterBraid * D.H) := by rw [h_c]
      _ = (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) * D.H := by
            noncomm_ring
  rw [fullTwist_val D]
  dsimp [fullTwist]
  change (D.Qbr * D.Qbr) * D.Qbr = D.coxeterBraid * D.coxeterBraid * D.coxeterBraid * D.H
  simp only [h_q1]
  calc
    (D.H * D.coxeterBraid) * (D.H * D.coxeterBraid) *
        (D.H * D.coxeterBraid) =
        D.H * (D.coxeterBraid * D.H) * D.coxeterBraid *
        (D.H * D.coxeterBraid) := by noncomm_ring
    _ = D.H * (D.H * D.coxeterBraid) * D.coxeterBraid *
        (D.H * D.coxeterBraid) := by rw [h_c.symm]
    _ = (D.H * D.H) * (D.coxeterBraid * D.coxeterBraid) *
        (D.H * D.coxeterBraid) := by noncomm_ring
    _ = D.H * (D.coxeterBraid * D.coxeterBraid) *
        (D.H * D.coxeterBraid) := by rw [D.H_sq]
    _ = D.H * ((D.coxeterBraid * D.coxeterBraid) * D.H) *
        D.coxeterBraid := by noncomm_ring
    _ = D.H * (D.H * (D.coxeterBraid * D.coxeterBraid)) *
        D.coxeterBraid := by rw [h2.symm]
    _ = (D.H * D.H) * (D.coxeterBraid * D.coxeterBraid) *
        D.coxeterBraid := by noncomm_ring
    _ = D.H * (D.coxeterBraid * D.coxeterBraid) * D.coxeterBraid := by rw [D.H_sq]
    _ = D.H * (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) := by noncomm_ring
    _ = (D.coxeterBraid * D.coxeterBraid * D.coxeterBraid) * D.H := by rw [h3]

theorem star_b2_H_b2 : star D.b2 * D.H * D.b2 = D.H := by
  calc star D.b2 * D.H * D.b2
      = star D.b2 * (D.H * D.b2) := by noncomm_ring
    _ = star D.b2 * (D.b2 * D.H) := by rw [D.H_comm_b2]
    _ = (star D.b2 * D.b2) * D.H := by noncomm_ring
    _ = 1 * D.H := by rw [D.b2_u_left]
    _ = D.H := by noncomm_ring

theorem star_b1_H_b1 : star D.b1 * D.H * D.b1 = D.H := by
  calc star D.b1 * D.H * D.b1
      = star D.b1 * (D.H * D.b1) := by noncomm_ring
    _ = star D.b1 * (D.b1 * D.H) := by rw [D.H_comm_b1]
    _ = (star D.b1 * D.b1) * D.H := by noncomm_ring
    _ = 1 * D.H := by rw [D.b1_u_left]
    _ = D.H := by noncomm_ring

theorem b1_H_star_b1 : D.b1 * D.H * star D.b1 = D.H := by
  calc D.b1 * D.H * star D.b1
      = (D.b1 * D.H) * star D.b1 := by noncomm_ring
    _ = (D.H * D.b1) * star D.b1 := by rw [D.H_comm_b1]
    _ = D.H * (D.b1 * star D.b1) := by noncomm_ring
    _ = D.H * 1 := by rw [D.b1_u_right]
    _ = D.H := by noncomm_ring

theorem b2_H_star_b2 : D.b2 * D.H * star D.b2 = D.H := by
  have h_comm : D.b2 * D.H = D.H * D.b2 := D.H_comm_b2.symm
  have h_assoc : D.H * D.b2 * star D.b2 = D.H * (D.b2 * star D.b2) := mul_assoc D.H D.b2 (star D.b2)
  rw [h_comm, h_assoc, D.b2_u_right, mul_one]

/-- **Apex Theorem 2**: Left Normal Unitarity Q_br* Q_br = H. -/
theorem braidedCubicSupercharge_star_mul_self : star D.Qbr * D.Qbr = D.H := by
  dsimp [Qbr, coxeterBraid]
  have h_star : star (D.H * (D.b2 * D.b1) * D.H) = D.H * star D.b1 * star D.b2 * D.H := by
    simp only [star_mul, D.H_star]
    noncomm_ring
  rw [h_star]
  have h1 : D.H * star D.b1 * star D.b2 * D.H * (D.H * (D.b2 * D.b1) * D.H) =
            D.H * star D.b1 * (star D.b2 * (D.H * D.H) * D.b2) * D.b1 * D.H := by noncomm_ring
  rw [D.H_sq] at h1
  rw [h1]
  have h2 : star D.b2 * D.H * D.b2 = D.H := star_b2_H_b2 D
  rw [h2]
  have h_assoc : D.H * star D.b1 * D.H * D.b1 * D.H = D.H * (star D.b1 * D.H * D.b1) * D.H := by noncomm_ring
  rw [h_assoc, star_b1_H_b1 D, D.H_sq, D.H_sq]

/-- **Apex Theorem 3**: Right Normal Unitarity Q_br Q_br* = H. -/
theorem braidedCubicSupercharge_mul_star : D.Qbr * star D.Qbr = D.H := by
  dsimp [Qbr, coxeterBraid]
  have h_star : star (D.H * (D.b2 * D.b1) * D.H) = D.H * star D.b1 * star D.b2 * D.H := by
    simp only [star_mul, D.H_star]
    noncomm_ring
  rw [h_star]
  have h1 : D.H * (D.b2 * D.b1) * D.H * (D.H * star D.b1 * star D.b2 * D.H) =
            D.H * D.b2 * (D.b1 * (D.H * D.H) * star D.b1) * star D.b2 * D.H := by noncomm_ring
  rw [D.H_sq] at h1
  rw [h1]
  have h2 : D.b1 * D.H * star D.b1 = D.H := b1_H_star_b1 D
  rw [h2]
  have h_assoc : D.H * D.b2 * D.H * star D.b2 * D.H = D.H * (D.b2 * D.H * star D.b2) * D.H := by noncomm_ring
  rw [h_assoc, b2_H_star_b2 D, D.H_sq, D.H_sq]

/-- **Apex Theorem 4**: Automatic Defect Vacuum Annihilation Q_br P₀ = 0. -/
theorem braidedCubicSupercharge_mul_defect : D.Qbr * D.P0 = 0 := by
  dsimp [Qbr, P0]
  have h1 : D.H * D.coxeterBraid * D.H * (1 - D.H) = D.H * D.coxeterBraid * (D.H * (1 - D.H)) := by noncomm_ring
  have h2 : D.H * (1 - D.H) = 0 := by
    calc D.H * (1 - D.H) = D.H - D.H * D.H := by noncomm_ring
      _ = D.H - D.H := by rw [D.H_sq]
      _ = 0 := by noncomm_ring
  rw [h1, h2, mul_zero]

/-- **Apex Theorem 5**: Automatic Defect Vacuum Annihilation P₀ Q_br = 0. -/
theorem defect_mul_braidedCubicSupercharge : D.P0 * D.Qbr = 0 := by
  dsimp [Qbr, P0]
  have h1 : (1 - D.H) * (D.H * D.coxeterBraid * D.H) = ((1 - D.H) * D.H) * D.coxeterBraid * D.H := by noncomm_ring
  have h2 : (1 - D.H) * D.H = 0 := by
    calc (1 - D.H) * D.H = D.H - D.H * D.H := by noncomm_ring
      _ = D.H - D.H := by rw [D.H_sq]
      _ = 0 := by noncomm_ring
  rw [h1, h2, zero_mul, zero_mul]

/-- **Master Abstract Braided Compression Synthesis Theorem**. -/
theorem master_abstract_braided_compression_synthesis :
    (∀ x : InfoGeometry.Physics.B3PresentedGroup.B3,
      Commute (D.b3Representation fullTwistWord) (D.b3Representation x)) ∧
    D.Qbr * D.Qbr * D.Qbr = (D.b3Representation fullTwistWord : A) * D.H ∧
    star D.Qbr * D.Qbr = D.H ∧
    D.Qbr * star D.Qbr = D.H ∧
    D.Qbr * D.P0 = 0 ∧
    D.P0 * D.Qbr = 0 := ⟨
  fullTwist_is_central_in_b3_image D,
  braidedCubicSupercharge_cube D,
  braidedCubicSupercharge_star_mul_self D,
  braidedCubicSupercharge_mul_star D,
  braidedCubicSupercharge_mul_defect D,
  defect_mul_braidedCubicSupercharge D
⟩

end BraidedProjectionData

end InfoGeometry.Canonical.BraidedCubicCompressionBridge
