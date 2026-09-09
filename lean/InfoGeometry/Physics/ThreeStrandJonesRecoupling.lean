import Mathlib
import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Physics.TwoStrandJonesWeakReadout

/-!
# Three-strand Jones projectors and recoupling

The carrier is the explicit eight-dimensional tensor product of three
two-component spinors.  The normalized singlet projectors on adjacent
strands satisfy the Temperley--Lieb relation with loop parameter `1 / 4`.
-/

noncomputable section

set_option maxHeartbeats 1200000

namespace InfoGeometry.Physics.ThreeStrandJonesRecoupling

open InfoGeometry.Physics.TwoStrandJonesCasimir
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional

abbrev ThreeStrandState := Fin 2 → Fin 2 → Fin 2 → ℂ
abbrev ThreeStrandOperator := Module.End ℂ ThreeStrandState

def e12 : ThreeStrandOperator where
  toFun ψ i j k :=
    let c := (1 / 2 : ℂ) * (ψ 0 1 k - ψ 1 0 k)
    if i = 0 ∧ j = 1 then c else if i = 1 ∧ j = 0 then -c else 0
  map_add' ψ φ := by
    funext i j k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c ψ := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [RingHom.id_apply] <;> ring

def e23 : ThreeStrandOperator where
  toFun ψ i j k :=
    let c := (1 / 2 : ℂ) * (ψ i 0 1 - ψ i 1 0)
    if j = 0 ∧ k = 1 then c else if j = 1 ∧ k = 0 then -c else 0
  map_add' ψ φ := by
    funext i j k
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c ψ := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [RingHom.id_apply] <;> ring

theorem e12_idem : e12.comp e12 = e12 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e12] <;> ring

theorem e23_idem : e23.comp e23 = e23 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e23] <;> ring

theorem e12_e23_e12 :
    e12.comp (e23.comp e12) = (1 / 4 : ℂ) • e12 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e12, e23] <;> ring

theorem e23_e12_e23 :
    e23.comp (e12.comp e23) = (1 / 4 : ℂ) • e23 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [e12, e23] <;> ring

/-! ## Fusion-basis data and adjacent Jones operators -/

abbrev FusionState := Fin 2 → ℂ

/-- The two-channel recoupling matrix.  The parameters are kept explicit so
the same carrier supports classical and quantum-dimension specializations. -/
def recouplingF (d r : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / d, r / d; r / d, -(1 / d)]

def fusionSinglet : FusionState := ![1, 0]

def recoupledSinglet (d r : ℂ) : FusionState :=
  Matrix.mulVec (recouplingF d r) fusionSinglet

theorem recoupledSinglet_components (d r : ℂ) :
    recoupledSinglet d r 0 = 1 / d ∧
    recoupledSinglet d r 1 = r / d := by
  constructor <;> simp [recoupledSinglet, recouplingF, fusionSinglet,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def fusionProjector12 : Module.End ℂ FusionState where
  toFun ψ i := if i = 0 then ψ 0 else 0
  map_add' ψ φ := by
    funext i
    split_ifs <;> simp_all
  map_smul' c ψ := by
    funext i
    split_ifs <;> simp_all

def fusionCasimir (M : ℂ) : Module.End ℂ FusionState :=
  (-2 * M ^ 2) • ((1 : Module.End ℂ FusionState) - fusionProjector12)

def recoupledBoundaryPair (d r : ℝ) (pre : FusionState)
    (h : pairing (fun i => (recoupledSinglet d r i : ℂ)) pre ≠ 0) :
    RegularBoundaryPair (Fin 2) where
  pre := pre
  post := fun i => (recoupledSinglet (d : ℂ) (r : ℂ) i : ℂ)
  overlap_ne := h

theorem recoupled_e12_weakValue
    (d r : ℝ) (pre : FusionState)
    (h_d : d ≠ 0)
    (h : pairing (fun i => (recoupledSinglet d r i : ℂ)) pre ≠ 0) :
    weakValue (recoupledBoundaryPair d r pre h) fusionProjector12 =
      (pre 0) / (pre 0 + (r : ℂ) * pre 1) := by
  dsimp [weakValue, numerator, overlap, recoupledBoundaryPair,
    fusionProjector12, recoupledSinglet, recouplingF, fusionSinglet,
    pairing, Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_succ, Complex.star_def]
  field_simp [h_d]

theorem recoupled_casimir_weakValue
    (d r : ℝ) (M : ℂ) (pre : FusionState)
    (h_d : d ≠ 0)
    (h : pairing (fun i => (recoupledSinglet d r i : ℂ)) pre ≠ 0) :
    weakValue (recoupledBoundaryPair d r pre h) (fusionCasimir M) =
      (-2 * M ^ 2) *
        (1 - (pre 0) / (pre 0 + (r : ℂ) * pre 1)) := by
  rw [fusionCasimir, weakValue_smul, weakValue_sub, weakValue_one,
    recoupled_e12_weakValue d r pre h_d h]

/-- Jones braid operators on the two adjacent pairs. -/
noncomputable def braid12 (q : ℂ) : ThreeStrandOperator :=
  q • (1 : ThreeStrandOperator) - q ^ 2 • e12

noncomputable def braid23 (q : ℂ) : ThreeStrandOperator :=
  q • (1 : ThreeStrandOperator) - q ^ 2 • e23

theorem braid12_on_singlet (q : ℂ) (ψ : ThreeStrandState)
    (hψ : e12 ψ = ψ) : braid12 q ψ = (q - q ^ 2) • ψ := by
  simp [braid12, hψ, sub_smul]

theorem braid23_on_singlet (q : ℂ) (ψ : ThreeStrandState)
    (hψ : e23 ψ = ψ) : braid23 q ψ = (q - q ^ 2) • ψ := by
  simp [braid23, hψ, sub_smul]

/-! The unnormalized TL generators match the existing `q = I` Jones owner. -/
noncomputable def E12 : ThreeStrandOperator := 2 • e12
noncomputable def E23 : ThreeStrandOperator := 2 • e23

theorem E12_sq : E12.comp E12 = 2 • E12 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [E12, e12, LinearMap.comp_apply, Fin.sum_univ_succ] <;> ring

theorem E23_sq : E23.comp E23 = 2 • E23 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [E23, e23, LinearMap.comp_apply, Fin.sum_univ_succ] <;> ring

theorem E12_E23_E12 : E12.comp (E23.comp E12) = E12 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [E12, E23, e12, e23, LinearMap.comp_apply, Fin.sum_univ_succ]

theorem E23_E12_E23 : E23.comp (E12.comp E23) = E23 := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [E12, E23, e12, e23, LinearMap.comp_apply, Fin.sum_univ_succ]

noncomputable def standardJonesBraid12 : ThreeStrandOperator :=
  Complex.I • (1 : ThreeStrandOperator) - Complex.I • E12

noncomputable def standardJonesBraid23 : ThreeStrandOperator :=
  Complex.I • (1 : ThreeStrandOperator) - Complex.I • E23

theorem standardJonesBraid_artin :
    standardJonesBraid12.comp
        (standardJonesBraid23.comp standardJonesBraid12) =
      standardJonesBraid23.comp
        (standardJonesBraid12.comp standardJonesBraid23) := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [standardJonesBraid12, standardJonesBraid23, E12, E23,
      e12, e23, LinearMap.comp_apply, Fin.sum_univ_succ, Complex.I_mul_I] <;> ring

theorem standardJonesBraid12_square :
    standardJonesBraid12.comp standardJonesBraid12 =
      (-1 : ℂ) • (1 : ThreeStrandOperator) := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [standardJonesBraid12, E12, e12, LinearMap.comp_apply,
      Fin.sum_univ_succ, Complex.I_mul_I]
    ring_nf
    simp [Complex.I_sq]

theorem standardJonesBraid23_square :
    standardJonesBraid23.comp standardJonesBraid23 =
      (-1 : ℂ) • (1 : ThreeStrandOperator) := by
  apply LinearMap.ext
  intro ψ
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    simp [standardJonesBraid23, E23, e23, LinearMap.comp_apply,
      Fin.sum_univ_succ, Complex.I_mul_I]
    ring_nf
    simp [Complex.I_sq]

noncomputable def standardJonesBraid12Unit : (ThreeStrandOperator)ˣ where
  val := standardJonesBraid12
  inv := -standardJonesBraid12
  val_inv := by
    calc
      standardJonesBraid12.comp (-standardJonesBraid12) =
          -(standardJonesBraid12.comp standardJonesBraid12) := by
        ext ψ
        simp [LinearMap.comp_apply]
      _ = -((-1 : ℂ) • (1 : ThreeStrandOperator)) := by
        rw [standardJonesBraid12_square]
      _ = 1 := by
        ext ψ
        simp
  inv_val := by
    calc
      (-standardJonesBraid12).comp standardJonesBraid12 =
          -(standardJonesBraid12.comp standardJonesBraid12) := by
        ext ψ
        simp [LinearMap.comp_apply]
      _ = -((-1 : ℂ) • (1 : ThreeStrandOperator)) := by
        rw [standardJonesBraid12_square]
      _ = 1 := by
        ext ψ
        simp

noncomputable def standardJonesBraid23Unit : (ThreeStrandOperator)ˣ where
  val := standardJonesBraid23
  inv := -standardJonesBraid23
  val_inv := by
    calc
      standardJonesBraid23.comp (-standardJonesBraid23) =
          -(standardJonesBraid23.comp standardJonesBraid23) := by
        ext ψ
        simp [LinearMap.comp_apply]
      _ = -((-1 : ℂ) • (1 : ThreeStrandOperator)) := by
        rw [standardJonesBraid23_square]
      _ = 1 := by
        ext ψ
        simp
  inv_val := by
    calc
      (-standardJonesBraid23).comp standardJonesBraid23 =
          -(standardJonesBraid23.comp standardJonesBraid23) := by
        ext ψ
        simp [LinearMap.comp_apply]
      _ = -((-1 : ℂ) • (1 : ThreeStrandOperator)) := by
        rw [standardJonesBraid23_square]
      _ = 1 := by
        ext ψ
        simp

theorem standardJonesBraid_units_artin :
    standardJonesBraid12Unit * standardJonesBraid23Unit * standardJonesBraid12Unit =
      standardJonesBraid23Unit * standardJonesBraid12Unit * standardJonesBraid23Unit := by
  apply Units.ext
  exact standardJonesBraid_artin

noncomputable def threeStrandB3Representation : B3 →* (ThreeStrandOperator)ˣ :=
  homOfArtinPair standardJonesBraid12Unit standardJonesBraid23Unit
    standardJonesBraid_units_artin

@[simp] theorem threeStrandB3Representation_sig0 :
    threeStrandB3Representation (PresentedGroup.of B3Gen.sig0 : B3) =
      standardJonesBraid12Unit := by
  exact homOfArtinPair_sig0 _ _ _

@[simp] theorem threeStrandB3Representation_sig1 :
    threeStrandB3Representation (PresentedGroup.of B3Gen.sig1 : B3) =
      standardJonesBraid23Unit := by
  exact homOfArtinPair_sig1 _ _ _

end InfoGeometry.Physics.ThreeStrandJonesRecoupling
