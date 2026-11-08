/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
import InfoGeometry.Canonical.Cl55CARRepresentationCalibration
import InfoGeometry.Canonical.Cl55CommonCarrierIntertwiner
import InfoGeometry.Clifford.Cl55WittCalibratedColimit
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Clifford.Cl11StarAlgebraColimit

/-!
# Five-mode CAR mass and Peirce–Hodge coercivity

Each of the five native Jordan–Wigner CAR modes gives its own self-adjoint
occupation projection and unit Peirce horizon. The finite-stage coercivity
descent therefore applies modewise in the same UHF colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl55AllModeMassCoercivity

open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55VacuumIdempotentIdeal
open InfoGeometry.Twistor.RealSupertwistor
open InfoGeometry.Canonical.Cl55CARRepresentationCalibration
open InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading
open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Clifford.Cl11StarAlgebraColimit
open InfoGeometry.Clifford.Cl55WittCalibratedColimit
open InfoGeometry.Canonical.CliffordCARGeneratorTopological

/-- The occupied projection of CAR mode `i` in the finite five-mode stage. -/
def modeOccupation (i : Fin 5) : Stage 5 := creation i * annihilation i

/-- The self-adjoint Majorana mass operator of CAR mode `i`. -/
def modeMajorana (i : Fin 5) : Stage 5 := creation i + annihilation i

/-- The total Majorana interaction across the five finite CAR modes. -/
def fiveModeMajorana : Stage 5 := ∑ i ∈ Finset.univ, modeMajorana i

/-- The first three CAR Majorana modes, which are the color sector represented
on the split-octonion Zorn carrier. -/
def threeColorModeMajorana : Stage 5 :=
  ∑ i : Fin 3, modeMajorana (Fin.castAdd 2 i)

/-- The two remaining CAR Majorana modes complementary to the first-three
color sector. -/
def twoComplementModeMajorana : Stage 5 :=
  ∑ i : Fin 2, modeMajorana (Fin.natAdd 3 i)

/-- Total creation and annihilation operators on the five-mode Fock stage. -/
def fiveModeCreation : Stage 5 := ∑ i ∈ Finset.univ, creation i
def fiveModeAnnihilation : Stage 5 := ∑ i ∈ Finset.univ, annihilation i

/-- The native Clifford-algebra sum of the five Witt Majorana generators. -/
def nativeFiveModeMajorana : Cl55 :=
  ∑ i ∈ Finset.univ, (creation55 i + annihilation55 i)

/-- Native Cl(5,5) Majorana mass of the first three color modes. -/
def nativeThreeColorModeMajorana : Cl55 :=
  ∑ i : Fin 3,
    (creation55 (Fin.castAdd 2 i) + annihilation55 (Fin.castAdd 2 i))

/-- Native Cl(5,5) Majorana mass of the two modes complementary to the
first-three color sector. -/
def nativeTwoComplementModeMajorana : Cl55 :=
  ∑ i : Fin 2,
    (creation55 (Fin.natAdd 3 i) + annihilation55 (Fin.natAdd 3 i))

/-- The native Clifford mass carried by the four CAR modes orthogonal to the
geometric infinity/origin mode `4`. -/
def nativeFourModeMajoranaComplement : Cl55 :=
  ∑ i ∈ Finset.univ.erase 4, (creation55 i + annihilation55 i)

/-- The four-mode complement of the Majorana direction represented by the
infinity/origin CAR endpoint (mode `4`). -/
def fourModeMajoranaComplement : Stage 5 :=
  ∑ i ∈ Finset.univ.erase 4, modeMajorana i

private theorem square_sum_of_anticommuting_involutions
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → Stage 5)
    (hsq : ∀ i, T i * T i = 1)
    (hanti : ∀ i j, i ≠ j → T i * T j + T j * T i = 0) :
    (∑ i ∈ s, T i) * (∑ i ∈ s, T i) = (s.card : ℝ) • (1 : Stage 5) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hnot ih =>
      rw [Finset.sum_insert hnot]
      have hcross :
          T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a = 0 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro b hb
        exact hanti a b (by
          intro hab
          subst b
          exact hnot hb)
      calc
        (T a + (∑ i ∈ s, T i)) * (T a + (∑ i ∈ s, T i)) =
            T a * T a +
              (T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a) +
              (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by noncomm_ring
        _ = T a * T a + (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by
              rw [hcross]
              simp
        _ = (↑s.card + 1 : ℝ) • (1 : Stage 5) := by
              rw [hsq a, ih]
              simp only [add_smul, one_smul]
              abel
        _ = (↑(insert a s).card : ℝ) • (1 : Stage 5) := by
              congr 1
              simp [hnot]

private theorem mode_car_relations (i : Fin 5) :
    creation i * creation i = 0 ∧
    annihilation i * annihilation i = 0 ∧
    creation i * annihilation i + annihilation i * creation i = 1 := by
  exact ⟨creation_same_site_sq i, annihilation_same_site_sq i,
    creation_annihilation_same_site i⟩

/-- Every native CAR occupation is a self-adjoint idempotent. -/
theorem modeOccupation_structure (i : Fin 5) :
    modeOccupation i * modeOccupation i = modeOccupation i ∧
    star (modeOccupation i) = modeOccupation i := by
  rcases mode_car_relations i with ⟨hc, ha, hca⟩
  have hac : annihilation i * creation i = 1 - creation i * annihilation i := by
    rw [← hca]
    noncomm_ring
  constructor
  · change (creation i * annihilation i) * (creation i * annihilation i) = _
    calc
      (creation i * annihilation i) * (creation i * annihilation i) =
          creation i * (annihilation i * creation i) * annihilation i := by
            noncomm_ring
      _ = creation i * (1 - creation i * annihilation i) * annihilation i := by
            rw [hac]
      _ = creation i * annihilation i := by
            noncomm_ring [hc, ha]
  · change star (creation i * annihilation i) = creation i * annihilation i
    rw [star_mul]
    have hstarC : star (creation i) = annihilation i := by
      simpa only [Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using creation_transpose i
    have hstarA : star (annihilation i) = creation i := by
      calc
        star (annihilation i) = star (star (creation i)) := by rw [hstarC]
        _ = creation i := star_star _
    rw [hstarC, hstarA]

/-- Each Majorana mode has unit Tetraktys mass in its occupation Peirce cut. -/
theorem modeMajorana_unit_horizon (i : Fin 5) :
    star (modeMajorana i) = modeMajorana i ∧
    genV (modeOccupation i) (modeMajorana i) (star (modeMajorana i)) = 1 := by
  rcases mode_car_relations i with ⟨hc, ha, hca⟩
  have hac : annihilation i * creation i = 1 - creation i * annihilation i := by
    rw [← hca]
    noncomm_ring
  have hstarC : star (creation i) = annihilation i := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using creation_transpose i
  have hstarA : star (annihilation i) = creation i := by
    rw [← hstarC, star_star]
  have hMassStar : star (modeMajorana i) = modeMajorana i := by
    change star (creation i + annihilation i) = creation i + annihilation i
    rw [star_add, hstarC, hstarA]
    exact add_comm _ _
  have hCreationCorner : creation i * annihilation i * creation i = creation i := by
    calc
      creation i * annihilation i * creation i =
          creation i * (annihilation i * creation i) := by noncomm_ring
      _ = creation i * (1 - creation i * annihilation i) := by rw [hac]
      _ = creation i := by
        rw [mul_sub, mul_one]
        have hzero : creation i * (creation i * annihilation i) = 0 := by
          rw [← mul_assoc, hc, zero_mul]
        rw [hzero, sub_zero]
  have hAnnihilationCorner : annihilation i * creation i * annihilation i =
      annihilation i := by
    have hac' : creation i * annihilation i = 1 - annihilation i * creation i := by
      rw [← hca]
      noncomm_ring
    calc
      annihilation i * creation i * annihilation i =
          annihilation i * (creation i * annihilation i) := by noncomm_ring
      _ = annihilation i * (1 - annihilation i * creation i) := by rw [hac']
      _ = annihilation i := by
        rw [mul_sub, mul_one]
        have hzero : annihilation i * (annihilation i * creation i) = 0 := by
          rw [← mul_assoc, ha, zero_mul]
        rw [hzero, sub_zero]
  have hUpper : conePlus (modeOccupation i) (modeMajorana i) = creation i := by
    change (creation i * annihilation i) * (creation i + annihilation i) *
      (1 - creation i * annihilation i) = creation i
    have hPA : (creation i * annihilation i) *
        (creation i + annihilation i) = creation i := by
      rw [mul_add, hCreationCorner]
      have hzero : creation i * annihilation i * annihilation i = 0 := by
        rw [mul_assoc, ha, mul_zero]
      rw [hzero, add_zero]
    calc
      _ = creation i * annihilation i * creation i := by
        rw [hac.symm, hPA]
        noncomm_ring
      _ = creation i := hCreationCorner
  have hLower : coneMinus (modeOccupation i) (modeMajorana i) = annihilation i := by
    change (1 - creation i * annihilation i) * (creation i + annihilation i) *
      (creation i * annihilation i) = annihilation i
    rw [hac.symm]
    have hAP : (annihilation i * creation i) *
        (creation i + annihilation i) = annihilation i := by
      rw [mul_add]
      have hzero : annihilation i * creation i * creation i = 0 := by
        rw [mul_assoc, hc, mul_zero]
      rw [hzero, hAnnihilationCorner, zero_add]
    calc
      (annihilation i * creation i) * (creation i + annihilation i) *
          (creation i * annihilation i) =
          annihilation i * creation i * annihilation i := by
            rw [hAP]
            noncomm_ring
      _ = annihilation i := hAnnihilationCorner
  refine ⟨hMassStar, ?_⟩
  rw [hMassStar]
  unfold genV anticomm
  rw [hUpper, hLower]
  exact hca

/-- Distinct finite CAR Majorana modes anticommute. -/
theorem modeMajorana_anticommute {i j : Fin 5} (hij : i ≠ j) :
    modeMajorana i * modeMajorana j + modeMajorana j * modeMajorana i = 0 := by
  unfold modeMajorana
  simp only [add_mul, mul_add]
  have hcc := creation_cross_anticommute hij
  have haa := annihilation_cross_anticommute hij
  have hca := creation_annihilation_cross_anticommute hij
  have hac := annihilation_creation_cross_anticommute hij
  calc
    _ = (creation i * creation j + creation j * creation i) +
        (creation i * annihilation j + annihilation j * creation i) +
        (annihilation i * creation j + creation j * annihilation i) +
        (annihilation i * annihilation j + annihilation j * annihilation i) := by abel
    _ = 0 := by rw [hcc, hca, hac, haa]; simp

/-- The total finite mass generator splits as its geometric infinity/origin
Majorana direction plus the four remaining CAR modes. -/
theorem nativeFiveModeMajorana_infinity_mode_decomposition :
    nativeFiveModeMajorana =
      (creation55 4 + annihilation55 4) +
        nativeFourModeMajoranaComplement := by
  unfold nativeFiveModeMajorana nativeFourModeMajoranaComplement
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin 5)))
    (f := fun i : Fin 5 => creation55 i + annihilation55 i)
    (a := (4 : Fin 5)) (Finset.mem_univ 4)
  rw [← hsplit, add_comm]

/-- The finite matrix mass has the matching decomposition into its fourth CAR
mode and the remaining four modes. -/
theorem fiveModeMajorana_infinity_mode_decomposition :
    fiveModeMajorana =
      modeMajorana 4 + fourModeMajoranaComplement := by
  unfold fiveModeMajorana fourModeMajoranaComplement
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin 5)))
    (f := modeMajorana) (a := (4 : Fin 5)) (Finset.mem_univ 4)
  rw [← hsplit, add_comm]

/-- The residual four-mode mass has square exactly four times the identity. -/
theorem fourModeMajoranaComplement_square :
    fourModeMajoranaComplement * fourModeMajoranaComplement =
      (4 : ℝ) • (1 : Stage 5) := by
  have hsq : ∀ i : Fin 5, modeMajorana i * modeMajorana i = 1 := by
    intro i
    rcases mode_car_relations i with ⟨hc, ha, hca⟩
    change (creation i + annihilation i) *
        (creation i + annihilation i) = 1
    calc
      (creation i + annihilation i) * (creation i + annihilation i) =
          creation i * annihilation i + annihilation i * creation i := by
            noncomm_ring [hc, ha]
      _ = 1 := hca
  have h := square_sum_of_anticommuting_involutions
    (Finset.univ.erase (4 : Fin 5)) modeMajorana hsq
    (fun i j hij => modeMajorana_anticommute hij)
  simpa [fourModeMajoranaComplement, Finset.card_erase_of_mem
    (Finset.mem_univ (4 : Fin 5))] using h

/-- The infinity/origin Majorana direction anticommutes with the entire
four-mode complement.  This is the cross-term cancellation behind the
`1 + 4 = 5` mass-square decomposition. -/
theorem fourth_mass_mode_anticommutes_with_complement :
    modeMajorana 4 * fourModeMajoranaComplement +
      fourModeMajoranaComplement * modeMajorana 4 = 0 := by
  unfold fourModeMajoranaComplement
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact modeMajorana_anticommute ((Finset.mem_erase.mp hi).1.symm)

private theorem square_sum_of_anticommuting_square_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → Stage 5)
    (hsq : ∀ i, T i * T i = 0)
    (hanti : ∀ i j, i ≠ j → T i * T j + T j * T i = 0) :
    (∑ i ∈ s, T i) * (∑ i ∈ s, T i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hnot ih =>
      rw [Finset.sum_insert hnot]
      have hcross :
          T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a = 0 := by
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro b hb
        exact hanti a b (by
          intro hab
          subst b
          exact hnot hb)
      calc
        (T a + (∑ i ∈ s, T i)) * (T a + (∑ i ∈ s, T i)) =
            T a * T a +
              (T a * (∑ i ∈ s, T i) + (∑ i ∈ s, T i) * T a) +
              (∑ i ∈ s, T i) * (∑ i ∈ s, T i) := by noncomm_ring
        _ = 0 := by rw [hsq a, hcross, ih]; simp

private theorem fiveModeCreation_sq :
    fiveModeCreation * fiveModeCreation = 0 := by
  have hsq : ∀ i : Fin 5, creation i * creation i = 0 :=
    creation_same_site_sq
  have hanti : ∀ i j : Fin 5, i ≠ j →
      creation i * creation j + creation j * creation i = 0 := by
    intro i j hij
    exact creation_cross_anticommute hij
  simpa [fiveModeCreation] using
    square_sum_of_anticommuting_square_zero Finset.univ creation hsq hanti

private theorem fiveModeAnnihilation_sq :
    fiveModeAnnihilation * fiveModeAnnihilation = 0 := by
  have hsq : ∀ i : Fin 5, annihilation i * annihilation i = 0 :=
    annihilation_same_site_sq
  have hanti : ∀ i j : Fin 5, i ≠ j →
      annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
    intro i j hij
    exact annihilation_cross_anticommute hij
  simpa [fiveModeAnnihilation] using
    square_sum_of_anticommuting_square_zero Finset.univ annihilation hsq hanti

/-- The sum of five mutually anticommuting CAR Majorana operators squares to
five times the identity in the finite real matrix stage. -/
theorem fiveModeMajorana_square :
    fiveModeMajorana * fiveModeMajorana = (5 : ℝ) • (1 : Stage 5) := by
  have hsq : ∀ i : Fin 5, modeMajorana i * modeMajorana i = 1 := by
    intro i
    rcases mode_car_relations i with ⟨hc, ha, hca⟩
    change (creation i + annihilation i) *
        (creation i + annihilation i) = 1
    calc
      (creation i + annihilation i) * (creation i + annihilation i) =
          creation i * annihilation i + annihilation i * creation i := by
            noncomm_ring [hc, ha]
      _ = 1 := hca
  have h := square_sum_of_anticommuting_involutions Finset.univ
    modeMajorana hsq (fun i j hij => modeMajorana_anticommute hij)
  simpa [fiveModeMajorana, Finset.card_univ] using h

/-- The five-mode Clifford mass is the sum of the first-three color mass and
the two complementary modes, with the repository's `Fin.castAdd` indexing. -/
theorem fiveModeMajorana_color_two_mode_decomposition :
    fiveModeMajorana = threeColorModeMajorana + twoComplementModeMajorana := by
  simp [fiveModeMajorana, threeColorModeMajorana, twoComplementModeMajorana,
    Fin.sum_univ_succ, Fin.castAdd, Fin.natAdd]
  abel

/-- The first-three color Majorana mass has square three on the actual finite
Cl(5,5) matrix carrier. -/
theorem threeColorModeMajorana_square :
    threeColorModeMajorana * threeColorModeMajorana = (3 : ℝ) • (1 : Stage 5) := by
  have hsq : ∀ i : Fin 3,
      modeMajorana (Fin.castAdd 2 i) * modeMajorana (Fin.castAdd 2 i) = 1 := by
    intro i
    rcases mode_car_relations (Fin.castAdd 2 i) with ⟨hc, ha, hca⟩
    change (creation (Fin.castAdd 2 i) + annihilation (Fin.castAdd 2 i)) *
        (creation (Fin.castAdd 2 i) + annihilation (Fin.castAdd 2 i)) = 1
    calc
      _ = creation (Fin.castAdd 2 i) * annihilation (Fin.castAdd 2 i) +
          annihilation (Fin.castAdd 2 i) * creation (Fin.castAdd 2 i) := by
            noncomm_ring [hc, ha]
      _ = 1 := hca
  have hanti : ∀ i j : Fin 3, i ≠ j →
      modeMajorana (Fin.castAdd 2 i) * modeMajorana (Fin.castAdd 2 j) +
        modeMajorana (Fin.castAdd 2 j) * modeMajorana (Fin.castAdd 2 i) = 0 := by
    intro i j hij
    apply modeMajorana_anticommute
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [Fin.val_castAdd] using hv
  simpa [threeColorModeMajorana, Finset.card_univ] using
    square_sum_of_anticommuting_involutions (Finset.univ : Finset (Fin 3))
      (fun i => modeMajorana (Fin.castAdd 2 i)) hsq hanti

/-- The two complementary Majorana modes square to two on the finite
Cl(5,5) carrier. -/
theorem twoComplementModeMajorana_square :
    twoComplementModeMajorana * twoComplementModeMajorana = (2 : ℝ) • (1 : Stage 5) := by
  have hsq : ∀ i : Fin 2,
      modeMajorana (Fin.natAdd 3 i) * modeMajorana (Fin.natAdd 3 i) = 1 := by
    intro i
    rcases mode_car_relations (Fin.natAdd 3 i) with ⟨hc, ha, hca⟩
    change (creation (Fin.natAdd 3 i) + annihilation (Fin.natAdd 3 i)) *
        (creation (Fin.natAdd 3 i) + annihilation (Fin.natAdd 3 i)) = 1
    calc
      _ = creation (Fin.natAdd 3 i) * annihilation (Fin.natAdd 3 i) +
          annihilation (Fin.natAdd 3 i) * creation (Fin.natAdd 3 i) := by
            noncomm_ring [hc, ha]
      _ = 1 := hca
  have hanti : ∀ i j : Fin 2, i ≠ j →
      modeMajorana (Fin.natAdd 3 i) * modeMajorana (Fin.natAdd 3 j) +
        modeMajorana (Fin.natAdd 3 j) * modeMajorana (Fin.natAdd 3 i) = 0 := by
    intro i j hij
    apply modeMajorana_anticommute
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  simpa [twoComplementModeMajorana, Finset.card_univ] using
    square_sum_of_anticommuting_involutions (Finset.univ : Finset (Fin 2))
      (fun i => modeMajorana (Fin.natAdd 3 i)) hsq hanti

/-- The color and complementary mass sectors anticommute. This identifies the
cross term as zero while keeping their operator products ordered. -/
theorem threeColor_twoComplement_mass_anticommute :
    threeColorModeMajorana * twoComplementModeMajorana +
      twoComplementModeMajorana * threeColorModeMajorana = 0 := by
  have hIndex : ∀ i : Fin 3, ∀ j : Fin 2,
      Fin.castAdd 2 i ≠ Fin.natAdd 3 j := by
    intro i j h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hEach : ∀ i : Fin 3,
      modeMajorana (Fin.castAdd 2 i) * twoComplementModeMajorana +
        twoComplementModeMajorana * modeMajorana (Fin.castAdd 2 i) = 0 := by
    intro i
    unfold twoComplementModeMajorana
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    exact modeMajorana_anticommute (hIndex i j)
  unfold threeColorModeMajorana
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact hEach i

/-- The five-mode mass square decomposes into the infinity/origin mode's unit
mass and the four orthogonal modes' mass; the mixed terms vanish by CAR. -/
theorem fiveModeMajorana_square_from_infinity_split :
    let M := modeMajorana 4
    let R := fourModeMajoranaComplement
    M * M + (M * R + R * M) + R * R = (5 : ℝ) • (1 : Stage 5) := by
  have hmode : modeMajorana 4 * modeMajorana 4 = 1 := by
    rcases mode_car_relations 4 with ⟨hc, ha, hca⟩
    change (creation 4 + annihilation 4) *
        (creation 4 + annihilation 4) = 1
    calc
      (creation 4 + annihilation 4) * (creation 4 + annihilation 4) =
          creation 4 * annihilation 4 + annihilation 4 * creation 4 := by
            noncomm_ring [hc, ha]
      _ = 1 := hca
  have hcross := fourth_mass_mode_anticommutes_with_complement
  have hcross' : fourModeMajoranaComplement * modeMajorana 4 +
      modeMajorana 4 * fourModeMajoranaComplement = 0 := by
    simpa only [add_comm] using hcross
  dsimp
  calc
    modeMajorana 4 * modeMajorana 4 +
        (modeMajorana 4 * fourModeMajoranaComplement +
          fourModeMajoranaComplement * modeMajorana 4) +
        fourModeMajoranaComplement * fourModeMajoranaComplement =
        (modeMajorana 4 + fourModeMajoranaComplement) *
          (modeMajorana 4 + fourModeMajoranaComplement) := by noncomm_ring
    _ = (5 : ℝ) • (1 : Stage 5) := by
      noncomm_ring [hmode, hcross, hcross', fourModeMajoranaComplement_square]
      rw [← add_assoc (fourModeMajoranaComplement * modeMajorana 4)
        (modeMajorana 4 * fourModeMajoranaComplement) ((4 : ℝ) • (1 : Stage 5)),
        hcross', zero_add]
      calc
        1 + (4 : ℝ) • (1 : Stage 5) =
            (1 : ℝ) • (1 : Stage 5) + (4 : ℝ) • (1 : Stage 5) := by
              rw [one_smul]
        _ = ((1 : ℝ) + 4) • (1 : Stage 5) := by rw [add_smul]
        _ = (5 : ℝ) • (1 : Stage 5) := by norm_num

/-- Summing the five CAR modes preserves the mixed CAR relation exactly. -/
theorem fiveMode_creation_annihilation_anticommutator :
    fiveModeCreation * fiveModeAnnihilation +
      fiveModeAnnihilation * fiveModeCreation = (5 : ℝ) • (1 : Stage 5) := by
  have hsplit : fiveModeMajorana = fiveModeCreation + fiveModeAnnihilation := by
    simp [fiveModeMajorana, fiveModeCreation, fiveModeAnnihilation,
      modeMajorana, Finset.sum_add_distrib]
  have hMajorana := fiveModeMajorana_square
  rw [hsplit] at hMajorana
  calc
    fiveModeCreation * fiveModeAnnihilation +
        fiveModeAnnihilation * fiveModeCreation =
      (fiveModeCreation + fiveModeAnnihilation) *
        (fiveModeCreation + fiveModeAnnihilation) := by
          noncomm_ring [fiveModeCreation_sq, fiveModeAnnihilation_sq]
    _ = (5 : ℝ) • (1 : Stage 5) := hMajorana

/-- The summed creation/annihilation pair does not commute: its mixed CAR
relation is nonzero while both summed chiral operators are square-zero. -/
theorem fiveMode_creation_annihilation_commutator_ne_zero :
    fiveModeCreation * fiveModeAnnihilation -
      fiveModeAnnihilation * fiveModeCreation ≠ 0 := by
  intro hcomm
  have hcomm' : fiveModeCreation * fiveModeAnnihilation =
      fiveModeAnnihilation * fiveModeCreation := sub_eq_zero.mp hcomm
  have hsumSq :
      (fiveModeCreation * fiveModeAnnihilation +
        fiveModeAnnihilation * fiveModeCreation) *
        (fiveModeCreation * fiveModeAnnihilation +
          fiveModeAnnihilation * fiveModeCreation) = 0 := by
    have hprod :
        (fiveModeCreation * fiveModeAnnihilation) *
          (fiveModeCreation * fiveModeAnnihilation) = 0 := by
      calc
        (fiveModeCreation * fiveModeAnnihilation) *
            (fiveModeCreation * fiveModeAnnihilation) =
          fiveModeCreation * (fiveModeAnnihilation * fiveModeCreation) *
            fiveModeAnnihilation := by noncomm_ring
        _ = fiveModeCreation * (fiveModeCreation * fiveModeAnnihilation) *
            fiveModeAnnihilation := by rw [hcomm']
        _ = (fiveModeCreation * fiveModeCreation) *
            (fiveModeAnnihilation * fiveModeAnnihilation) := by noncomm_ring
        _ = 0 := by rw [fiveModeCreation_sq, fiveModeAnnihilation_sq]; simp
    have hprod' := hprod
    rw [hcomm'] at hprod'
    rw [hcomm']
    noncomm_ring [hprod']
  rw [fiveMode_creation_annihilation_anticommutator] at hsumSq
  have hscalar : ((5 : ℝ) • (1 : Stage 5)) * ((5 : ℝ) • (1 : Stage 5)) =
      (25 : ℝ) • (1 : Stage 5) := by
    calc
      ((5 : ℝ) • (1 : Stage 5)) * ((5 : ℝ) • (1 : Stage 5)) =
          (5 : ℝ) • ((1 : Stage 5) * ((5 : ℝ) • (1 : Stage 5))) := by
            rw [smul_mul_assoc]
      _ = (5 : ℝ) • ((5 : ℝ) • (1 : Stage 5)) := by simp
      _ = (25 : ℝ) • (1 : Stage 5) := by rw [smul_smul]; norm_num
  rw [hscalar] at hsumSq
  have hOne : (1 : Stage 5) ≠ 0 := one_ne_zero
  exact (smul_ne_zero (by norm_num : (25 : ℝ) ≠ 0) hOne) hsumSq

/-- The total five-mode CAR interaction gives a genuine off-diagonal BdG mass
anomaly. Particle–hole (Andreev) reflection reverses that anomaly, and adding
the reflected operator cancels it while retaining the two ordered diagonal
operator products. -/
theorem fiveMode_mass_interaction_and_andreev_cancellation :
    let D := fiveModeCreation
    let M := fiveModeAnnihilation
    let H := InfoGeometry.Physics.massiveBdGHamiltonian D M
    D * M - M * D ≠ 0 ∧
    (H * H) 0 1 ≠ 0 ∧
    H * H + InfoGeometry.Physics.andreevSwap * (H * H) *
        InfoGeometry.Physics.andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  dsimp
  refine ⟨fiveMode_creation_annihilation_commutator_ne_zero, ?_, ?_⟩
  · intro hentry
    have hcommEntry :
        (InfoGeometry.Physics.massiveBdGHamiltonian fiveModeCreation
          fiveModeAnnihilation *
          InfoGeometry.Physics.massiveBdGHamiltonian fiveModeCreation
            fiveModeAnnihilation) 0 1 =
          fiveModeCreation * fiveModeAnnihilation -
            fiveModeAnnihilation * fiveModeCreation := by
      rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
      simp
    apply fiveMode_creation_annihilation_commutator_ne_zero
    rw [← hcommEntry, hentry]
  · exact InfoGeometry.Physics.massiveBdGHamiltonian_andreev_anomaly_cancellation
      fiveModeCreation fiveModeAnnihilation

/-- The summed five-mode CAR commutator remains nonzero under the actual
finite-stage-to-UHF embedding. This uses injectivity of the owner map rather
than a separately postulated limit nonvanishing condition. -/
theorem fiveMode_creation_annihilation_commutator_survives_UHF :
    ofStage 5 (fiveModeCreation * fiveModeAnnihilation -
      fiveModeAnnihilation * fiveModeCreation) ≠ 0 := by
  intro hzero
  have hzero' :
      ofStage 5 (fiveModeCreation * fiveModeAnnihilation -
        fiveModeAnnihilation * fiveModeCreation) = ofStage 5 0 := by
    simpa using hzero
  have hfinite := (ofStage_injective 5) hzero'
  exact fiveMode_creation_annihilation_commutator_ne_zero hfinite

/-- The five-mode mass interaction survives as a nonzero BdG square anomaly
at the UHF colimit, and Andreev reflection cancels it exactly there. The
diagonal entries preserve their noncommutative order. -/
theorem fiveMode_mass_interaction_and_andreev_cancellation_at_UHF_limit :
    let D : Limit := ofStage 5 fiveModeCreation
    let M : Limit := ofStage 5 fiveModeAnnihilation
    let H := InfoGeometry.Physics.massiveBdGHamiltonian D M
    (D * M - M * D ≠ 0) ∧
    (H * H) 0 1 ≠ 0 ∧
    H * H + InfoGeometry.Physics.andreevSwap * (H * H) *
        InfoGeometry.Physics.andreevSwap =
      !![D * D + M * M + (M * M + D * D), 0;
         0, M * M + D * D + (D * D + M * M)] := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hmap : ofStage 5
        (fiveModeCreation * fiveModeAnnihilation -
          fiveModeAnnihilation * fiveModeCreation) = ofStage 5 0 := by
      simpa only [map_sub, map_mul, map_zero] using hzero
    have hfinite := (ofStage_injective 5) hmap
    exact fiveMode_creation_annihilation_commutator_ne_zero hfinite
  · intro hentry
    have hcommEntry :
        (InfoGeometry.Physics.massiveBdGHamiltonian (ofStage 5 fiveModeCreation)
          (ofStage 5 fiveModeAnnihilation) *
          InfoGeometry.Physics.massiveBdGHamiltonian (ofStage 5 fiveModeCreation)
            (ofStage 5 fiveModeAnnihilation)) 0 1 =
          ofStage 5 (fiveModeCreation * fiveModeAnnihilation -
            fiveModeAnnihilation * fiveModeCreation) := by
      rw [InfoGeometry.Physics.massiveBdGHamiltonian_sq_with_commutator]
      simp [map_sub, map_mul]
    have hzero : ofStage 5
        (fiveModeCreation * fiveModeAnnihilation -
          fiveModeAnnihilation * fiveModeCreation) = 0 := by
      rw [← hcommEntry, hentry]
    exact fiveMode_creation_annihilation_commutator_survives_UHF hzero
  · exact InfoGeometry.Physics.massiveBdGHamiltonian_andreev_anomaly_cancellation
      (ofStage 5 fiveModeCreation) (ofStage 5 fiveModeAnnihilation)

/-- Calibration of each native Clifford Majorana against the five-mode
Jordan–Wigner matrix generator. -/
theorem nativeModeMajorana_calibration (i : Fin 5) :
    exteriorToWittStageEquiv
      (cl55ToStage5 (creation55 i + annihilation55 i)) = modeMajorana i := by
  rw [map_add cl55ToStage5, map_add exteriorToWittStageEquiv,
    exteriorToWitt_creation55, exteriorToWitt_annihilation55]
  rfl

/-- The native first-three Cl(5,5) mass calibrates to the same three-mode
finite matrix sector used by the Zorn color representation. -/
theorem nativeThreeColorModeMajorana_calibration :
    exteriorToWittStageEquiv
      (cl55ToStage5 nativeThreeColorModeMajorana) = threeColorModeMajorana := by
  unfold nativeThreeColorModeMajorana threeColorModeMajorana
  simp only [map_sum, map_add, exteriorToWitt_creation55,
    exteriorToWitt_annihilation55, modeMajorana]

/-- The two remaining native Cl(5,5) modes calibrate to the complementary
two-mode finite matrix operator. -/
theorem nativeTwoComplementModeMajorana_calibration :
    exteriorToWittStageEquiv
      (cl55ToStage5 nativeTwoComplementModeMajorana) = twoComplementModeMajorana := by
  unfold nativeTwoComplementModeMajorana twoComplementModeMajorana
  simp only [map_sum, map_add, exteriorToWitt_creation55,
    exteriorToWitt_annihilation55, modeMajorana]

/-- The infinity/origin null pair determines the fourth Majorana direction
after the existing Clifford-to-Witt spinor coordinate map. -/
theorem infinity_origin_pair_calibrates_to_fourth_mass_mode :
    exteriorToWittStageEquiv
        (cl55ToStage5
          (InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityClifford55 +
           InfoGeometry.Canonical.Cl55InfinityWittBoundary.originClifford55)) =
      modeMajorana 4 := by
  simpa only [InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading.infinityClifford55_eq_creation55,
    InfoGeometry.Canonical.Cl55InfinitySourceSinkGrading.originClifford55_eq_annihilation55] using
    nativeModeMajorana_calibration 4

/-- The geometric infinity/origin Peirce projectors become the occupied and
unoccupied mode-four mass projections in the same UHF colimit used for the
finite-stage coercivity descent.  This composes the native endpoint
representation, its Witt calibration, and the existing direct-limit map. -/
theorem infinity_origin_cut_is_the_mode_four_mass_cut_in_UHF_limit :
    cl55WittColimit
        InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityProjector55 =
      ofStage 5 (modeOccupation 4) ∧
    cl55WittColimit
        InfoGeometry.Canonical.Cl55InfinityWittBoundary.originProjector55 =
      ofStage 5 (1 - modeOccupation 4) := by
  rcases infinity_origin_projectors_are_mode_four_occupations_in_limit with
    ⟨hInfinity, hOrigin, hComplement⟩
  have hCreate : algebraicCreationElement 5 4 = ofStage 5 (creation 4) := by
    rfl
  have hAnnihilate : algebraicAnnihilationElement 5 4 =
      ofStage 5 (annihilation 4) := by
    rfl
  have hOccupation : algebraicCreationElement 5 4 *
      algebraicAnnihilationElement 5 4 =
        ofStage 5 (creation 4 * annihilation 4) := by
    calc
      _ = ofStage 5 (creation 4) * ofStage 5 (annihilation 4) := by
        rw [hCreate, hAnnihilate]
      _ = ofStage 5 (creation 4 * annihilation 4) :=
        (map_mul (ofStage 5) (creation 4) (annihilation 4)).symm
  have hComplementStage :
      ofStage 5 (annihilation 4 * creation 4) =
        1 - ofStage 5 (creation 4 * annihilation 4) := by
    calc
      _ = ofStage 5 (annihilation 4) * ofStage 5 (creation 4) :=
        map_mul (ofStage 5) (annihilation 4) (creation 4)
      _ = algebraicAnnihilationElement 5 4 * algebraicCreationElement 5 4 := by
        rw [hAnnihilate, hCreate]
      _ = 1 - algebraicCreationElement 5 4 *
          algebraicAnnihilationElement 5 4 := hComplement
      _ = 1 - ofStage 5 (creation 4 * annihilation 4) := by
        rw [hOccupation]
  have hOriginStage : algebraicAnnihilationElement 5 4 *
      algebraicCreationElement 5 4 =
        ofStage 5 (1 - creation 4 * annihilation 4) := by
    calc
      _ = ofStage 5 (annihilation 4 * creation 4) := by
        calc
          _ = ofStage 5 (annihilation 4) * ofStage 5 (creation 4) := by
            rw [hAnnihilate, hCreate]
          _ = ofStage 5 (annihilation 4 * creation 4) :=
            (map_mul (ofStage 5) (annihilation 4) (creation 4)).symm
      _ = 1 - ofStage 5 (creation 4 * annihilation 4) := hComplementStage
      _ = ofStage 5 (1 - creation 4 * annihilation 4) := by
        rw [map_sub, map_one]
  constructor
  · change cl55WittColimit
      InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityProjector55 =
      ofStage 5 (creation 4 * annihilation 4)
    calc
      _ = algebraicCreationElement 5 4 * algebraicAnnihilationElement 5 4 :=
        hInfinity
      _ = ofStage 5 (creation 4 * annihilation 4) := hOccupation
  · change cl55WittColimit
      InfoGeometry.Canonical.Cl55InfinityWittBoundary.originProjector55 =
      ofStage 5 (1 - creation 4 * annihilation 4)
    calc
      _ = algebraicAnnihilationElement 5 4 * algebraicCreationElement 5 4 :=
        hOrigin
      _ = ofStage 5 (1 - creation 4 * annihilation 4) := hOriginStage

/-- The full native Clifford mass sum calibrates to the summed matrix CAR
operator, with the actual change of finite spinor coordinates included. -/
theorem nativeFiveModeMajorana_calibration :
    exteriorToWittStageEquiv (cl55ToStage5 nativeFiveModeMajorana) =
      fiveModeMajorana := by
  unfold nativeFiveModeMajorana fiveModeMajorana
  simp only [map_sum, map_add, exteriorToWitt_creation55,
    exteriorToWitt_annihilation55, modeMajorana]

/-- The five-mode Clifford mass decomposes inside Cl(5,5) into its represented
three-color mass and its two-mode complement. -/
theorem nativeFiveModeMajorana_color_two_mode_decomposition :
    nativeFiveModeMajorana =
      nativeThreeColorModeMajorana + nativeTwoComplementModeMajorana := by
  simp [nativeFiveModeMajorana, nativeThreeColorModeMajorana,
    nativeTwoComplementModeMajorana, Fin.sum_univ_succ,
    Fin.castAdd, Fin.natAdd]
  abel

/-- The two complementary native Clifford mass sectors have the same
quadratic weights as their calibrated finite CAR operators. -/
theorem nativeColor_and_complement_mass_squares :
    nativeThreeColorModeMajorana * nativeThreeColorModeMajorana =
        (3 : ℝ) • (1 : Cl55) ∧
    nativeTwoComplementModeMajorana * nativeTwoComplementModeMajorana =
        (2 : ℝ) • (1 : Cl55) := by
  have hColor : nativeThreeColorModeMajorana * nativeThreeColorModeMajorana =
      (3 : ℝ) • (1 : Cl55) := by
    let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
    apply E.injective
    have hcal : E nativeThreeColorModeMajorana = threeColorModeMajorana := by
      change exteriorToWittStageEquiv
        (exteriorCl55StageEquiv nativeThreeColorModeMajorana) = _
      have h := nativeThreeColorModeMajorana_calibration
      rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
      exact h
    calc
      E (nativeThreeColorModeMajorana * nativeThreeColorModeMajorana) =
          E nativeThreeColorModeMajorana * E nativeThreeColorModeMajorana :=
        map_mul E _ _
      _ = threeColorModeMajorana * threeColorModeMajorana := by rw [hcal]
      _ = (3 : ℝ) • (1 : Stage 5) := threeColorModeMajorana_square
      _ = E ((3 : ℝ) • (1 : Cl55)) := by simp [E]
  have hComplement : nativeTwoComplementModeMajorana *
      nativeTwoComplementModeMajorana = (2 : ℝ) • (1 : Cl55) := by
    let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
    apply E.injective
    have hcal : E nativeTwoComplementModeMajorana = twoComplementModeMajorana := by
      change exteriorToWittStageEquiv
        (exteriorCl55StageEquiv nativeTwoComplementModeMajorana) = _
      have h := nativeTwoComplementModeMajorana_calibration
      rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
      exact h
    calc
      E (nativeTwoComplementModeMajorana * nativeTwoComplementModeMajorana) =
          E nativeTwoComplementModeMajorana * E nativeTwoComplementModeMajorana :=
        map_mul E _ _
      _ = twoComplementModeMajorana * twoComplementModeMajorana := by rw [hcal]
      _ = (2 : ℝ) • (1 : Stage 5) := twoComplementModeMajorana_square
      _ = E ((2 : ℝ) • (1 : Cl55)) := by simp [E]
  exact ⟨hColor, hComplement⟩

/-- The color mass and its two-mode complement have vanishing mixed
anticommutator in the native Clifford algebra. -/
theorem nativeColor_twoComplement_mass_anticommute :
    nativeThreeColorModeMajorana * nativeTwoComplementModeMajorana +
      nativeTwoComplementModeMajorana * nativeThreeColorModeMajorana = 0 := by
  let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
  apply E.injective
  have hColor : E nativeThreeColorModeMajorana = threeColorModeMajorana := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv nativeThreeColorModeMajorana) = _
    have h := nativeThreeColorModeMajorana_calibration
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  have hComplement : E nativeTwoComplementModeMajorana = twoComplementModeMajorana := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv nativeTwoComplementModeMajorana) = _
    have h := nativeTwoComplementModeMajorana_calibration
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  simpa only [map_add, map_mul, map_zero, hColor, hComplement] using
    threeColor_twoComplement_mass_anticommute

/-- The full native Clifford mass square is the sum of the color and
complement squares; the mixed interaction cancels by CAR. -/
theorem nativeFiveModeMajorana_square_from_color_split :
    nativeFiveModeMajorana * nativeFiveModeMajorana =
      (5 : ℝ) • (1 : Cl55) := by
  rw [nativeFiveModeMajorana_color_two_mode_decomposition]
  rcases nativeColor_and_complement_mass_squares with ⟨hColor, hComplement⟩
  have hCross := nativeColor_twoComplement_mass_anticommute
  calc
    (nativeThreeColorModeMajorana + nativeTwoComplementModeMajorana) *
        (nativeThreeColorModeMajorana + nativeTwoComplementModeMajorana) =
      nativeThreeColorModeMajorana * nativeThreeColorModeMajorana +
        (nativeThreeColorModeMajorana * nativeTwoComplementModeMajorana +
          nativeTwoComplementModeMajorana * nativeThreeColorModeMajorana) +
        nativeTwoComplementModeMajorana * nativeTwoComplementModeMajorana := by
          noncomm_ring
    _ = (3 : ℝ) • (1 : Cl55) + 0 + (2 : ℝ) • (1 : Cl55) := by
          rw [hColor, hCross, hComplement]
    _ = (5 : ℝ) • (1 : Cl55) := by
          rw [add_zero, ← add_smul]
          norm_num

/-- The four-mode Clifford complement is carried by the same calibrated
finite matrix operator as the corresponding Peirce–CAR sum. -/
theorem nativeFourModeMajoranaComplement_calibration :
    exteriorToWittStageEquiv
      (cl55ToStage5 nativeFourModeMajoranaComplement) =
        fourModeMajoranaComplement := by
  unfold nativeFourModeMajoranaComplement fourModeMajoranaComplement
  simp only [map_sum, map_add, exteriorToWitt_creation55,
    exteriorToWitt_annihilation55, modeMajorana]

/-- The native Clifford four-mode mass complement has square `4`, proved by
transport through the faithful finite spinor coordinate equivalence. -/
theorem nativeFourModeMajoranaComplement_square :
    nativeFourModeMajoranaComplement * nativeFourModeMajoranaComplement =
      (4 : ℝ) • (1 : Cl55) := by
  let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
  apply E.injective
  have hcal : E nativeFourModeMajoranaComplement =
      fourModeMajoranaComplement := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv nativeFourModeMajoranaComplement) = _
    have h := nativeFourModeMajoranaComplement_calibration
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  calc
    E (nativeFourModeMajoranaComplement * nativeFourModeMajoranaComplement) =
        E nativeFourModeMajoranaComplement * E nativeFourModeMajoranaComplement :=
      map_mul E _ _
    _ = fourModeMajoranaComplement * fourModeMajoranaComplement := by
      rw [hcal]
    _ = (4 : ℝ) • (1 : Stage 5) := fourModeMajoranaComplement_square
    _ = E ((4 : ℝ) • (1 : Cl55)) := by simp [E]

/-- The infinity/origin Majorana direction anticommutes with the native
four-mode Clifford mass complement. -/
theorem infinity_origin_majorana_anticommutes_with_native_complement :
    (InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityClifford55 +
      InfoGeometry.Canonical.Cl55InfinityWittBoundary.originClifford55) *
        nativeFourModeMajoranaComplement +
      nativeFourModeMajoranaComplement *
        (InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityClifford55 +
          InfoGeometry.Canonical.Cl55InfinityWittBoundary.originClifford55) = 0 := by
  let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
  apply E.injective
  have hmode : E
      (InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityClifford55 +
        InfoGeometry.Canonical.Cl55InfinityWittBoundary.originClifford55) =
      modeMajorana 4 := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv
        (InfoGeometry.Canonical.Cl55InfinityWittBoundary.infinityClifford55 +
          InfoGeometry.Canonical.Cl55InfinityWittBoundary.originClifford55)) = _
    have h := infinity_origin_pair_calibrates_to_fourth_mass_mode
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  have hrest : E nativeFourModeMajoranaComplement =
      fourModeMajoranaComplement := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv nativeFourModeMajoranaComplement) = _
    have h := nativeFourModeMajoranaComplement_calibration
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  simpa only [map_add, map_mul, map_zero, hmode, hrest] using
    fourth_mass_mode_anticommutes_with_complement

/-- The native five-mode Clifford mass squares to its exact finite CAR value. -/
theorem nativeFiveModeMajorana_square :
    nativeFiveModeMajorana * nativeFiveModeMajorana =
      (5 : ℝ) • (1 : Cl55) := by
  let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
  apply E.injective
  calc
    E (nativeFiveModeMajorana * nativeFiveModeMajorana) =
        E nativeFiveModeMajorana * E nativeFiveModeMajorana := map_mul E _ _
    _ = fiveModeMajorana * fiveModeMajorana := by
      have hcal : E nativeFiveModeMajorana = fiveModeMajorana := by
        change exteriorToWittStageEquiv
          (exteriorCl55StageEquiv nativeFiveModeMajorana) = fiveModeMajorana
        have h := nativeFiveModeMajorana_calibration
        rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
        exact h
      rw [hcal]
    _ = (5 : ℝ) • (1 : Stage 5) := fiveModeMajorana_square
    _ = E ((5 : ℝ) • (1 : Cl55)) := by simp [E]

/-- The common polynomial–Fock representation of `Cl(5,5)` carries the same
five-mode mass square as the calibrated Witt matrix representation. -/
theorem commonCarrier_nativeFiveModeMajorana_square :
    cl55CommonCarrierRep nativeFiveModeMajorana *
        cl55CommonCarrierRep nativeFiveModeMajorana =
      (5 : ℝ) • (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) := by
  have h := congrArg cl55CommonCarrierRep nativeFiveModeMajorana_square
  simpa only [map_mul, map_smul, map_one] using h

/-- The color and complementary mass operators retain their distinct
quadratic weights on the actual polynomial–Fock carrier. -/
theorem commonCarrier_color_complement_mass_squares :
    cl55CommonCarrierRep nativeThreeColorModeMajorana *
        cl55CommonCarrierRep nativeThreeColorModeMajorana =
      (3 : ℝ) • (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) ∧
    cl55CommonCarrierRep nativeTwoComplementModeMajorana *
        cl55CommonCarrierRep nativeTwoComplementModeMajorana =
      (2 : ℝ) • (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) := by
  constructor
  · have h := congrArg cl55CommonCarrierRep
      nativeColor_and_complement_mass_squares.1
    simpa only [map_mul, map_smul, map_one] using h
  · have h := congrArg cl55CommonCarrierRep
      nativeColor_and_complement_mass_squares.2
    simpa only [map_mul, map_smul, map_one] using h

/-- The two represented sectors still have zero mixed anticommutator after
lifting to the common fermion–boson operator carrier. -/
theorem commonCarrier_color_complement_mass_anticommute :
    cl55CommonCarrierRep nativeThreeColorModeMajorana *
        cl55CommonCarrierRep nativeTwoComplementModeMajorana +
      cl55CommonCarrierRep nativeTwoComplementModeMajorana *
        cl55CommonCarrierRep nativeThreeColorModeMajorana = 0 := by
  have h := congrArg cl55CommonCarrierRep
    nativeColor_twoComplement_mass_anticommute
  simpa only [map_mul, map_add, map_zero] using h

/-- On the common operator carrier, the five-mode mass square is the sum of
the color and complementary mass squares, with no cross interaction. -/
theorem commonCarrier_fiveMode_mass_square_sector_sum :
    cl55CommonCarrierRep nativeFiveModeMajorana *
        cl55CommonCarrierRep nativeFiveModeMajorana =
      cl55CommonCarrierRep nativeThreeColorModeMajorana *
          cl55CommonCarrierRep nativeThreeColorModeMajorana +
        cl55CommonCarrierRep nativeTwoComplementModeMajorana *
          cl55CommonCarrierRep nativeTwoComplementModeMajorana := by
  have hdecomp := congrArg cl55CommonCarrierRep
    nativeFiveModeMajorana_color_two_mode_decomposition
  rw [map_add] at hdecomp
  rw [hdecomp]
  calc
    (cl55CommonCarrierRep nativeThreeColorModeMajorana +
        cl55CommonCarrierRep nativeTwoComplementModeMajorana) *
        (cl55CommonCarrierRep nativeThreeColorModeMajorana +
          cl55CommonCarrierRep nativeTwoComplementModeMajorana) =
      cl55CommonCarrierRep nativeThreeColorModeMajorana *
          cl55CommonCarrierRep nativeThreeColorModeMajorana +
        (cl55CommonCarrierRep nativeThreeColorModeMajorana *
            cl55CommonCarrierRep nativeTwoComplementModeMajorana +
          cl55CommonCarrierRep nativeTwoComplementModeMajorana *
            cl55CommonCarrierRep nativeThreeColorModeMajorana) +
        cl55CommonCarrierRep nativeTwoComplementModeMajorana *
          cl55CommonCarrierRep nativeTwoComplementModeMajorana := by noncomm_ring
    _ = cl55CommonCarrierRep nativeThreeColorModeMajorana *
          cl55CommonCarrierRep nativeThreeColorModeMajorana +
        cl55CommonCarrierRep nativeTwoComplementModeMajorana *
          cl55CommonCarrierRep nativeTwoComplementModeMajorana := by
      rw [commonCarrier_color_complement_mass_anticommute]
      simp

/-- The five-mode common-carrier mass square is recovered from the two
sector weights `3` and `2`; this is the sector-resolved operator form of the
finite CAR mass identity. -/
theorem commonCarrier_fiveMode_mass_square_from_sectors :
    cl55CommonCarrierRep nativeFiveModeMajorana *
        cl55CommonCarrierRep nativeFiveModeMajorana =
      (5 : ℝ) • (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) := by
  rw [commonCarrier_fiveMode_mass_square_sector_sum]
  rcases commonCarrier_color_complement_mass_squares with ⟨hColor, hComplement⟩
  rw [hColor, hComplement]
  rw [← add_smul]
  norm_num

/-- The established sixth cyclotomic Higgs polynomial, evaluated at the
quadratic operator generated by the five-mode CAR mass, has the exact value
`21` times the identity. This is the all-mode specialization of the existing
operator cyclotomic polynomial, using the proved mass square. -/
theorem nativeFiveModeMajorana_cyclotomic_higgs :
    cyclotomicSix
        (nativeFiveModeMajorana * nativeFiveModeMajorana) =
      (21 : ℝ) • (1 : Cl55) := by
  rw [nativeFiveModeMajorana_square]
  simp only [cyclotomicSix, Algebra.smul_def]
  simp only [mul_one]
  calc
    (algebraMap ℝ Cl55) 5 * (algebraMap ℝ Cl55) 5 -
        (algebraMap ℝ Cl55) 5 + 1 =
      (algebraMap ℝ Cl55) ((5 : ℝ) * 5 - 5 + 1) := by
        rw [← map_mul (algebraMap ℝ Cl55) (5 : ℝ) 5,
          ← map_sub (algebraMap ℝ Cl55) ((5 : ℝ) * 5) 5,
          ← map_one (algebraMap ℝ Cl55),
          ← map_add (algebraMap ℝ Cl55) ((5 : ℝ) * 5 - 5) 1]
    _ = (algebraMap ℝ Cl55) 21 := by
      exact congrArg (algebraMap ℝ Cl55) (by norm_num)

/-- Calibration transports the all-mode cyclotomic Higgs value from the
native Clifford carrier to its finite Witt-matrix realization. -/
theorem fiveModeMajorana_cyclotomic_higgs :
    cyclotomicSix (fiveModeMajorana * fiveModeMajorana) =
      (21 : ℝ) • (1 : Stage 5) := by
  let E := exteriorCl55StageEquiv.trans exteriorToWittStageEquiv
  have hcal : E nativeFiveModeMajorana = fiveModeMajorana := by
    change exteriorToWittStageEquiv
      (exteriorCl55StageEquiv nativeFiveModeMajorana) = fiveModeMajorana
    have h := nativeFiveModeMajorana_calibration
    rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at h
    exact h
  have h := congrArg E nativeFiveModeMajorana_cyclotomic_higgs
  simpa only [cyclotomicSix, map_mul, map_sub, map_add, map_one,
    map_smul, hcal] using h

/-- The same cyclotomic Higgs evaluation holds on the actual polynomial–Fock
representation of the Clifford mass. The carrier map preserves the polynomial
and the identity, so this identifies the operator polynomial across the
already-proved CAR representation. -/
theorem commonCarrier_nativeFiveModeMajorana_cyclotomic_higgs :
    cyclotomicSix
        (cl55CommonCarrierRep nativeFiveModeMajorana *
          cl55CommonCarrierRep nativeFiveModeMajorana) =
      (21 : ℝ) • (1 : SuperOperator (Fin 5) (Fin 5 → ℝ)) := by
  have h := congrArg cl55CommonCarrierRep
    nativeFiveModeMajorana_cyclotomic_higgs
  simpa only [cyclotomicSix, map_mul, map_sub, map_add, map_one, map_smul] using h

/-- On the shared boson–fermion carrier, the native five-mode Clifford mass
is the sum of the actual fermionic creation and contraction operators. This
identifies the mass generator itself, not only its CAR relations or square. -/
theorem nativeFiveModeMajorana_commonCarrier_operator_sum :
    cl55CommonCarrierRep nativeFiveModeMajorana =
      ∑ i ∈ Finset.univ,
        (fermionAnnihilate (Fin 5) (Fin 5 → ℝ)
            (InfoGeometry.Clifford.SplitClifford55ExteriorSpinor.dualBasisVector i) +
          fermionCreate 5 i) := by
  unfold nativeFiveModeMajorana
  simp only [map_sum, map_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cl55_creation_eq_common_fermionAnnihilate,
    cl55_annihilation_eq_common_fermionCreate]

/-- The native Clifford mass and the finite CAR sum have the same image in
the UHF system, after transporting the CAR sum through the proved spinor
coordinate change. -/
theorem nativeFiveModeMajorana_UHF_image_calibration :
    ofStage 5 (cl55ToStage5 nativeFiveModeMajorana) =
      ofStage 5 (exteriorToWittStageEquiv.symm fiveModeMajorana) := by
  have hcal := nativeFiveModeMajorana_calibration
  rw [cl55ToStage5_eq_exteriorCl55StageEquiv] at hcal
  have hstage := congrArg exteriorToWittStageEquiv.symm hcal
  have hstage' : exteriorCl55StageEquiv nativeFiveModeMajorana =
      exteriorToWittStageEquiv.symm fiveModeMajorana := by
    simpa using hstage
  change ofStage 5 (exteriorCl55StageEquiv nativeFiveModeMajorana) = _
  exact congrArg (ofStage 5) hstage'

/-- The UHF colimit embedding preserves the finite sum of all five CAR modes. -/
theorem fiveModeMajoranaLimit_eq_sum :
    (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) =
      ofStage 5 fiveModeMajorana := by
  unfold fiveModeMajorana
  simp only [map_sum]

/-- Each finite CAR mass sector keeps its own quadratic weight in the UHF
limit: three for the color sector and two for the complementary sector. -/
theorem color_and_complement_mass_squares_at_limit :
    ofStage 5 threeColorModeMajorana * ofStage 5 threeColorModeMajorana =
        (3 : ℝ) • (1 : Limit) ∧
    ofStage 5 twoComplementModeMajorana *
        ofStage 5 twoComplementModeMajorana = (2 : ℝ) • (1 : Limit) := by
  constructor
  · rw [← (ofStage 5).map_mul, threeColorModeMajorana_square]
    rw [Algebra.smul_def', Algebra.smul_def']
    change ofStage 5 (algebraMap ℝ (Stage 5) 3 * 1) =
      realAlgebraMap 3 * 1
    rw [(ofStage 5).map_mul, (ofStage 5).map_one, realAlgebraMap_stage]
  · rw [← (ofStage 5).map_mul, twoComplementModeMajorana_square]
    rw [Algebra.smul_def', Algebra.smul_def']
    change ofStage 5 (algebraMap ℝ (Stage 5) 2 * 1) =
      realAlgebraMap 2 * 1
    rw [(ofStage 5).map_mul, (ofStage 5).map_one, realAlgebraMap_stage]

/-- The color and complementary CAR mass sectors continue to have zero mixed
anticommutator after passage to the UHF colimit. -/
theorem color_complement_mass_anticommute_at_limit :
    ofStage 5 threeColorModeMajorana * ofStage 5 twoComplementModeMajorana +
      ofStage 5 twoComplementModeMajorana * ofStage 5 threeColorModeMajorana =
        0 := by
  have h := congrArg (ofStage 5) threeColor_twoComplement_mass_anticommute
  simpa only [map_add, map_mul, map_zero] using h

/-- The full five-mode UHF mass is the sum of the embedded color and
complementary mass operators. -/
theorem fiveModeMajorana_limit_sector_decomposition :
    (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) =
      ofStage 5 threeColorModeMajorana +
        ofStage 5 twoComplementModeMajorana := by
  rw [fiveModeMajoranaLimit_eq_sum]
  simpa only [map_add] using
    congrArg (ofStage 5) fiveModeMajorana_color_two_mode_decomposition

/-- The squared five-mode UHF mass is the sum of the squared color and
complementary masses; no mixed term remains in the inductive limit. -/
theorem fiveModeMajorana_square_sector_sum_at_limit :
    (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) *
        (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) =
      ofStage 5 threeColorModeMajorana * ofStage 5 threeColorModeMajorana +
        ofStage 5 twoComplementModeMajorana *
          ofStage 5 twoComplementModeMajorana := by
  rw [fiveModeMajorana_limit_sector_decomposition]
  calc
    (ofStage 5 threeColorModeMajorana +
        ofStage 5 twoComplementModeMajorana) *
        (ofStage 5 threeColorModeMajorana +
          ofStage 5 twoComplementModeMajorana) =
      ofStage 5 threeColorModeMajorana * ofStage 5 threeColorModeMajorana +
        (ofStage 5 threeColorModeMajorana * ofStage 5 twoComplementModeMajorana +
          ofStage 5 twoComplementModeMajorana * ofStage 5 threeColorModeMajorana) +
        ofStage 5 twoComplementModeMajorana * ofStage 5 twoComplementModeMajorana := by
          noncomm_ring
    _ = ofStage 5 threeColorModeMajorana * ofStage 5 threeColorModeMajorana +
        ofStage 5 twoComplementModeMajorana * ofStage 5 twoComplementModeMajorana := by
          rw [color_complement_mass_anticommute_at_limit]
          simp

/-- The five-mode mass interaction retains its exact square after passage to
the actual UHF inductive limit. -/
theorem fiveModeMajorana_square_at_limit :
    (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) *
        (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) =
      (5 : ℝ) • (1 : Limit) := by
  rw [fiveModeMajoranaLimit_eq_sum, ← (ofStage 5).map_mul,
    fiveModeMajorana_square]
  rw [Algebra.smul_def', Algebra.smul_def']
  change ofStage 5 (algebraMap ℝ (Stage 5) 5 * 1) =
    realAlgebraMap 5 * 1
  rw [(ofStage 5).map_mul, (ofStage 5).map_one, realAlgebraMap_stage]

/-- The finite-stage cyclotomic Higgs identity is preserved by the actual
UHF connecting embedding, giving the same all-mode operator value in the
inductive limit. -/
theorem fiveModeMajorana_cyclotomic_higgs_at_limit :
    cyclotomicSix
        ((∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i)) *
          (∑ i ∈ Finset.univ, ofStage 5 (modeMajorana i))) =
      (21 : ℝ) • (1 : Limit) := by
  rw [fiveModeMajoranaLimit_eq_sum]
  have h := congrArg (ofStage 5) fiveModeMajorana_cyclotomic_higgs
  have hpoly :
      cyclotomicSix
          (ofStage 5 fiveModeMajorana * ofStage 5 fiveModeMajorana) =
        ofStage 5 ((21 : ℝ) • (1 : Stage 5)) := by
    simpa only [cyclotomicSix, map_mul, map_sub, map_add, map_one] using h
  calc
    cyclotomicSix
        (ofStage 5 fiveModeMajorana * ofStage 5 fiveModeMajorana) =
      ofStage 5 ((21 : ℝ) • (1 : Stage 5)) := hpoly
    _ = (21 : ℝ) • (1 : Limit) := by
      rw [Algebra.smul_def', Algebra.smul_def']
      change ofStage 5 ((algebraMap ℝ (Stage 5) 21) * 1) =
        realAlgebraMap 21 * 1
      rw [(ofStage 5).map_mul, (ofStage 5).map_one, realAlgebraMap_stage]

/-- The normalized-trace coercive estimate holds for every one of the five
finite CAR modes after its canonical embedding into the UHF colimit. -/
theorem each_mode_mass_peirce_coercivity_at_limit (i : Fin 5) (x : Limit) :
    (2 : ℝ) * normalizedTraceLimit
        (star (x - ofStage 5 (modeOccupation i) * x * ofStage 5 (modeOccupation i)) *
          (x - ofStage 5 (modeOccupation i) * x * ofStage 5 (modeOccupation i))) ≤
      normalizedTraceLimit
        (star x *
          (genV (ofStage 5 (modeOccupation i)) (ofStage 5 (modeMajorana i))
              (star (ofStage 5 (modeMajorana i))) * x +
            x * genV (ofStage 5 (modeOccupation i)) (ofStage 5 (modeMajorana i))
              (star (ofStage 5 (modeMajorana i))))) := by
  apply seed_unit_horizon_mass_coercivity_descends
    5 normalizedTraceLimit
    (fun n y => by rfl)
    (modeOccupation i) (modeMajorana i)
    (modeOccupation_structure i).1 (modeOccupation_structure i).2
    (modeMajorana_unit_horizon i).2 x

/-- Summing the five finite-stage coercivity estimates gives a simultaneous
all-mode energy bound in the UHF colimit. Each summand retains its own Peirce
pinch and Hodge horizon, so no commutativity between different modes is used. -/
theorem five_mode_mass_peirce_coercivity_energy_sum (x : Limit) :
    (2 : ℝ) *
        (∑ i : Fin 5,
          normalizedTraceLimit
            (star (x - ofStage 5 (modeOccupation i) * x * ofStage 5 (modeOccupation i)) *
              (x - ofStage 5 (modeOccupation i) * x * ofStage 5 (modeOccupation i)))) ≤
      ∑ i : Fin 5,
        normalizedTraceLimit
          (star x *
            (genV (ofStage 5 (modeOccupation i)) (ofStage 5 (modeMajorana i))
                (star (ofStage 5 (modeMajorana i))) * x +
              x * genV (ofStage 5 (modeOccupation i)) (ofStage 5 (modeMajorana i))
                (star (ofStage 5 (modeMajorana i))))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact each_mode_mass_peirce_coercivity_at_limit i x

end InfoGeometry.Canonical.Cl55AllModeMassCoercivity

end
