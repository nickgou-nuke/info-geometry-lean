import InfoGeometry.Canonical.HestenesCircularSheetCAR
import InfoGeometry.Krein.TwoSheetKreinIdealBridge

/-!
# Native finite Hestenes--Krein two-sheet bridge

This owner promotes the already native Pauli sheet matrices into the Krein
ideal-transport API.  It remains a finite matrix theorem package; no
Clifford-algebra identification is asserted here.
-/

namespace InfoGeometry.Krein.HestenesKreinFinite

open InfoGeometry.Canonical.ChiralStokesPauliBasis
open InfoGeometry.Krein

noncomputable section


abbrev fundamentalSymmetry : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix := sheetFlip
abbrev fPlus : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix := uPlus
abbrev fMinus : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix := uMinus

@[simp] theorem fundamentalSymmetry_sq :
    fundamentalSymmetry * fundamentalSymmetry = (1 : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) := by
  unfold fundamentalSymmetry
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetIdentity, Matrix.mul_apply, Fin.sum_univ_two]

theorem fundamentalSymmetry_selfAdjoint :
    Matrix.conjTranspose fundamentalSymmetry = fundamentalSymmetry := by
  ext i j
  fin_cases i <;> fin_cases j <;>
      simp [fundamentalSymmetry, sheetFlip, Matrix.conjTranspose, Matrix.transpose,
      Matrix.conjTranspose_apply]

noncomputable def sheetKreinAdjoint (A : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix :=
  fundamentalSymmetry * Matrix.conjTranspose A * fundamentalSymmetry

theorem sheetKreinAdjoint_involutive (A : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) :
    sheetKreinAdjoint (sheetKreinAdjoint A) = A := by
  simp only [sheetKreinAdjoint, Matrix.conjTranspose_mul,
    fundamentalSymmetry_selfAdjoint, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, fundamentalSymmetry_sq, one_mul, mul_one]

@[simp] theorem fPlus_idempotent : fPlus * fPlus = fPlus :=
  uPlus_idempotent

@[simp] theorem fMinus_idempotent : fMinus * fMinus = fMinus :=
  uMinus_idempotent

@[simp] theorem fPlus_mul_fMinus : fPlus * fMinus = 0 :=
  uPlus_mul_uMinus

@[simp] theorem fMinus_mul_fPlus : fMinus * fPlus = 0 :=
  uMinus_mul_uPlus

theorem fPlus_selfAdjoint : Matrix.conjTranspose fPlus = fPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fPlus, uPlus, sheetIdentity, sheetParity,
      Matrix.conjTranspose, Matrix.transpose, Matrix.conjTranspose_apply] <;>
    norm_num [map_ofNat]

theorem fMinus_selfAdjoint : Matrix.conjTranspose fMinus = fMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fMinus, uMinus, sheetIdentity, sheetParity,
      Matrix.conjTranspose, Matrix.transpose, Matrix.conjTranspose_apply] <;>
    norm_num [map_ofNat]

@[simp] theorem fPlus_add_fMinus : fPlus + fMinus = (1 : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix) :=
  by
    unfold fPlus fMinus uPlus uMinus
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sheetIdentity, sheetParity] <;> norm_num [div_eq_mul_inv]

@[simp] theorem fundamentalSymmetry_fPlus_fundamentalSymmetry :
    fundamentalSymmetry * fPlus * fundamentalSymmetry = fMinus := by
  unfold fundamentalSymmetry fPlus fMinus uPlus uMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, sheetIdentity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

@[simp] theorem fundamentalSymmetry_fMinus_fundamentalSymmetry :
    fundamentalSymmetry * fMinus * fundamentalSymmetry = fPlus := by
  unfold fundamentalSymmetry fPlus fMinus uPlus uMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetFlip, sheetParity, sheetIdentity, Matrix.mul_apply,
      Fin.sum_univ_two] <;> norm_num [div_eq_mul_inv]

theorem diracConjugate_fPlus_left_to_fMinus_right {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ leftPrincipal fPlus) :
    fundamentalSymmetry * Matrix.conjTranspose x ∈ rightPrincipal fMinus := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨fundamentalSymmetry * Matrix.conjTranspose a, ?_⟩
  rw [Matrix.conjTranspose_mul, fPlus_selfAdjoint]
  calc
    fMinus * (fundamentalSymmetry * Matrix.conjTranspose a) =
        (fundamentalSymmetry * fPlus * fundamentalSymmetry) *
          (fundamentalSymmetry * Matrix.conjTranspose a) := by
            rw [fundamentalSymmetry_fPlus_fundamentalSymmetry]
    _ = fundamentalSymmetry * (fPlus * Matrix.conjTranspose a) := by
      calc
        fundamentalSymmetry * fPlus * fundamentalSymmetry *
            (fundamentalSymmetry * Matrix.conjTranspose a) =
            fundamentalSymmetry * fPlus *
              (fundamentalSymmetry * fundamentalSymmetry) *
              Matrix.conjTranspose a := by simp only [mul_assoc]
        _ = fundamentalSymmetry * (fPlus * Matrix.conjTranspose a) := by
          rw [fundamentalSymmetry_sq]
          simp only [mul_one, mul_assoc]

theorem diracConjugate_fMinus_left_to_fPlus_right {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ leftPrincipal fMinus) :
    fundamentalSymmetry * Matrix.conjTranspose x ∈ rightPrincipal fPlus := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨fundamentalSymmetry * Matrix.conjTranspose a, ?_⟩
  rw [Matrix.conjTranspose_mul, fMinus_selfAdjoint]
  calc
    fPlus * (fundamentalSymmetry * Matrix.conjTranspose a) =
        (fundamentalSymmetry * fMinus * fundamentalSymmetry) *
          (fundamentalSymmetry * Matrix.conjTranspose a) := by
            rw [fundamentalSymmetry_fMinus_fundamentalSymmetry]
    _ = fundamentalSymmetry * (fMinus * Matrix.conjTranspose a) := by
      calc
        fundamentalSymmetry * fMinus * fundamentalSymmetry *
            (fundamentalSymmetry * Matrix.conjTranspose a) =
            fundamentalSymmetry * fMinus *
              (fundamentalSymmetry * fundamentalSymmetry) *
              Matrix.conjTranspose a := by simp only [mul_assoc]
        _ = fundamentalSymmetry * (fMinus * Matrix.conjTranspose a) := by
          rw [fundamentalSymmetry_sq]
          simp only [mul_one, mul_assoc]

theorem kreinConjugate_fPlus_leftPrincipal_iff {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix} :
    x ∈ leftPrincipal fPlus ↔
      kreinConjugate fundamentalSymmetry x ∈ leftPrincipal fMinus :=
  kreinConjugate_leftPrincipal_iff fundamentalSymmetry fPlus fMinus
    fundamentalSymmetry_sq fundamentalSymmetry_fPlus_fundamentalSymmetry

theorem kreinConjugate_fPlus_fMinus_corner_iff {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix} :
    x ∈ peirceCorner fPlus fMinus ↔
      kreinConjugate fundamentalSymmetry x ∈ peirceCorner fMinus fPlus :=
  kreinConjugate_peirceCorner_iff fundamentalSymmetry fPlus fMinus
    fundamentalSymmetry_sq fundamentalSymmetry_fPlus_fundamentalSymmetry
    fundamentalSymmetry_fMinus_fundamentalSymmetry

theorem fPlus_corner_eq_scalar_line {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ peirceCorner fPlus fPlus) :
    ∃ c : ℂ, x = c • fPlus := by
  change fPlus * x * fPlus = x at hx
  refine ⟨x 0 0, ?_⟩
  have hhalf : (2⁻¹ : ℂ) * (1 + 1) = 1 := by norm_num
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [fPlus, uPlus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Matrix.vecHead, Fin.sum_univ_two, hhalf] using
      (congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 0 0) hx).symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 0 1) hx
    simpa [fPlus, uPlus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_two] using h.symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 1 0) hx
    simpa [fPlus, uPlus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_two] using h.symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 1 1) hx
    simpa [fPlus, uPlus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_two] using h.symm

theorem fMinus_corner_eq_scalar_line {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ peirceCorner fMinus fMinus) :
    ∃ c : ℂ, x = c • fMinus := by
  change fMinus * x * fMinus = x at hx
  refine ⟨x 1 1, ?_⟩
  have hhalf : (2⁻¹ : ℂ) * (1 + 1) = 1 := by norm_num
  ext i j
  fin_cases i <;> fin_cases j
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 0 0) hx
    simpa [fMinus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Matrix.vecHead, Fin.sum_univ_two, hhalf] using h.symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 0 1) hx
    simpa [fMinus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_two] using h.symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 1 0) hx
    simpa [fMinus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Fin.sum_univ_two] using h.symm
  · have h := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 1 1) hx
    simpa [fMinus, uMinus, sheetIdentity, sheetParity, Matrix.mul_apply,
      Matrix.vecMul, Matrix.vecTail, Matrix.vecHead, Function.comp_def,
      Fin.sum_univ_two, hhalf] using h.symm

theorem mem_fPlus_corner_iff_exists_scalar {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix} :
    x ∈ peirceCorner fPlus fPlus ↔ ∃ c : ℂ, x = c • fPlus := by
  constructor
  · exact fPlus_corner_eq_scalar_line
  · rintro ⟨c, rfl⟩
    change fPlus * (c • fPlus) * fPlus = c • fPlus
    simp [mul_smul, smul_mul_assoc, fPlus_idempotent]

theorem mem_fMinus_corner_iff_exists_scalar {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix} :
    x ∈ peirceCorner fMinus fMinus ↔ ∃ c : ℂ, x = c • fMinus := by
  constructor
  · exact fMinus_corner_eq_scalar_line
  · rintro ⟨c, rfl⟩
    change fMinus * (c • fMinus) * fMinus = c • fMinus
    simp [mul_smul, smul_mul_assoc, fMinus_idempotent]

theorem fPlus_scalar_coefficient_unique {c d : ℂ}
    (h : c • fPlus = d • fPlus) : c = d := by
  have h00 := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 0 0) h
  simpa [fPlus, uPlus, sheetIdentity, sheetParity] using h00

theorem fMinus_scalar_coefficient_unique {c d : ℂ}
    (h : c • fMinus = d • fMinus) : c = d := by
  have h11 := congrArg (fun M : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix => M 1 1) h
  simpa [fMinus, uMinus, sheetIdentity, sheetParity] using h11

theorem fPlus_corner_existsUnique_scalar {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ peirceCorner fPlus fPlus) :
    ∃! c : ℂ, x = c • fPlus := by
  obtain ⟨c, hc⟩ := fPlus_corner_eq_scalar_line hx
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (fPlus_scalar_coefficient_unique (hc.symm.trans hd)).symm

theorem fMinus_corner_existsUnique_scalar {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix}
    (hx : x ∈ peirceCorner fMinus fMinus) :
    ∃! c : ℂ, x = c • fMinus := by
  obtain ⟨c, hc⟩ := fMinus_corner_eq_scalar_line hx
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (fMinus_scalar_coefficient_unique (hc.symm.trans hd)).symm

theorem fPlus_corner_set_eq_smul_range :
    {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix | x ∈ peirceCorner fPlus fPlus} =
      Set.range (fun c : ℂ => c • fPlus) := by
  ext x
  constructor
  · intro hx
    rcases fPlus_corner_eq_scalar_line hx with ⟨c, hc⟩
    exact Set.mem_range.mpr ⟨c, hc.symm⟩
  · intro hx
    rcases Set.mem_range.mp hx with ⟨c, rfl⟩
    exact (mem_fPlus_corner_iff_exists_scalar (x := c • fPlus)).mpr ⟨c, rfl⟩

theorem fMinus_corner_set_eq_smul_range :
    {x : InfoGeometry.Canonical.ChiralStokesPauliBasis.SheetMatrix | x ∈ peirceCorner fMinus fMinus} =
      Set.range (fun c : ℂ => c • fMinus) := by
  ext x
  constructor
  · intro hx
    rcases fMinus_corner_eq_scalar_line hx with ⟨c, hc⟩
    exact Set.mem_range.mpr ⟨c, hc.symm⟩
  · intro hx
    rcases Set.mem_range.mp hx with ⟨c, rfl⟩
    exact (mem_fMinus_corner_iff_exists_scalar (x := c • fMinus)).mpr ⟨c, rfl⟩

end

end InfoGeometry.Krein.HestenesKreinFinite
