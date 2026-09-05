import Mathlib
import InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

/-!
# BdG even-sector compression and the centered Soloviev normal form

The two-mode CAR carrier contains the even sector spanned by the empty and
paired states. The pairing Hamiltonian compresses to the standard traceless
`2 × 2` BdG block. A finite Soloviev block is exactly an affine scalar shift
of this traceless block after the substitution `ξ = ω / 2`.

This is a matrix normal-form and compression theorem, not an identification of
a microscopic BdG mean-field model with the full quasiparticle--phonon model.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearBdGSolovievCompression

open InfoGeometry.Physics.NuclearTwoModeCARFiveGrade

abbrev EvenSector := Fin 2 → ℂ
abbrev EvenEnd := Module.End ℂ EvenSector
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- Inclusion of the empty/paired sector. -/
def evenEmbed : EvenSector →ₗ[ℂ] Fock4 where
  toFun φ := ![φ 0, 0, 0, φ 1]
  map_add' φ ψ := by
    ext i
    fin_cases i <;> simp
  map_smul' c φ := by
    ext i
    fin_cases i <;> simp

/-- Projection onto the empty/paired coordinates. -/
def evenProject : Fock4 →ₗ[ℂ] EvenSector where
  toFun ψ := ![ψ 0, ψ 3]
  map_add' ψ φ := by
    ext i
    fin_cases i <;> simp
  map_smul' c ψ := by
    ext i
    fin_cases i <;> simp

@[simp] theorem evenEmbed_apply (φ : EvenSector) :
    evenEmbed φ = ![φ 0, 0, 0, φ 1] := rfl

@[simp] theorem evenProject_apply (ψ : Fock4) :
    evenProject ψ = ![ψ 0, ψ 3] := rfl

@[simp] theorem evenProject_evenEmbed :
    evenProject.comp evenEmbed = LinearMap.id := by
  apply LinearMap.ext
  intro φ
  ext i
  fin_cases i <;> simp

/-- Four-state pairing Hamiltonian. -/
def fullBdG (ξ Δ : ℂ) : Op :=
  ξ • gradeCartan + Δ • (pairCreation + pairAnnihilation)

/-- Traceless two-dimensional BdG block. -/
def bdgBlock (ξ Δ : ℂ) : Mat2 :=
  !![-ξ, Δ;
     Δ, ξ]

/-- Compression to the even sector. -/
def compressedBdG (ξ Δ : ℂ) : EvenEnd :=
  evenProject.comp ((fullBdG ξ Δ).comp evenEmbed)

@[simp] theorem compressedBdG_apply (ξ Δ : ℂ) (φ : EvenSector) :
    compressedBdG ξ Δ φ =
      ![-ξ * φ 0 + Δ * φ 1,
        Δ * φ 0 + ξ * φ 1] := by
  ext i
  fin_cases i <;>
    simp [compressedBdG, fullBdG, Module.End.mul_apply] <;>
    ring

/-- Compression equals matrix multiplication by the BdG block. -/
theorem compressedBdG_eq_mulVec (ξ Δ : ℂ) (φ : EvenSector) :
    compressedBdG ξ Δ φ = Matrix.mulVec (bdgBlock ξ Δ) φ := by
  ext i
  fin_cases i <;>
    simp [compressedBdG_apply, bdgBlock, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    ring

/-- Characteristic determinant of the traceless BdG block. -/
theorem bdgBlock_characteristic (ξ Δ E : ℂ) :
    Matrix.det (bdgBlock ξ Δ - E • (1 : Mat2)) =
      E ^ 2 - ξ ^ 2 - Δ ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [bdgBlock]
  ring

/-- Squaring gives the scalar spectral invariant. -/
theorem bdgBlock_sq (ξ Δ : ℂ) :
    bdgBlock ξ Δ * bdgBlock ξ Δ =
      (ξ ^ 2 + Δ ^ 2) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bdgBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- Finite two-sector Soloviev matrix. -/
def solovievBlock (Eqp ω V : ℂ) : Mat2 :=
  !![Eqp, V;
     V, Eqp + ω]

/-- Soloviev is a scalar center plus a traceless BdG block. -/
theorem solovievBlock_eq_center_add_bdg
    (Eqp ω V : ℂ) :
    solovievBlock Eqp ω V =
      (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [solovievBlock, bdgBlock] <;>
    ring

/-- Secular determinant. -/
theorem solovievBlock_characteristic (Eqp ω V E : ℂ) :
    Matrix.det (solovievBlock Eqp ω V - E • (1 : Mat2)) =
      (Eqp - E) * (Eqp + ω - E) - V ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [solovievBlock]
  ring

/-- Four-state operator whose even compression is the Soloviev block. -/
def fullCenteredSoloviev (Eqp ω V : ℂ) : Op :=
  (Eqp + ω / 2) • 1 + fullBdG (ω / 2) V

/-- Compression of the centered four-state operator. -/
def compressedCenteredSoloviev (Eqp ω V : ℂ) : EvenEnd :=
  evenProject.comp ((fullCenteredSoloviev Eqp ω V).comp evenEmbed)

@[simp] theorem compressedCenteredSoloviev_apply
    (Eqp ω V : ℂ) (φ : EvenSector) :
    compressedCenteredSoloviev Eqp ω V φ =
      ![Eqp * φ 0 + V * φ 1,
        V * φ 0 + (Eqp + ω) * φ 1] := by
  ext i
  fin_cases i <;>
    simp [compressedCenteredSoloviev, fullCenteredSoloviev,
      fullBdG, Module.End.mul_apply] <;>
    ring

/-- The compressed operator is exactly the Soloviev matrix action. -/
theorem compressedCenteredSoloviev_eq_mulVec
    (Eqp ω V : ℂ) (φ : EvenSector) :
    compressedCenteredSoloviev Eqp ω V φ =
      Matrix.mulVec (solovievBlock Eqp ω V) φ := by
  ext i
  fin_cases i <;>
    simp [compressedCenteredSoloviev_apply, solovievBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- Exact CAR-pair/BdG/Soloviev packet. -/
theorem nuclear_bdg_soloviev_compression_packet
    (Eqp ω V ξ Δ E : ℂ) :
    compressedBdG ξ Δ =
        evenProject.comp ((fullBdG ξ Δ).comp evenEmbed) ∧
      bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) • (1 : Mat2) ∧
      solovievBlock Eqp ω V =
        (Eqp + ω / 2) • (1 : Mat2) + bdgBlock (ω / 2) V ∧
      Matrix.det (solovievBlock Eqp ω V - E • (1 : Mat2)) =
        (Eqp - E) * (Eqp + ω - E) - V ^ 2 := by
  exact ⟨rfl, bdgBlock_sq ξ Δ,
    solovievBlock_eq_center_add_bdg Eqp ω V,
    solovievBlock_characteristic Eqp ω V E⟩

end InfoGeometry.Physics.NuclearBdGSolovievCompression
