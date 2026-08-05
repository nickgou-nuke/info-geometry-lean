import Mathlib
import InfoGeometry.Clifford.Cl55SpinorDimensionReadout
import InfoGeometry.Algebra.ZornMatrix

/-!
# A finite real coordinate readout from the `Cl(5,5)` spinor carrier

`SpinorSpace 5` is the explicit real carrier `Fin 32 → ℝ`.  This owner
extracts eight selected coordinates and packages them as the native Zorn
vector-matrix carrier.  It is a linear readout only; no Clifford/Zorn
isomorphism, triality representation, or multiplicative intertwining is
claimed.
-/

namespace InfoGeometry.Clifford.SpinorRep

open InfoGeometry.Algebra

abbrev Spinor32 := SpinorSpace 5

def zornAIndex : Fin 32 := 0
def zornBIndex : Fin 32 := 7

def zornVIndex (i : Fin 3) : Fin 32 :=
  ⟨i.1 + 1, by omega⟩

def zornWIndex (i : Fin 3) : Fin 32 :=
  ⟨i.1 + 4, by omega⟩

/-- The explicit coordinate readout `Fin 32 → ℝ → ZornMatrix ℝ`. -/
def spinor32ZornReadout : Spinor32 →ₗ[ℝ] ZornMatrix ℝ where
  toFun ψ :=
    { a := ψ zornAIndex
      v := fun i => ψ (zornVIndex i)
      w := fun i => ψ (zornWIndex i)
      b := ψ zornBIndex }
  map_add' ψ φ := by
    apply ZornMatrix.ext
    · rfl
    · funext i
      rfl
    · funext i
      rfl
    · rfl
  map_smul' c ψ := by
    apply ZornMatrix.ext
    · rfl
    · funext i
      rfl
    · funext i
      rfl
    · rfl

@[simp] theorem spinor32ZornReadout_a (ψ : Spinor32) :
    (spinor32ZornReadout ψ).a = ψ zornAIndex :=
  rfl

@[simp] theorem spinor32ZornReadout_b (ψ : Spinor32) :
    (spinor32ZornReadout ψ).b = ψ zornBIndex :=
  rfl

@[simp] theorem spinor32ZornReadout_v (ψ : Spinor32) (i : Fin 3) :
    (spinor32ZornReadout ψ).v i = ψ (zornVIndex i) :=
  rfl

@[simp] theorem spinor32ZornReadout_w (ψ : Spinor32) (i : Fin 3) :
    (spinor32ZornReadout ψ).w i = ψ (zornWIndex i) :=
  rfl

theorem spinor32ZornReadout_zero :
    spinor32ZornReadout (0 : Spinor32) = 0 := by
  change spinor32ZornReadout (0 : Spinor32) = ZornMatrix.zero
  apply ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem spinor32ZornReadout_add (ψ φ : Spinor32) :
    spinor32ZornReadout (ψ + φ) =
      spinor32ZornReadout ψ + spinor32ZornReadout φ := by
  change spinor32ZornReadout (ψ + φ) =
    ZornMatrix.add (spinor32ZornReadout ψ) (spinor32ZornReadout φ)
  apply ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem spinor32ZornReadout_smul (c : ℝ) (ψ : Spinor32) :
    spinor32ZornReadout (c • ψ) =
      c • spinor32ZornReadout ψ := by
  change spinor32ZornReadout (c • ψ) =
    ZornMatrix.smul c (spinor32ZornReadout ψ)
  apply ZornMatrix.ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

end InfoGeometry.Clifford.SpinorRep
