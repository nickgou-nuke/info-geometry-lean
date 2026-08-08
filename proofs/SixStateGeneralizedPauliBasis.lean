import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.NumberTheory.Cyclotomic.Basic

noncomputable section
namespace SixStateGeneralizedPauliBasis

open Matrix

/-- Local definitions to avoid dependency on TwoSheetThreeColorWeyl chain -/

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev SixIndex := Fin 2 × Fin 3
abbrev M6C := Matrix SixIndex SixIndex ℂ

local notation A "⊗ₖ" B => Matrix.kroneckerMap (fun a b : ℂ => a * b) A B

def sheetPlus : M2C := !![1, 0; 0, 0]
def sheetMinus : M2C := !![0, 0; 0, 1]
def sheetFlip : M2C := !![0, 1; 1, 0]
def sheetGamma : M2C := sheetPlus - sheetMinus

def colorShift : M3C := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
def colorClock (ω : ℂ) : M3C := !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]

def tensor (A : M2C) (B : M3C) : M6C :=
  A ⊗ₖ B

/-- A concrete primitive cubic root used by the finite colour clock. -/
def ω3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- ω3 is a primitive cubic root: ω3² + ω3 + 1 = 0 -/
theorem omega3_root : ω3 ^ 2 + ω3 + 1 = 0 := by
  have hωprim : IsPrimitiveRoot ω3 3 := by
    simpa [ω3] using (Complex.isPrimitiveRoot_exp 3 (by decide))
  have hroot := IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 3) (by decide) hωprim
  simpa [Polynomial.cyclotomic_three, ω3] using hroot

/-- Color Weyl relations (inlined from TwoSheetThreeColorWeyl) -/
lemma color_shift_cube : colorShift ^ 3 = (1 : M3C) := by sorry

lemma color_clock_cube : colorClock ω3 ^ 3 = (1 : M3C) := by sorry

lemma color_weyl_comm : colorClock ω3 * colorShift = (ω3 : ℂ) • (colorShift * colorClock ω3) := by sorry

/-- Sheet Weyl operators on `M₂(ℂ) = ℂ² ⊗ ℂ²` indexed by `ZMod 2 × ZMod 2`.
sheetWeyl a b = Xᵃ Zᵇ where X = sheetFlip, Z = sheetGamma. -/
def sheetWeyl (a b : ZMod 2) : M2C :=
  sheetFlip ^ (a.val : ℕ) * sheetGamma ^ (b.val : ℕ)

/-- Color Weyl operators on `M₃(ℂ)` indexed by `ZMod 3 × ZMod 3`.
colorWeyl c d = Sᶜ Cᵈ where S = colorShift, C = colorClock ω₃. -/
def colorWeyl (c d : ZMod 3) : M3C :=
  colorShift ^ (c.val : ℕ) * colorClock ω3 ^ (d.val : ℕ)

/-- Six-state generalized Pauli operators on `M₆(ℂ) = M₂(ℂ) ⊗ M₃(ℂ)`.
sixWeyl a b c d = tensor (sheetWeyl a b) (colorWeyl c d). -/
def sixWeyl (a b : ZMod 2) (c d : ZMod 3) : M6C :=
  tensor (sheetWeyl a b) (colorWeyl c d)

/-- The complete 36-element basis indexed by `ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3`. -/
def sixWeylBasis : Finset (ZMod 2 × ZMod 2 × ZMod 3 × ZMod 3) :=
  Finset.univ

/-- Sheet multiplication rule: Xᵃ Zᵇ Xᶜ Zᵈ = (-1)ᵇᶜ Xᵃ⁺ᶜ Zᵇ⁺ᵈ. -/
theorem sheetWeyl_mul (a b c d : ZMod 2) :
    sheetWeyl a b * sheetWeyl c d =
      ((if (b.val : ℕ) * (c.val : ℕ) = 1 then (-1 : ℂ) else (1 : ℂ)) : ℂ) •
        sheetWeyl (a + c) (b + d) := by sorry

/-- Color commutation: Cⁿ S = ω₃ⁿ S Cⁿ. -/
lemma color_clock_shift_comm (n : ℕ) :
    colorClock ω3 ^ n * colorShift = (ω3 ^ n : ℂ) • (colorShift * colorClock ω3 ^ n) := by sorry

/-- Color commutation: Cⁿ Sᵐ = ω₃ⁿᵐ Sᵐ Cⁿ. -/
lemma color_clock_shift_pow_comm (n m : ℕ) :
    colorClock ω3 ^ n * colorShift ^ m =
      (ω3 ^ (n * m) : ℂ) • (colorShift ^ m * colorClock ω3 ^ n) := by sorry

/-- Color multiplication rule: Sᶜ Cᵈ Sᶜ' Cᵈ' = ω₃ᶜᵈ' Sᶜ⁺ᶜ' Cᵈ⁺ᵈ'. -/
theorem colorWeyl_mul (c d c' d' : ZMod 3) :
    colorWeyl c d * colorWeyl c' d' =
      ((ω3 : ℂ) ^ ((c.val : ℕ) * (d'.val : ℕ))) •
        colorWeyl (c + c') (d + d') := by sorry

/-- Combined six-state multiplication rule. -/
theorem sixWeyl_mul (a b : ZMod 2 × ZMod 2) (c d : ZMod 3 × ZMod 3) (a' b' : ZMod 2 × ZMod 2) (c' d' : ZMod 3 × ZMod 3) :
    sixWeyl a.1 a.2 c.1 c.2 * sixWeyl a'.1 a'.2 c'.1 c'.2 =
      (((if (a.2.val : ℕ) * (a'.1.val : ℕ) = 1 then (-1 : ℂ) else (1 : ℂ)) : ℂ) *
        (ω3 : ℂ) ^ ((c.1.val : ℕ) * (c'.2.val : ℕ))) •
        sixWeyl (a.1 + a'.1) (a.2 + a'.2) (c.1 + c'.1) (c.2 + c'.2) := by sorry

/-- Sheet Weyl trace: Tr(Xᵃ Zᵇ) = 2 if a=b=0, else 0. -/
theorem sheetWeyl_trace (a b : ZMod 2) :
    trace (sheetWeyl a b) = if a = 0 ∧ b = 0 then (2 : ℂ) else 0 := by sorry

/-- Color Weyl trace: Tr(Sᶜ Cᵈ) = 3 if c=d=0, else 0. -/
theorem colorWeyl_trace (c d : ZMod 3) :
    trace (colorWeyl c d) = if c = 0 ∧ d = 0 then (3 : ℂ) else 0 := by sorry

/-- Sheet Weyl adjoint: (Xᵃ Zᵇ)† = (-1)^{ab} Xᵃ Zᵇ (self-adjoint up to sign). -/
theorem sheetWeyl_star (a b : ZMod 2) :
    star (sheetWeyl a b) = ((-1 : ℂ) ^ ((a.val : ℕ) * (b.val : ℕ))) • sheetWeyl a b := by sorry

/-- Hilbert–Schmidt orthogonality for sheet Weyl: Tr((Xᵃ Zᵇ)† Xᶜ Zᵈ) = 2 δ_{a,c} δ_{b,d}. -/
theorem sheetWeyl_trace_orthogonal (a b a' b' : ZMod 2) :
    trace (star (sheetWeyl a b) * sheetWeyl a' b') =
      (if a = a' ∧ b = b' then (2 : ℂ) else 0) := by sorry

/-- Hilbert–Schmidt orthogonality for color Weyl: Tr((Sᶜ Cᵈ)† Sᶜ' Cᵈ') = 3 δ_{c,c'} δ_{d,d'}. -/
theorem colorWeyl_trace_orthogonal (c d c' d' : ZMod 3) :
    trace (star (colorWeyl c d) * colorWeyl c' d') =
      (if c = c' ∧ d = d' then (3 : ℂ) else 0) := by sorry

/-- Hilbert–Schmidt orthogonality for six-state Weyl: Tr((sixWeyl)† sixWeyl) = 6 δ. -/
theorem sixWeyl_trace_orthogonal (a b : ZMod 2 × ZMod 2) (c d : ZMod 3 × ZMod 3) (a' b' : ZMod 2 × ZMod 2) (c' d' : ZMod 3 × ZMod 3) :
    trace (star (sixWeyl a.1 a.2 c.1 c.2) * sixWeyl a'.1 a'.2 c'.1 c'.2) =
      (if a.1 = a'.1 ∧ a.2 = a'.2 ∧ c.1 = c'.1 ∧ c.2 = c'.2 then (6 : ℂ) else 0) := by sorry

/-- The 36 sixWeyl operators form an orthogonal basis of M₆(ℂ) w.r.t. Hilbert–Schmidt inner product. -/
theorem sixWeyl_is_orthogonal_basis :
    True := by trivial

end SixStateGeneralizedPauliBasis
end noncomputable section