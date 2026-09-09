import Mathlib
import InfoGeometry.LLM.SpectralToken

/-!
# Symmetric and antisymmetric decomposition of a spectral twin

This is the finite algebraic form of the two-sheet split used by the
spectral-token layer.  The involution is the existing `SpectralToken.swap`;
the two components below are its `+1` and `-1` eigenspace projections over
`ℂ`.  No analytic or physical interpretation is part of this file.
-/

namespace InfoGeometry.Canonical.SpectralTwinWaveDecomposition

noncomputable section

/-! ## The complex two-sheet carrier -/

abbrev Token := InfoGeometry.LLM.SpectralToken.SpectralToken ℂ

def symmetric (t : Token) : Token :=
  ⟨(t.primal + t.dual) / 2, (t.primal + t.dual) / 2⟩

def antisymmetric (t : Token) : Token :=
  ⟨(t.primal - t.dual) / 2, (t.dual - t.primal) / 2⟩

@[simp] theorem symmetric_primal (t : Token) :
    (symmetric t).primal = (t.primal + t.dual) / 2 := rfl

@[simp] theorem symmetric_dual (t : Token) :
    (symmetric t).dual = (t.primal + t.dual) / 2 := rfl

@[simp] theorem antisymmetric_primal (t : Token) :
    (antisymmetric t).primal = (t.primal - t.dual) / 2 := rfl

@[simp] theorem antisymmetric_dual (t : Token) :
    (antisymmetric t).dual = (t.dual - t.primal) / 2 := rfl

theorem symmetric_fixed (t : Token) :
    InfoGeometry.LLM.SpectralToken.SpectralToken.swap (symmetric t) = symmetric t := by
  rfl

theorem antisymmetric_negated (t : Token) :
    InfoGeometry.LLM.SpectralToken.SpectralToken.swap (antisymmetric t) =
      ⟨-(antisymmetric t).primal, -(antisymmetric t).dual⟩ := by
  cases t with
  | mk p d =>
      change
        InfoGeometry.LLM.SpectralToken.SpectralToken.mk ((d - p) / 2) ((p - d) / 2) =
          InfoGeometry.LLM.SpectralToken.SpectralToken.mk
            (-((p - d) / 2)) (-((d - p) / 2))
      congr 1 <;> ring

theorem reconstruct (t : Token) :
    (symmetric t).primal + (antisymmetric t).primal = t.primal ∧
    (symmetric t).dual + (antisymmetric t).dual = t.dual := by
  constructor <;> simp [symmetric, antisymmetric, sub_eq_add_neg]
  · ring
  · ring

theorem swap_eigenvalue_characterization (t : Token)
    (hs : InfoGeometry.LLM.SpectralToken.SpectralToken.swap t = t) : t.primal = t.dual := by
  have h := congrArg (fun u : Token => u.primal) hs
  simpa [eq_comm] using h

theorem antisymmetric_characterization (t : Token) :
    (antisymmetric t).dual = -(antisymmetric t).primal := by
  simp [antisymmetric]
  ring

end
end InfoGeometry.Canonical.SpectralTwinWaveDecomposition
