import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.LogCftMonodromyBridge

Thin canonical bridge from the logarithmic-CFT monodromy owner file.

This surface only re-exports the finite upper-triangular and lower-parabolic
matrix facts already proved in the owner file. It does not assert any analytic
continuation, CFT completeness, or geometric interpretation beyond the matrix
identities themselves.
-/

namespace LogCftMonodromyBridge

open InfoGeometry.Clifford.LogCftMonodromy
open Matrix

/-- The nilpotent Jordan shear squares to zero. -/
theorem jordanNilpotent_sq :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent_sq (K := ℂ)

/-- Multiplication law for equal-diagonal upper-Jordan blocks. -/
theorem upperJordan_mul {K : Type*} [CommSemiring K] (a b c d : K) :
    upperJordan a b * upperJordan c d =
      upperJordan (a * c) (a * d + b * c) :=
  InfoGeometry.Clifford.LogCftMonodromy.upperJordan_mul a b c d

/--
Power law for equal-diagonal upper-Jordan blocks.

This is the finite upper-triangular induction schema used by the monodromy
and logarithmic-cell lanes.
-/
theorem upperJordan_pow {K : Type*} [CommSemiring K] (a b : K) :
    ∀ n : ℕ,
      upperJordan a b ^ n =
        upperJordan (a ^ n) ((n : K) * b * a ^ (n - 1)) :=
  InfoGeometry.Clifford.LogCftMonodromy.upperJordan_pow (a := a) (b := b)

/-- Inductive power law for the Virasoro `L₀` Jordan cell. -/
theorem virasoroL0Cell_pow {K : Type*} [CommSemiring K] (h : K) (n : ℕ) :
    virasoroL0Cell h ^ n =
      upperJordan (h ^ n) ((n : K) * h ^ (n - 1)) :=
  InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell_pow (K := K) h n

/-- The logarithmic phase for one positive monodromy wrap. -/
noncomputable def lcftPhase (h : ℂ) : ℂ :=
  InfoGeometry.Clifford.LogCftMonodromy.lcftPhase h

/-- The universal logarithmic shear coefficient before multiplying by the phase. -/
noncomputable def logShearBase : ℂ :=
  InfoGeometry.Clifford.LogCftMonodromy.logShearBase

/-- The actual one-wrap shear coefficient. -/
noncomputable def logShear (h : ℂ) : ℂ :=
  InfoGeometry.Clifford.LogCftMonodromy.logShear h

/-- Hadjiivanov logarithmic monodromy for one wrap around a singularity. -/
noncomputable def hadjiivanovMonodromy (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy h

/-- The monodromy splits into a scalar phase and a nilpotent logarithmic shear. -/
theorem monodromy_decomposition (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        InfoGeometry.Clifford.LogCftMonodromy.monodromyNilpotentPart h :=
  InfoGeometry.Clifford.LogCftMonodromy.monodromy_decomposition h

/-- The lower Jordan block is the transpose of the upper one. -/
theorem lowerJordan_eq_transpose {K : Type*} [Zero K] (a b : K) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerJordan a b = (upperJordan a b)ᵀ :=
  InfoGeometry.Clifford.LogCftMonodromy.lowerJordan_eq_transpose a b

/-- The lower Hadjiivanov monodromy is the transpose of the upper one. -/
theorem lowerHadjiivanovMonodromy_eq_transpose (h : ℂ) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy h =
      (hadjiivanovMonodromy h)ᵀ :=
  InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy_eq_transpose h

/-- The lower Hadjiivanov monodromy after `n` wraps has the winding law. -/
theorem lowerHadjiivanovMonodromy_pow_winding (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) •
            InfoGeometry.Clifford.LogCftMonodromy.lowerJordanNilpotent) :=
  InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy_pow_winding h n

/-- The lower Hadjiivanov monodromy power law in original matrix form. -/
theorem lowerHadjiivanovMonodromy_pow_original (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy h ^ n =
      InfoGeometry.Clifford.LogCftMonodromy.lowerJordan (lcftPhase h ^ n)
        ((n : ℂ) * logShearBase * lcftPhase h ^ n) :=
  InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy_pow_original h n

end LogCftMonodromyBridge
