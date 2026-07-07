  rfl

/-- The logarithmic phase for one positive monodromy wrap. -/
def lcftPhase (h : ℂ) : ℂ :=
  Complex.exp (-(2 : ℂ) * Complex.I * (Real.pi : ℂ) * h)

/-- The universal logarithmic shear coefficient before multiplying by the phase. -/
def logShearBase : ℂ :=
  -(2 : ℂ) * Complex.I * (Real.pi : ℂ)

/-- The actual one-wrap shear coefficient. -/
def logShear (h : ℂ) : ℂ :=
  logShearBase * lcftPhase h

/--
Hadjiivanov logarithmic monodromy for one wrap around a singularity:
`phase` on the diagonal and logarithmic shear in the upper-right entry.
-/
def hadjiivanovMonodromy (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  upperJordan (lcftPhase h) (logShear h)

/-- The nilpotent part of the one-wrap monodromy. -/
def monodromyNilpotentPart (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, logShear h; 0, 0]

/-- The monodromy splits into a scalar phase and a nilpotent logarithmic shear. -/
theorem monodromy_decomposition (h : ℂ) :
    hadjiivanovMonodromy h =
      lcftPhase h • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        monodromyNilpotentPart h := by
  ext i j