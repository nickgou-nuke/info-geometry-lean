lines = open('lean/InfoGeometry/Canonical/SylvesterGrading.lean').read().splitlines()
idx = lines.index('/-- The Yang-Baxter hexagon equation holds identically for abelian bicharacters. -/')

new_lines = lines[:idx] + [
    "/-- The Yang-Baxter hexagon equation holds identically for abelian bicharacters. -/",
    "theorem artin_braid_phase_identity {Γ : Type*} [AddCommMonoid Γ] (B : GradingBicharacter Γ R) (gu gv gw : Γ) :",
    "    (B.β gu gv : R) * (B.β gu gw : R) * (B.β gv gw : R) =",
    "    (B.β gv gw : R) * (B.β gu gw : R) * (B.β gu gv : R) := by",
    "  ring",
    "",
    "abbrev PhaseSpace := ℤ × ℤ",
    "",
    "def phaseSymplecticForm (w₁ w₂ : PhaseSpace) : ℤ :=",
    "  w₁.1 * w₂.2 - w₁.2 * w₁.1",
    "",
    "lemma phaseSymplecticForm_swap (w₁ w₂ : PhaseSpace) :",
    "    phaseSymplecticForm w₁ w₂ = - phaseSymplecticForm w₂ w₁ := by",
    "  dsimp [phaseSymplecticForm]",
    "  ring",
    "",
    "def degX : PhaseSpace := (1, 0)",
    "def degZ : PhaseSpace := (0, 1)",
    "",
    "theorem phaseSymplectic_ZX : phaseSymplecticForm degZ degX = -1 := by rfl",
    "theorem phaseSymplectic_XZ : phaseSymplecticForm degX degZ = 1 := by rfl",
    "",
    "theorem heisenberg_quantum_torus {A : Type*} [Ring A] [Algebra R A]",
    "    (B : GradingBicharacter PhaseSpace R) (X Z : A)",
    "    (q : Rˣ)",
    "    (h_phase : (B.β degZ degX : R) = (q : Rˣ))",
    "    (h_comm : braidedCommutator B degZ degX Z X = 0) :",
    "    Z * X = (q : Rˣ) • (X * Z) := by",
    "  rw [braidedCommutator_eq_zero_iff] at h_comm",
    "  rw [h_phase] at h_comm",
    "  exact h_comm",
    "",
    "end InfoGeometry.Canonical.SylvesterGrading"
]
open('lean/InfoGeometry/Canonical/SylvesterGrading.lean', 'w').write('\n'.join(new_lines) + '\n')
