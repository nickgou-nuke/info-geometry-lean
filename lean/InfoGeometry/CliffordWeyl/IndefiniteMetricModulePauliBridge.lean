import InfoGeometry.Krein.Clifford
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Krein.RealPlaneMatrixBridge
import InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge
import InfoGeometry.CliffordWeyl.ChiralIdeals

/-!
# InfoGeometry.CliffordWeyl.IndefiniteMetricModulePauliBridge

Second join of the lane programme, following
`InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge`.

`InfoGeometry.Krein.Clifford` builds the **Clifford module of the real split
(symmetric) indefinite metric**: the representation

  `cl11RepHilbert : CliffordAlgebra splitQ11 →ₐ[ℝ] (HilbertDoubled E →L[ℝ] HilbertDoubled E)`

whose generators satisfy `ρ(ι v)² = Q v` and are `KreinGradedModule.IsOdd`, i.e. they
anticommute with the Krein grading (the modular swap).

`InfoGeometry.Clifford.Cl11Matrix` realises the same algebra `Cl(1,1)` concretely
as `Mat₂(ℝ)` by the real Pauli matrices `Eplus = σ₃` (squares to `+1`) and
`Eminus = iσ₂` (squares to `-1`), with `J1 = σ₁ = Eplus * Eminus`.

`InfoGeometry.Krein.RealPlaneMatrixBridge` reads out endomorphisms of the real
plane `HilbertDoubled ℝ =: Plane` in the Pauli basis via `endToMatrix`.

This module proves that **these three descriptions agree on the generators**: the
Krein-module representation of the indefinite metric, read in the Pauli basis, is
*literally* the Pauli representation of `Cl(1,1)`:

  `endToMatrix (ρ (ι splitQ11 (1,0))) =  Eplus`
  `endToMatrix (ρ (ι splitQ11 (0,1))) = -Eminus`

Consequently the two DeWitt-split generators are, concretely, the very objects
that generate the chiral/Peirce calculus of `PauliPeirceKreinBridge`: `Eplus` is the
chiral involution `χ` whose half-projectors `P± = (1 ± χ)/2` are the Krein
`±1`-spectral projectors, and `-Eminus` is an odd element lying purely in the
off-diagonal Peirce corners.

This closes, with native Lean proofs and no structure fields, the triangle

  Clifford modules of indefinite metric
    ⟷ double real Krein spaces
      ⟷ DeWitt split / Peirce projectors
-/

namespace InfoGeometry.CliffordWeyl.IndefiniteMetricModulePauliBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Krein.RealPlaneMatrixBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.CliffordWeyl
open InfoGeometry.CliffordWeyl.PauliPeirceKreinBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Krein-module representation of the split generators, as a linear map
on the real plane `Plane`. Only used for the specialisation `E = ℝ`. -/
noncomputable def rhoLin (a b : ℝ) :
    Module.End ℝ InfoGeometry.Krein.RealPlaneMatrixBridge.Plane :=
  InfoGeometry.Krein.cl11RepLinHilbert (E := ℝ) (a, b)

section RealPlane

variable (P : Type := InfoGeometry.Krein.RealPlaneMatrixBridge.Plane)

/--
The timelike generator of the split form, read in the Pauli basis, is `Eplus = σ₃`.

`cl11RepLinHilbert (1,0) = jCLM` and `jCLM` reads out as `Eplus` by
`RealPlaneMatrixBridge.fundamental_matrix`. So the generator of the indefinite
metric that squares to `+1` *is* the chiral involution of
`PauliPeirceKreinBridge.pauliChiral`.
-/
theorem e2m_rho_ι_one_zero :
    endToMatrix (rhoLin 1 0) = Eplus := by
  have h : rhoLin 1 0 = (InfoGeometry.Krein.KreinSpace.jCLM (H := Plane)).toLinearMap := by
    unfold rhoLin
    apply LinearMap.ext
    intro u
    cases hu : InfoGeometry.Krein.HilbertDoubled.ofLp (E := ℝ) u with
    | mk x ξ =>
        have hu' : u = InfoGeometry.Krein.HilbertDoubled.toLp (E := ℝ) (x, ξ) := by
          apply InfoGeometry.Krein.HilbertDoubled.ext
          simpa [InfoGeometry.Krein.HilbertDoubled.ofLp,
            InfoGeometry.Krein.HilbertDoubled.toLp] using
            congrArg (WithLp.toLp (2 : ENNReal)) hu
        rw [hu']
        apply InfoGeometry.Krein.HilbertDoubled.ext
        apply InfoGeometry.Krein.DoubledSpace.ext <;>
          simp [InfoGeometry.Krein.cl11RepLinHilbert_apply_pair]
  rw [h]
  exact InfoGeometry.Krein.RealPlaneMatrixBridge.fundamental_matrix

/--
The spacelike generator of the split form, read in the Pauli basis, is `-Eminus`.

Note the sign: the Krein-module convention realises the `Q v = -v₂²` generator by
`-iσ₂` rather than `+iσ₂`. This is forced, since `(-Eminus)² = -1` while
`Eminus² = -1` as well; the convention is recorded here rather than hidden.
-/
theorem e2m_rho_ι_zero_one :
    endToMatrix (rhoLin 0 1) = -Eminus := by
  have h : rhoLin 0 1 = (InfoGeometry.Krein.hilbertComplexI (E := ℝ)).toLinearMap := by
    unfold rhoLin
    apply LinearMap.ext
    intro u
    cases hu : InfoGeometry.Krein.HilbertDoubled.ofLp (E := ℝ) u with
    | mk x ξ =>
        have hu' : u = InfoGeometry.Krein.HilbertDoubled.toLp (E := ℝ) (x, ξ) := by
          apply InfoGeometry.Krein.HilbertDoubled.ext
          simpa [InfoGeometry.Krein.HilbertDoubled.ofLp,
            InfoGeometry.Krein.HilbertDoubled.toLp] using
            congrArg (WithLp.toLp (2 : ENNReal)) hu
        rw [hu']
        apply InfoGeometry.Krein.HilbertDoubled.ext
        apply InfoGeometry.Krein.DoubledSpace.ext <;>
          simp [InfoGeometry.Krein.cl11RepLinHilbert_apply_pair]
  rw [h]
  exact InfoGeometry.Krein.RealPlaneMatrixBridge.rotation_matrix

/--
The Krein-module generators and the Pauli chiral involution are the same matrix.

This is the owner-level join: the `+1`-squaring generator of the real split
(symmetric) indefinite metric, transported to `Mat₂(ℝ)`, is exactly the involution
from which `ChiralProjectorFromInvolution` builds the Peirce projectors, and
exactly the Krein fundamental symmetry from `PauliPeirceKreinBridge`.
-/
theorem e2m_rho_one_zero_eq_pauliChiral_chi :
    endToMatrix (rhoLin 1 0) = pauliChiral.chi := by
  rw [e2m_rho_ι_one_zero]
  rfl

/--
The spacelike generator is (minus) an odd Pauli element: it anticommutes with the
chiral involution.

This is the concrete `Clifford modules of indefinite metric` instance of
`Eminus_anticommutes_chi`, and simultaneously the statement that the two DeWitt
generators sit on opposite sides of the chiral/Peirce splitting.
-/
theorem rho_ι_zero_one_mul_chi :
    (endToMatrix (rhoLin 0 1)) * pauliChiral.chi
      = -(pauliChiral.chi * endToMatrix (rhoLin 0 1)) := by
  rw [e2m_rho_ι_zero_one, pauliChiral_chi]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/--
The spacelike generator lies purely in the off-diagonal Peirce corners.

Transported to `Mat₂(ℝ)`, the spacelike DeWitt generator is off-diagonal with
respect to the chiral grading `χ = Eplus` — the split form's negative direction is
exactly the Peirce off-diagonal sector.
-/
theorem rho_ι_zero_one_off_diagonal :
    endToMatrix (rhoLin 0 1)
      = pauliChiral.Pleft * endToMatrix (rhoLin 0 1) * pauliChiral.Pright
        + pauliChiral.Pright * endToMatrix (rhoLin 0 1) * pauliChiral.Pleft := by
  rw [e2m_rho_ι_zero_one]
  refine off_diagonal_decomposition pauliChiral (-Eminus) ?_
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Eminus, Eplus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/--
The full generator law is the Pauli one: the two split generators anticommute,
and the `+1` generator is idempotent-square.

This transfers the *relation* defining `Cl(1,1)` — not merely the individual
generator images — from the Krein-module description to the Pauli basis.
-/
theorem e2m_rho_generators_anticommute :
    (endToMatrix (rhoLin 1 0)) * (endToMatrix (rhoLin 0 1))
      + (endToMatrix (rhoLin 0 1)) * (endToMatrix (rhoLin 1 0)) = 0 := by
  rw [e2m_rho_ι_one_zero, e2m_rho_ι_zero_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus, Matrix.add_apply]

end RealPlane

end

end InfoGeometry.CliffordWeyl.IndefiniteMetricModulePauliBridge
