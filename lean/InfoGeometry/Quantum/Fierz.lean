import InfoGeometry.Quantum.Fock
import InfoGeometry.Krein.HilbertBridge
import InfoGeometry.Krein.DoubledSpace

/-!
# Fierz Identities for Information Geometry

This module formalizes the Fierz identities for the doubled Krein space $E \oplus E$,
interpreted as identities between different informational channels:
1. **Scalar Channel**: Hessian/Krein pairing (Information Density).
2. **Symplectic Channel**: Induced symplectic form (Information Phase).
3. **Hilbert Channel**: Euclidean pairing (Total Information Power).

Fierz identities provide the "conservation of information power" across these channels.
-/

namespace InfoGeometry.Quantum.Fierz

open InfoGeometry.Krein
open InfoGeometry.Quantum

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Information Scalar Channel**: $S(\psi) = \langle \psi, J \psi \rangle = 2 \langle x, \xi \rangle$. -/
noncomputable def infoScalar (ψ : Krein.DoubledSpace E) : ℝ :=
  hessianIndefiniteForm (E := E) ψ ψ

/-- **Information Symplectic Channel**: $\omega(\psi) = \langle \psi, \epsilon \psi \rangle = \|x\|^2 - \|\xi\|^2$. -/
noncomputable def infoSymplectic (ψ : Krein.DoubledSpace E) : ℝ :=
  inducedSymplecticForm (E := E) ψ ψ

/-- **Information Hilbert Channel**: $H(\psi) = \langle \psi, \psi \rangle = \|x\|^2 + \|\xi\|^2$. -/
noncomputable def infoHilbert (ψ : Krein.DoubledSpace E) : ℝ :=
  inner ℝ ψ.1 ψ.1 + inner ℝ ψ.2 ψ.2

/-- **Information Area (Uncertainty)**: The squared area spanned by the data and model components.
Identified with the Gram determinant of the state components. -/
noncomputable def infoArea (ψ : Krein.DoubledSpace E) : ℝ :=
  inner ℝ ψ.1 ψ.1 * inner ℝ ψ.2 ψ.2 - (inner ℝ ψ.1 ψ.2)^2

/-! ### The Informational Fierz Identity -/

/-- 
**The Information Power Conservation Theorem**:
The total Hilbert power of a belief state is distributed across the
scalar and symplectic channels, with the remainder being the information uncertainty (Area).

$H(\psi)^2 = S(\psi)^2 + \omega(\psi)^2 + 4 \cdot \text{Area}(\psi)$
-/
theorem information_fierz_identity [CompleteSpace E] (ψ : Krein.DoubledSpace E) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 + 4 * (infoArea ψ) := by
  rcases ψ with ⟨x, ξ⟩
  unfold infoHilbert infoScalar infoSymplectic infoArea
  simp [inducedSymplecticForm_eq_complex_pairing, InfoGeometry.Krein.hessianIndefiniteForm,
    InfoGeometry.hessianIndefiniteForm, hessianIndefiniteForm,
    _root_.complexI,
    sub_eq_add_neg]
  ring

/--
**Majorana Information Condition**:
A belief state is 'Majorana' if its data and model components are perfectly aligned
(zero uncertainty/area). For such states, the conservation identity simplifies to a sum of squares.
-/
def IsMajoranaBelief (ψ : Krein.DoubledSpace E) : Prop :=
  infoArea ψ = 0

theorem information_fierz_majorana [CompleteSpace E] (ψ : Krein.DoubledSpace E) (hM : IsMajoranaBelief ψ) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 := by
  rw [information_fierz_identity (E := E) ψ, hM]
  ring

end InfoGeometry.Quantum.Fierz
