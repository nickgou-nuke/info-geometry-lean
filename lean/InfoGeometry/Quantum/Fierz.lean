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

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Information Scalar Channel**: $S(\psi) = \langle \psi, J \psi \rangle = 2 \langle x, \xi \rangle$. -/
noncomputable def infoScalar (ψ : Krein.DoubledSpace E) : ℝ :=
  hessianIndefiniteForm (E := E) ψ ψ

/-- **Information Symplectic Channel**: $\omega(\psi) = \langle \psi, \epsilon \psi \rangle = \|x\|^2 - \|\xi\|^2$. -/
noncomputable def infoSymplectic (ψ : Krein.DoubledSpace E) : ℝ :=
  inducedSymplecticForm (E := E) ψ ψ

/-- **Information Hilbert Channel**: $H(\psi) = \langle \psi, \psi \rangle = \|x\|^2 + \|\xi\|^2$. -/
noncomputable def infoHilbert (ψ : Krein.DoubledSpace E) : ℝ :=
  inner ℝ (DoubledSpace.fst ψ) (DoubledSpace.fst ψ) + inner ℝ (DoubledSpace.snd ψ) (DoubledSpace.snd ψ)

/-- **Information Area (Uncertainty)**: The squared area spanned by the data and model components.
Identified with the Gram determinant of the state components. -/
noncomputable def infoArea (ψ : Krein.DoubledSpace E) : ℝ :=
  inner ℝ (DoubledSpace.fst ψ) (DoubledSpace.fst ψ) * inner ℝ (DoubledSpace.snd ψ) (DoubledSpace.snd ψ) -
    (inner ℝ (DoubledSpace.fst ψ) (DoubledSpace.snd ψ))^2

/-! ### The Informational Fierz Identity -/

/--
**The Information Power Conservation Theorem**:
The total Hilbert power of a belief state is distributed across the
scalar and symplectic channels, with the remainder being the information uncertainty (Area).

$H(\psi)^2 = S(\psi)^2 + \omega(\psi)^2 + 4 \cdot \text{Area}(\psi)$
-/
theorem information_fierz_identity (ψ : Krein.DoubledSpace E) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 + 4 * (infoArea ψ) := by
  obtain ⟨⟨x, ξ⟩⟩ := ψ
  simp only [infoHilbert, infoScalar, infoSymplectic, infoArea, DoubledSpace.fst, DoubledSpace.snd, WithLp.ofLp]
  sorry

/--
**Majorana Information Condition**:
A belief state is 'Majorana' if its data and model components are perfectly aligned
(zero uncertainty/area). For such states, the conservation identity simplifies to a sum of squares.
-/
def IsMajoranaBelief (ψ : Krein.DoubledSpace E) : Prop :=
  infoArea ψ = 0

theorem information_fierz_majorana (ψ : Krein.DoubledSpace E) (hM : IsMajoranaBelief ψ) :
    (infoHilbert ψ)^2 = (infoScalar ψ)^2 + (infoSymplectic ψ)^2 := by
  rw [information_fierz_identity (E := E) ψ, hM]
  ring

end InfoGeometry.Quantum.Fierz
