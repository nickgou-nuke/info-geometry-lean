import Mathlib

/-!
QMS isolated proof target for replacing the impossible
`SouriauKLBregmanWitness` support socket in
`InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `MomentMapGeneratingPotential` carries a scalar partition potential `Φ(β)`
  and first variation `dΦ`.
- `SouriauKLBregmanWitness` carries:
  - `alphaPartitionPotential`, read as `Φ(α)`;
  - `generator.souriau.partitionPotential`, read as `Φ(β)`;
  - `generator.dPhi alphaMinusBeta`, read as the linear first-variation term.
- The Bregman/KL support expression is the finite algebraic value
  `Φ(α) - Φ(β) - dΦ(α-β)`.

Existing mathlib/literature context:
- Mathlib provides ring/order syntax over `ℝ`; no convexity or measure theory is
  used in this local readback.
- In Souriau/Bregman thermodynamics, identifying KL with a Bregman divergence
  requires support/regularity hypotheses. This abstract owner surface does not
  prove those analytic hypotheses. It only defines the algebraic Bregman value.

QMS purification move:
- Replace the impossible `False` theorem surface by a positive readback of the
  explicitly defined Bregman/KL value.
- Do not claim convexity, support, absolute continuity, or KL nonnegativity.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialBregmanSupport

structure SouriauData where
  partitionPotential : ℝ

structure MomentMapGeneratingPotential where
  souriau : SouriauData
  dPhi : Unit → ℝ

structure SouriauKLBregmanWitness where
  generator : MomentMapGeneratingPotential
  alphaPartitionPotential : ℝ
  alphaMinusBeta : Unit

namespace SouriauKLBregmanWitness

/-- Algebraic Souriau/KL-as-Bregman readout. -/
def klValue (B : SouriauKLBregmanWitness) : ℝ :=
  B.alphaPartitionPotential - B.generator.souriau.partitionPotential -
    B.generator.dPhi B.alphaMinusBeta

/-- The support socket reduces to the explicit algebraic Bregman readout. -/
theorem supportHypotheses_as_bregman_readout
    (B : SouriauKLBregmanWitness) :
    B.klValue =
      B.alphaPartitionPotential - B.generator.souriau.partitionPotential -
        B.generator.dPhi B.alphaMinusBeta := by
  rfl

end SouriauKLBregmanWitness

end InfoGeometry.QMS.SouriauOperatorialLogPotentialBregmanSupport
