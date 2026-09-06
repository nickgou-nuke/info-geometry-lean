import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Signs `±1` encoded by booleans. -/
def walshSign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The mixed trace moment `m_{s,t}(T)`. -/
def mixedMoment (scanInvolution revInvolution T : ℝ) (s t : Bool) : ℝ :=
  (if s then scanInvolution else 1) * (if t then revInvolution else 1) * T

/-- The sector idempotent `e_{α,β} = (1/4) (1 + α ε_scan) (1 + β ε_rev)`. -/
noncomputable def sectorProjector
    (scanInvolution revInvolution : ℝ) (α β : Bool) : ℝ :=
  ((1 : ℝ) / 4) * (1 + walshSign α * scanInvolution) * (1 + walshSign β * revInvolution)

/-- The sector trace `τ(e_{α,β} T)`. -/
noncomputable def sectorTrace
    (scanInvolution revInvolution T : ℝ) (α β : Bool) : ℝ :=
  sectorProjector scanInvolution revInvolution α β * T

/-- Expanding the two commuting central involutions gives the four mixed moments with the
    Walsh-Hadamard coefficients.
    prop:op-algebra-z2x2-walsh-hadamard-sector-trace -/
theorem paper_op_algebra_z2x2_walsh_hadamard_sector_trace
    (scanInvolution revInvolution T : ℝ) :
    ∀ α β,
      sectorTrace scanInvolution revInvolution T α β =
        ((1 : ℝ) / 4) *
          (mixedMoment scanInvolution revInvolution T false false
            + walshSign α * mixedMoment scanInvolution revInvolution T true false
            + walshSign β * mixedMoment scanInvolution revInvolution T false true
            + walshSign α * walshSign β * mixedMoment scanInvolution revInvolution T true true) := by
  intro α β
  cases α <;> cases β <;>
    simp [sectorTrace, sectorProjector, mixedMoment, walshSign] <;>
    ring

end Omega.OperatorAlgebra
