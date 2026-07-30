import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

namespace AtiyahTQFT

/--
Atiyah TQFT Hilbert Space Representation dim(Z(Σ)).

The finite TQFT state-space carrier is the native subtype of positive natural
dimensions.  The named accessors and constructor below preserve the owner API
without carrying a wrapper structure around the actual dimension datum.
-/
abbrev TQFTHilbertSpace := {d : ℕ // 0 < d}

abbrev TQFTHilbertSpace.hilbertDim (H : TQFTHilbertSpace) : ℕ := H.1

abbrev TQFTHilbertSpace.dim_pos (H : TQFTHilbertSpace) : 0 < H.hilbertDim := H.2

def TQFTHilbertSpace.mk (d : ℕ) (hd : 0 < d) : TQFTHilbertSpace := ⟨d, hd⟩

namespace TQFTHilbertSpace

/-- Empty Manifold Hilbert Space Z(∅) has dimension 1. -/
def emptyManifoldSpace : TQFTHilbertSpace where
  val := 1
  property := by norm_num

/-- **Theorem**: Empty Manifold TQFT Dimension is 1. -/
theorem empty_manifold_dim : emptyManifoldSpace.hilbertDim = 1 := rfl

/-- Disjoint Union Monoidal Tensor Product Z(Σ₁ ⊔ Σ₂) dimension multiplication. -/
def tensorProductSpace (H1 H2 : TQFTHilbertSpace) : TQFTHilbertSpace where
  val := H1.hilbertDim * H2.hilbertDim
  property := Nat.mul_pos H1.dim_pos H2.dim_pos

/-- **Theorem**: Atiyah TQFT Monoidal Tensor Product Multiplicativity: dim(Z(Σ₁ ⊔ Σ₂)) = dim(Z(Σ₁)) * dim(Z(Σ₂)). -/
theorem tensor_product_dim_mult (H1 H2 : TQFTHilbertSpace) :
    (tensorProductSpace H1 H2).hilbertDim = H1.hilbertDim * H2.hilbertDim := rfl

/-- Cylinder Cobordism Z(Σ × [0, 1]) trace operator equals Hilbert space dimension. -/
def cylinderCobordismTrace (H : TQFTHilbertSpace) : ℕ :=
  H.hilbertDim

/-- **Theorem**: Cylinder Trace Equals State Space Dimension. -/
theorem cylinder_trace_eq_dim (H : TQFTHilbertSpace) :
    cylinderCobordismTrace H = H.hilbertDim := rfl

end TQFTHilbertSpace

end AtiyahTQFT
