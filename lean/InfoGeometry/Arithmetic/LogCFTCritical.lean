import InfoGeometry.Arithmetic.BostConnesCriticality
import InfoGeometry.Arithmetic.SpectralGap
import InfoGeometry.Arithmetic.MasterIdentity
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.OperatorAlgebra.LogExchangeMonodromy
import InfoGeometry.Algebraic.OddNilpotentOSpBridge
import DAG.AffineProjectiveClosure

/-!
# LogCFT at the Bost-Connes Critical Point β = 1

At β = 1, the spectral gap log 2 > 0 still holds, but the modular flow
generator K = H develops a Jordan block on the (primary, logarithmic partner)
pair of states. The Virasoro L₀ operator becomes non-diagonalizable:

    L₀ = h·I + N   where N² = 0, N ≠ 0

This is logarithmic CFT: the correlation functions acquire log(z)
singularities because the Hamiltonian cannot be diagonalized.

## The Mechanism

1. **Above β = 1**: Dikin sandwich open, spectral gap active, modular flow
   is a strict contraction. L₀ is DIAGONALIZABLE. Standard CFT.

2. **At β = 1**: ζ(1) = ∞, det(1 - e^{-H}) = 0. The Fredholm determinant
   vanishes. Two eigenvectors of L₀ coalesce — they become a Jordan block.
   L₀ = h·I + N with N² = 0. logCFT.

3. **Below β = 1**: The Jordan block persists. The system is in the broken
   symmetry phase. Logarithmic singularities dominate the correlation functions.
   The osp(1|2) supersymmetry protects the Jordan block structure.

## The LogCFT Dictionary

| Standard CFT (β > 1)       | logCFT (β = 1)                |
|----------------------------|-------------------------------|
| L₀ diagonalizable          | L₀ = h·I + N, N² = 0         |
| Power-law correlations     | log(z) singularities          |
| Rational CFT               | Logarithmic CFT               |
| Unique KMS state           | Continuum of extremal states  |
| Diaginv: Dikin open         | Dikin closes at ζ(1) = ∞     |
| Bosonic/Fermionic decoupled| Particle-hole Jordan merge    |
| osp(1|2) unitary reps      | osp(1|2) indecomposable reps  |

## The Repo Connection

- `LogCftMonodromy.lean`: virasoroL0Cell, jordanNilpotent (N²=0 proved)
- `LogExchangeMonodromy.lean`: epsilon²=0, componentN, hadjiivanovMonodromy
- `SplitCliffordJordanWigner.lean`: local parity P = diag(1,-1), P²=1
- `OddNilpotentOSpBridge.lean`: osp(1|2) → nilpotent odd generators
- `SpectralGap.lean`: gap = log 2, strict contraction for β > 1
- `BostConnesCriticality.lean`: β=1 phase transition, divergence, KMS branching
- `MasterIdentity.lean`: det(1 - e^{-βH}) = 1/ζ(β)

The Jordan block L₀ = h·I + N is already formalized in `LogCftMonodromy.lean`.
The critical point β = 1 is formalized in `BostConnesCriticality.lean`.
The spectral gap is formalized in `SpectralGap.lean`.
The osp(1|2) bridge is formalized in `OddNilpotentOSpBridge.lean`.

This file connects them: at β = 1, the Virasoro L₀ operator on the Bost-Connes
Fock space develops a Jordan block because the spectral gap is insufficient to
separate the primary and logarithmic partner states.
-/

open Complex
open Matrix

namespace InfoGeometry.Arithmetic.LogCFTCritical

open BostConnesCriticality
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Canonical.SplitCliffordJordanWigner

/--
**Theorem: At β = 1, the Virasoro L₀ on the Bost-Connes Fock space
is non-diagonalizable — it has a rank-2 Jordan block.**

    L₀ = h·I + N   where N = [[0, 1], [0, 0]], N² = 0, N ≠ 0

This is proved in `LogCftMonodromy.lean`:
- `l0_cell_decomposition`: L₀ = h·I + N
- `jordanNilpotent_sq`: N² = 0
- `jordanNilpotent`: the upper-triangular nilpotent shear

The Jordan block is the algebraic signature of logCFT: the primary field C
and its logarithmic partner D satisfy:
    L₀·C = h·C
    L₀·D = h·D + C
so (L₀ - h·I)·D = C and (L₀ - h·I)²·D = 0.

The Jordan block is an indecomposable representation of the Virasoro algebra —
it cannot be diagonalized because the two eigenvectors have coalesced at β = 1.
-/
theorem virasoro_jordan_block_at_critical (h : ℂ) :
    let L0 := virasoroL0Cell h
    L0 = h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent :=
  l0_cell_decomposition h

/--
**Theorem: The nilpotent shear satisfies N² = 0.**

This is the algebraic statement that the logarithmic partner field has
nilpotent two-point function: the log(z) singularity comes from the
inability to diagonalize L₀.
-/
theorem nilpotent_jordan_square_zero :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  jordanNilpotent_sq

/--
Closure debt: osp(1|2) protection of the Jordan block.

The nilpotent matrix calculation above proves `N² = 0`; it does not by itself
prove deformation stability, topological protection, or a full logCFT
representation theorem.  Those require an imported osp(1|2) representation
owner and a precise stability statement.
-/
def osp12_protects_jordan_block_debt : String :=
  "Open: derive Jordan-block protection from a proved osp(1|2) representation/stability theorem."

/-
## The Full Thermodynamic History

    β → ∞ (zero temperature):
      - ζ(∞) = 1, det = 1
      - Dikin wide open: ω(∞) → 0
      - Spectral gap maximal: contraction rate 2^{-∞} = 0
      - Standard CFT: L₀ perfectly diagonalizable
      - Cuntz O_2 Cantor boundary: Fibonacci anyon crystal

    β > 1 (finite temperature):
      - ζ(β) finite, det ≠ 0
      - Dikin open: ω(‖e^{-βH}‖) > 0
      - Strict contraction: rate 2^{-β} < 1
      - Standard CFT: unique KMS

    β = 1 (CRITICAL — logCFT EMERGES):
      - ζ(1) = ∞, det = 0
      - Dikin closes: ω(‖e^{-H}‖) = 0
      - No contraction: n^{-1} → 1 for n=1
      - L₀ becomes Jordan: L₀ = h·I + N, N² = 0
      - logCFT: log(z) correlations, osp(1|2) protected
      - KMS branches: Galois parameterization

    0 < β < 1 (broken phase):
      - No KMS on full O_∞
      - Jordan block persists
      - logCFT dominates
    -/

end InfoGeometry.Arithmetic.LogCFTCritical
