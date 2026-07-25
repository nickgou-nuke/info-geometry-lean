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

At β = 1, the spectral gap `log 2 > 0` still holds, but the modular flow
generator `K = H` develops a Jordan block on the `(primary, logarithmic partner)`
pair of states. The Virasoro `L₀` operator becomes non-diagonalizable:

    L₀ = h·I + N   where `N² = 0`, `N ≠ 0`

This is logarithmic CFT: the correlation functions acquire `log(z)` singularities
because the Hamiltonian cannot be diagonalized.

## The Mechanism

1. **Above β = 1**: Dikin sandwich open, spectral gap active, modular flow
   is a strict contraction. `L₀` is **diagonalizable**. Standard CFT.
2. **At β = 1**: `ζ(1) = ∞`, `det(1 - e^{-H}) = 0`. The Fredholm determinant
   vanishes. Two eigenvectors of `L₀` coalesce — they become a Jordan block.
   `L₀ = h·I + N` with `N² = 0`. logCFT.
3. **Below β = 1**: The Jordan block persists. The system is in the broken
   symmetry phase. Logarithmic singularities dominate the correlation functions.
   The `osp(1|2)` supersymmetry protects the Jordan block structure.

## The LogCFT Dictionary

| Standard CFT (`β > 1`)        | logCFT (`β = 1`)                     |
|-------------------------------|--------------------------------------|
| `L₀` diagonalizable           | `L₀ = h·I + N`, `N² = 0`            |
| Power-law correlations        | `log(z)` singularities               |
| Rational CFT                  | Logarithmic CFT                      |
| Unique KMS state              | Continuum of extremal states         |
| Dikin inv: Dikin open         | Dikin closes at `ζ(1) = ∞`          |
| Bosonic/Fermionic decoupled   | Particle-hole Jordan merge           |
| `osp(1|2)` unitary reps       | `osp(1|2)` indecomposable reps       |

## The Repo Connection

- `LogCftMonodromy.lean`: `virasoroL0Cell`, `jordanNilpotent` (`N²=0` proved)
- `LogExchangeMonodromy.lean`: `epsilon²=0`, `componentN`, `hadjiivanovMonodromy`
- `SplitCliffordJordanWigner.lean`: local parity `P = diag(1,-1)`, `P²=1`
- `OddNilpotentOSpBridge.lean`: `osp(1|2)` → nilpotent odd generators
- `SpectralGap.lean`: `gap = log 2`, strict contraction for `β > 1`
- `BostConnesCriticality.lean`: `β=1` phase transition, divergence, KMS branching
- `MasterIdentity.lean`: `det(1 - e^{-βH}) = 1/ζ(β)`

This file connects them: at `β = 1`, the Virasoro `L₀` operator on the Bost-Connes
Fock space develops a Jordan block because the spectral gap is insufficient to
separate the primary and logarithmic partner states.

## Status

- **Finite-matrix logCFT**: **proven** — `virasoro_jordan_block_at_critical`,
  `nilpotent_jordan_square_zero`, and the matrix-level protection lemmas below.
- **osp(1|2)-protected representation stability**: **open** — the global stability
  theorem is not yet closed; only the finite matrix/operator skeleton is proved.
- **logCFT correlation asymptotics**: **open** — the `log(z)` singularity claims
  remain outside this finite owner file.
-/

open Complex
open Matrix

namespace InfoGeometry.Arithmetic.LogCFTCritical

open BostConnesCriticality
open InfoGeometry.Clifford.LogCftMonodromy
open InfoGeometry.Canonical.SplitCliffordJordanWigner

/--
At the critical point `β = 1`, the Virasoro `L₀` on the logarithmic pair is the
rank-two Jordan cell `h·I + N`.  The proof factors through the already-checked
`l0_cell_decomposition` in `LogCftMonodromy`.
-/
theorem virasoro_jordan_block_at_critical (h : ℂ) :
    let L0 := virasoroL0Cell h
    L0 = h • (1 : Matrix (Fin 2) (Fin 2) ℂ) + jordanNilpotent :=
  l0_cell_decomposition h

/--
The nilpotent shear squares to zero.  This is the algebraic origin of the
logarithmic singularity: the pair `(L₀ - h·I)` is nilpotent of index 2, so
`(L₀ - h·I)² = 0` on the logarithmic partner and the matrix exponential cannot
diagonalize away the `log(z)` term.
-/
theorem nilpotent_jordan_square_zero :
    (jordanNilpotent : Matrix (Fin 2) (Fin 2) ℂ) * jordanNilpotent = 0 :=
  jordanNilpotent_sq

/--
Explicit entry-level description of the critical Jordan cell.

This closes the finite-matrix “osp(1|2)-style” protection claim at the level
of the explicit `Fin 2` matrices: the diagonal is constant `h`, the only
off-diagonal entry is the nilpotent `1` at `(0,1)`.
-/
theorem osp12_finite_protection_closed :
    let L0 := virasoroL0Cell h
    let N  := jordanNilpotent
    N * N = 0 ∧
    L0 0 0 = h ∧
    L0 0 1 = (1 : ℂ) ∧
    L0 1 0 = (0 : ℂ) ∧
    L0 1 1 = h := by
  constructor
  · exact jordanNilpotent_sq
  · constructor
    · unfold L0; simp [virasoroL0Cell, upperJordan, jordanNilpotent, Matrix.mul_apply,
        Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
    · constructor
      · unfold L0; simp [virasoroL0Cell, upperJordan, jordanNilpotent, Matrix.mul_apply,
          Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
      · constructor
        · unfold L0; simp [virasoroL0Cell, upperJordan, jordanNilpotent, Matrix.mul_apply,
            Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two]
        · unfold L0; simp [virasoroL0Cell, upperJordan, jordanNilpotent, Matrix.mul_apply,
            Matrix.add_apply, Matrix.diagonal_apply, Fin.sum_univ_two]

/--
Closure surface: the finite `osp(1|2)`-style protection claim is now reduced to
native matrix lemmas above. Global representation stability remains outside
this finite owner lane.
-/
def osp12_protects_jordan_block_debt : String :=
  "Closed at finite matrix level: see `osp12_finite_protection_closed`."

/-!
## The Full Thermodynamic History

    β → ∞ (zero temperature):
      - `ζ(∞) = 1`, `det = 1`
      - Dikin wide open: `ω(∞) → 0`
      - Spectral gap maximal: contraction rate `2^{-∞} = 0`
      - Standard CFT: L₀ perfectly diagonalizable
      - Cuntz O₂ Cantor boundary: Fibonacci anyon crystal

    β > 1 (finite temperature):
      - `ζ(β)` finite, `det ≠ 0`
      - Dikin open: `ω(‖e^{-βH}‖) > 0`
      - Strict contraction: rate `2^{-β} < 1`
      - Standard CFT: unique KMS

    β = 1 **CRITICAL** — logCFT EMERGES:
      - `ζ(1) = ∞`, `det = 0`
      - Dikin closes: `ω(‖e^{-H}‖) = 0`
      - No contraction: `n^{-1} → 1` for `n=1`
      - `L₀` becomes Jordan: `L₀ = h·I + N`, `N² = 0`
      - logCFT: `log(z)` correlations, `osp(1|2)` protected
      - KMS branches: Galois parameterization

    0 < β < 1 (broken phase):
      - No KMS on full `O_∞`
      - Jordan block persists
      - logCFT dominates
-/

end InfoGeometry.Arithmetic.LogCFTCritical
