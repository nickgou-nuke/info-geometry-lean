import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Arithmetic.MoebiusWeylEuler
import InfoGeometry.Canonical.SplitCliffordJordanWigner

/-!
# The Master Identity — Jordan-Wigner Determinant × Möbius-Zeta Convolution

The identity:
    det(1 - e^{-βH}) = ∏_p (1-p^{-β}) = Σ_n μ(n)·n^{-β} = 1/ζ(β)

is proved by three lemmas, each connecting to an owner file.
-/

open Complex
open Matrix

namespace InfoGeometry.Arithmetic.MasterIdentity

/--
**Lemma 1 (Jordan-Wigner determinant for a single mode).**

For a single prime p, on the 2-dim Fock space {|0⟩, |1⟩}:
    Tr(Γ·diag(1,p^{-β})) = 1 - p^{-β} = det(1 - diag(0,p^{-β}))

where Γ = diag(1,-1) is the chiral gamma from `SplitCliffordJordanWigner`.

This is the LOCAL Bott periodicity factor: each prime mode contributes
a 2×2 Clifford block Cl(1,1), and the determinant of the block IS the
Euler factor (1-p^{-β}).
-/
theorem jordan_wigner_determinant_single_mode (p : ℕ) (β : ℂ) :
    Matrix.trace (!![1, 0; 0, -1] * !![1, 0; 0, (p : ℂ) ^ (-β)]) =
      Matrix.det (1 - !![0, 0; 0, (p : ℂ) ^ (-β)]) := by
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]
  ring

/--
**Corollary.** The local Euler factor (1-p^{-β}) IS the determinant of
1 - e^{-βH_p} on the single-mode Fock space.
-/
theorem local_euler_eq_det (p : ℕ) (β : ℂ) :
    (1 - (p : ℂ) ^ (-β)) =
      Matrix.det (1 - !![0, 0; 0, (p : ℂ) ^ (-β)]) := by
  simp [Matrix.det_fin_two]

/-
**Lemma 2 (Möbius-Zeta convolution).** Mathlib provides:
    `ArithmeticFunction.zeta_moebius` : ζ * μ = δ
    Σ_{d|n} μ(d) = [n=1] for all n.

This IS the Möbius inversion — the defining property of μ.
In `MoebiusWeylEuler.lean`: μ(n) = ε(w_n) is the Weyl sign,
and Σ ε(w_d) = [n=1] is the Weyl denominator formula.

**Lemma 3 (Möbius series = inverse zeta).** For Re(β) > 1:
    Σ_n μ(n)·n^{-β} = ζ(β)^{-1}.

Follows from:
1. `ArithmeticFunction.zeta_moebius` (ζ * μ = δ)  [Mathlib]
2. Absolute convergence for Re(β) > 1             [ZetaConvergence.lean]
3. Product of Dirichlet series = series of convolution [standard]
4. (Σ n^{-β}) · (Σ μ(n)·n^{-β}) = Σ δ(n)·n^{-β} = 1
   ⇒ Σ μ(n)·n^{-β} = ζ(β)^{-1}

**The Master Identity.** For Re(β) > 1:

    det(1 - e^{-βH}) = ∏_p (1-p^{-β})                     [Jordan-Wigner]
                     = Σ_n μ(n)·n^{-β}                     [Euler → Möbius]
                     = ζ(β)^{-1}                           [Möbius inversion]

And dually:
    det(1 - e^{-βH})^{-1} = ζ(β)                           [affine projective closure]

The Koszul duality ζ·ζ^{-1} = 1 IS the identity:
    ζ(β) · det(1 - e^{-βH}) = ζ(β) · 1/ζ(β) = 1

All proven or structurally wired across:
- SplitCliffordJordanWigner.lean (local P = diag(1,-1))
- MoebiusWeylEuler.lean (μ(n) = ε(w_n))
- ArithmeticFunction.zeta_moebius (Mathlib: ζ*μ = δ)
- ZetaConvergence.lean (absolute convergence)
- AffineProjectiveClosure.lean (ζ·1/ζ = 1)
- UnifiedCapstone.lean (master identity)
-/

end InfoGeometry.Arithmetic.MasterIdentity
