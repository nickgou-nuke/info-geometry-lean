import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Superconducting gap structures in wallpaper fermion systems

Digest source: arXiv:2509.25823v2,
Kaito Yoda and Ai Yamakage,
*Superconducting Gap Structures in Wallpaper Fermion Systems*.

The paper studies superconducting gap structures of p4g wallpaper fermions,
surface states of topological nonsymmorphic crystalline insulators.  For the six
momentum-independent pair potentials:

* `Δ₁, Δ₃, Δ₄` are fully gapped;
* `Δ₂` has point nodes;
* `Δ₅, Δ₆` have line nodes.

The 0D BdG symmetry classification gives a `Z₂` invariant precisely in class
BDI, occurring when the pair parity is odd, `χ(d)=-1`, and the crystalline
representation squares to `D(d)^2=-1`.  In the weak-coupling limit the invariant
is `ν_k[d]=N_occ(k) mod 2`; nodal structures appear at domain walls between the
two parity sectors.  Crystalline/glide-invariant-line nodes are not formalized
below.
-/

noncomputable section

namespace WallpaperFermionSuperconductingGap

open Matrix

/-! ## Pairing table -/

/-- The six momentum-independent pair potentials from the paper. -/
inductive PairPotential where
  | Δ1 | Δ2 | Δ3 | Δ4 | Δ5 | Δ6
  deriving DecidableEq, Repr

/-- Nodal outcome of a superconducting pairing. -/
inductive GapStructure where
  | fullGap | pointNode | lineNode
  deriving DecidableEq, Repr

/-- Table of nodal structures found in the paper. -/
def gapStructure : PairPotential → GapStructure
  | .Δ1 => .fullGap
  | .Δ2 => .pointNode
  | .Δ3 => .fullGap
  | .Δ4 => .fullGap
  | .Δ5 => .lineNode
  | .Δ6 => .lineNode

/-- The fully gapped pair potentials are `Δ₁, Δ₃, Δ₄`. -/
theorem full_gap_table :
    gapStructure .Δ1 = .fullGap ∧ gapStructure .Δ3 = .fullGap ∧ gapStructure .Δ4 = .fullGap := by
  simp [gapStructure]

/-- `Δ₂` has point nodes. -/
theorem point_node_table : gapStructure .Δ2 = .pointNode := by
  simp [gapStructure]

/-- `Δ₅, Δ₆` have line nodes. -/
theorem line_node_table : gapStructure .Δ5 = .lineNode ∧ gapStructure .Δ6 = .lineNode := by
  simp [gapStructure]

/-! ## 0D symmetry-class criterion -/

/-- Signs used in Table 3: pair parity `χ(d)` and crystalline square `D(d)^2`. -/
inductive Sign where
  | plus | minus
  deriving DecidableEq, Repr

open Sign

/-- Multiplication of signs. -/
def signMul : Sign → Sign → Sign
  | plus, s => s
  | minus, plus => minus
  | minus, minus => plus

/-- Negation of a sign. -/
def signNeg : Sign → Sign
  | plus => minus
  | minus => plus

/-- The square of the 0D time-reversal operator: `(Θ₀)^2=-D(d)^2`. -/
def theta0Sq (Dsq : Sign) : Sign := signNeg Dsq

/-- The square of the 0D particle-hole operator: `(Ξ₀)^2=χ(d)D(d)^2`. -/
def xi0Sq (chi Dsq : Sign) : Sign := signMul chi Dsq

/-- BDI occurs exactly when `(Θ₀)^2=+1` and `(Ξ₀)^2=+1`. -/
def isBDI (chi Dsq : Sign) : Prop := theta0Sq Dsq = plus ∧ xi0Sq chi Dsq = plus

/-- The BDI/Z₂ case is precisely `χ=-1` and `D(d)^2=-1`. -/
theorem BDI_iff_odd_pair_and_minus_square (chi Dsq : Sign) :
    isBDI chi Dsq ↔ chi = minus ∧ Dsq = minus := by
  cases chi <;> cases Dsq <;> simp [isBDI, theta0Sq, xi0Sq, signMul, signNeg]

/-- Weak-coupling 0D invariant is occupied-band parity. -/
def z2Invariant (Nocc : ℤ) : ℤ := Nocc % 2

/-- The invariant is parity-valued. -/
theorem z2Invariant_periodic (Nocc : ℤ) : z2Invariant (Nocc + 2) = z2Invariant Nocc := by
  unfold z2Invariant
  omega

/-! ## BdG/Majorana toy algebra -/

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Simple real BdG block `[[ξ,Δ],[Δ,-ξ]]`. -/
def BdG2 (ξ Δ : ℂ) : M2C := !![ξ, Δ; Δ, -ξ]

/-- Its determinant is `-(ξ²+Δ²)`. -/
theorem BdG2_det (ξ Δ : ℂ) : (BdG2 ξ Δ).det = -(ξ^2 + Δ^2) := by
  simp [BdG2, Matrix.det_fin_two]
  ring

/-- Null Majorana/BdG limit. -/
theorem BdG2_null : BdG2 0 0 = 0 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [BdG2]
    · simp [BdG2]
  · fin_cases j
    · simp [BdG2]
    · simp [BdG2]

/-- Main synthesis theorem. -/
theorem wallpaper_fermion_superconducting_gap_synthesis :
    gapStructure .Δ1 = .fullGap ∧ gapStructure .Δ3 = .fullGap ∧ gapStructure .Δ4 = .fullGap ∧
    gapStructure .Δ2 = .pointNode ∧ gapStructure .Δ5 = .lineNode ∧ gapStructure .Δ6 = .lineNode ∧
    (∀ chi Dsq : Sign, isBDI chi Dsq ↔ chi = minus ∧ Dsq = minus) ∧
    (∀ Nocc : ℤ, z2Invariant (Nocc + 2) = z2Invariant Nocc) ∧
    (∀ ξ Δ : ℂ, (BdG2 ξ Δ).det = -(ξ^2 + Δ^2)) ∧
    BdG2 0 0 = 0 := by
  have hFull := full_gap_table
  have hPoint := point_node_table
  have hLine := line_node_table
  refine And.intro ?_ ?_
  · simpa using hFull.1
  · refine And.intro ?_ ?_
    · simpa using hFull.2.1
    · refine And.intro ?_ ?_
      · simpa using hFull.2.2
      · refine And.intro ?_ ?_
        · simpa using hPoint
        · refine And.intro ?_ ?_
          · simpa using hLine.1
          · refine And.intro ?_ ?_
            · simpa using hLine.2
            · refine And.intro ?_ ?_
              · intro chi Dsq
                simpa using BDI_iff_odd_pair_and_minus_square chi Dsq
              · refine And.intro ?_ ?_
                · intro Nocc
                  simpa using z2Invariant_periodic Nocc
                · refine And.intro ?_ ?_
                  · intro ξ Δ
                    simpa using BdG2_det ξ Δ
                  · simpa using BdG2_null

end WallpaperFermionSuperconductingGap
