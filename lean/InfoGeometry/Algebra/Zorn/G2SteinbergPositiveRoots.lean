import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup
import Mathlib.Tactic

/-!
# Steinberg Positive Root Automorphisms of G₂(2)

This module constructs the explicit unipotent root automorphisms $u_{\alpha} \in \operatorname{SplitOctF2Aut}$
for positive roots of $G_2$ over $\mathbb{F}_2$ and proves the native Steinberg commutator relation:

$$[u_S, u_L] = u_S u_L u_S u_L = u_{\alpha_1 + \alpha_2}$$

All proofs are native Mathlib kernel-checked theorems with 0 `sorry`s.
-/

namespace InfoGeometry.Algebra.Zorn.G2SteinbergRoots

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- Simple short root unipotent automorphism $x_{\alpha_1}(1)$. -/
def uShort : SplitOctF2Aut := unipotentShortAut true

/-- Simple long root unipotent automorphism $x_{\alpha_2}(1)$. -/
def uLong : SplitOctF2Aut := unipotentLongAut true

/-- Unipotent action function for composite short root $\alpha_1 + \alpha_2$:
    shifts $x_0 \leftarrow x_0 + x_2$ and $y_2 \leftarrow y_2 + y_0$. -/
def uMidFun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, add2 X.x0 X.x2, X.x1, X.x2, X.y0, X.y1, add2 X.y2 X.y0⟩

def uMidEquiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := uMidFun
  invFun := uMidFun
  left_inv X := by rcases X; ext <;> simp [uMidFun, add2]
  right_inv X := by rcases X; ext <;> simp [uMidFun, add2]

/-- Proof that `uMidEquiv` preserves the split-octonion unit, addition, and multiplication. -/
theorem isSplitOctF2Aut_uMid : IsSplitOctF2Aut uMidEquiv := by
  refine ⟨rfl, ?_, ?_⟩
  · intro X Y
    rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, add]
      exact xor_swap x01 x02 x21 x22
    · rfl
    · rfl
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, add]
      exact xor_swap y21 y22 y01 y02
  · intro X Y
    rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, dot3]
      revert a1 a2 x01 x11 x21 y02 y12 y22 y01 y11 y21 x02 x12 x22
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, dot3]
      revert b1 b2 y01 y11 y21 x02 x12 x22 x01 x11 x21 y02 y12 y22
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross0, cross2]
      revert a1 a2 b1 b2 x01 x02 x21 x22 y11 y21 y12 y22 y01 y02
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross1]
      revert a1 b2 x11 x12 y01 y21 y02 y22 y01 y02
      decide
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross1]
      revert b1 a2 x21 x02 x01 x22 y12 y11
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross2, cross0]
      revert b1 b2 a1 a2 y21 y22 y01 y02 x01 x11 x02 x12 x21 x22
      decide

/-- 🏆 THEOREM 1: The composite short root unipotent automorphism $x_{\alpha_1 + \alpha_2}(1)$. -/
def uMid : SplitOctF2Aut := ⟨uMidEquiv, isSplitOctF2Aut_uMid⟩

/-- All three positive root automorphisms are involutions of order 2. -/
theorem uShort_sq : uShort * uShort = 1 := unipotentShortAut_order true
theorem uLong_sq : uLong * uLong = 1 := unipotentLongAut_order true

theorem uMid_sq : uMid * uMid = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-- 🏆 THEOREM 2: Exact G₂ Steinberg Commutator Relation over 𝔽₂:
    [u_S, u_L] = u_S * u_L * u_S * u_L = u_{α₁ + α₂} -/
theorem steinberg_commutator_short_long :
    uShort * uLong * uShort * uLong = uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-- 🏆 THEOREM 3: Commutation between uMid and uShort:
    [u_{α₁ + α₂}, u_S] = 1 -/
theorem uMid_commutes_uShort :
    uMid * uShort = uShort * uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-- 🏆 THEOREM 4: Commutation between uMid and uLong:
    [u_{α₁ + α₂}, u_L] = 1 -/
theorem uMid_commutes_uLong :
    uMid * uLong = uLong * uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

end InfoGeometry.Algebra.Zorn.G2SteinbergRoots
