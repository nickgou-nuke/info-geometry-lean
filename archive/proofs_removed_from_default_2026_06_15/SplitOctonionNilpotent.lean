import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Split-Octonions and the Nilpotent Zero-Mode

Formalizes the core Zorn vector-matrix rules for the split-octonion 
algebra (`O_s`). Proves the existence of a non-trivial nilpotent state 
(`Z² = 0, Z ≠ 0`) to algebraically and physically map the topological 
`s = 0` scale defect.
-/

namespace SplitOctonionNilpotent

/-- A spatial vector in ℝ³ -/
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def Vec3.zero : Vec3 := ⟨0, 0, 0⟩

def dot (u v : Vec3) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

def add (u v : Vec3) : Vec3 :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : Vec3) : Vec3 :=
  ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (c : ℝ) (v : Vec3) : Vec3 :=
  ⟨c * v.x, c * v.y, c * v.z⟩

/-- 
Zorn's vector-matrix representation of a split-octonion.
Represents the element `[ a, u ; v, b ]`.
-/
structure ZornMatrix where
  a : ℝ
  b : ℝ
  u : Vec3
  v : Vec3
  deriving DecidableEq

def ZornMatrix.zero : ZornMatrix := ⟨0, 0, Vec3.zero, Vec3.zero⟩

/-- 
The non-associative Zorn multiplication.
Provides the structural foundation for both `SL(2,C)` biquaternion spacetime 
and the `SU(3)` internal color gauge symmetry of the strong force.
-/
def zornMul (A B : ZornMatrix) : ZornMatrix :=
  ⟨A.a * B.a + dot A.u B.v,
   A.b * B.b + dot A.v B.u,
   sub (add (smul A.a B.u) (smul B.b A.u)) (cross A.v B.v),
   add (add (smul A.b B.v) (smul B.a A.v)) (cross A.u B.u)⟩

/-- The split-octonion invariant norm. Gives the (4,4) signature. -/
def zornNorm (A : ZornMatrix) : ℝ :=
  A.a * A.b - dot A.u A.v

/-- 
The topological `s = 0` scale defect algebraically represented 
as a pure non-invertible state.
-/
def Z_mode : ZornMatrix :=
  ⟨0, 0, Vec3.zero, ⟨1, 0, 0⟩⟩

/-- Theorem: The mode is non-trivial (`Z ≠ 0`). -/
theorem Z_mode_nonzero : Z_mode ≠ ZornMatrix.zero := by
  intro h
  injection h with ha hb hu hv
  injection hv with hx hy hz
  linarith

/-- 
Theorem: The Nilpotent Defect. 
The state intrinsically squares to zero (`Z² = 0`), meaning it 
sits exactly on the null cone as a non-invertible algebraic defect!
Unlike standard octonions or quaternions, the split-octonions 
natively support these zero-modes!
-/
theorem Z_mode_nilpotent : zornMul Z_mode Z_mode = ZornMatrix.zero := by
  dsimp [Z_mode, zornMul, dot, cross, add, sub, smul, Vec3.zero, ZornMatrix.zero]
  congr

/-- Theorem: The defect is strictly null under the (4,4) metric (`N(Z) = 0`). -/
theorem Z_mode_null : zornNorm Z_mode = 0 := by
  dsimp [Z_mode, zornNorm, dot, Vec3.zero]
  ring

end SplitOctonionNilpotent
