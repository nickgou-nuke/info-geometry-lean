import InfoGeometry.Canonical.BostConnesSuperalgebra

/-!
# Deformed Super-Cuntz Warp

This file gives a theorem-safe algebraic socket for the proposed
`𝒪_{N|M}(q)` mechanism.

It intentionally keeps the analytic/C*-completion and discrete-gravity
interpretation as explicit data.  The file proves only readback theorems from
that data:

* bosonic and fermionic generators carry a `ℤ₂` grade;
* the supplied `q`-deformed Cuntz/CAR-style relations are exposed without
  deriving them from undeformed Cuntz relations;
* a supplied modular flow scales prime-labelled generators by the supplied
  phase/dilation character;
* a supplied `q`-warped tessellation has deficit angle equal to the mismatch
  between flat and `q`-warped local angle sums.

No theorem here asserts existence of a universal C*-superalgebra, analytic
Tomita--Takesaki modular flow, Regge calculus completion, or physical gravity
law.  Those are model data/closure debt, not consequences of this finite socket.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeformedSuperCuntzWarp

open scoped BigOperators

/-! ## 1. Graded `q`-deformed super-Cuntz socket -/

/-- The two parity grades used by the finite super-Cuntz API. -/
inductive SuperGrade where
  | even
  | odd
  deriving DecidableEq, Repr

/-- Multiplication table for the `ℤ₂` grading. -/
def SuperGrade.mul : SuperGrade → SuperGrade → SuperGrade
  | .even, g => g
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : One SuperGrade where
  one := .even

instance : Mul SuperGrade where
  mul := SuperGrade.mul

@[simp] theorem even_mul (g : SuperGrade) : SuperGrade.even * g = g := by
  cases g <;> rfl

@[simp] theorem mul_even (g : SuperGrade) : g * SuperGrade.even = g := by
  cases g <;> rfl

@[simp] theorem odd_mul_odd : SuperGrade.odd * SuperGrade.odd = SuperGrade.even := rfl

/--
A proof-carrying finite `q`-deformed super-Cuntz algebra interface.

`Bos` indexes the even/bosonic generators and `Ferm` indexes the odd/fermionic
generators.  The deformation parameter `q` lives in the same operator algebra;
centrality, positivity, unitarity, and C*-norm data are deliberately not
asserted here.
-/
structure DeformedSuperCuntzAlgebra
    (Op Bos Ferm : Type*) [Ring Op] [StarRing Op]
    [DecidableEq Bos] [DecidableEq Ferm] where
  /-- Deformation parameter. -/
  q : Op
  /-- Even/bosonic generators. -/
  boson : Bos → Op
  /-- Odd/fermionic generators. -/
  fermion : Ferm → Op
  /-- `q`-deformed bosonic Cuntz/Toeplitz-style relation. -/
  boson_q_relation : ∀ i j : Bos,
    star (boson i) * boson j - q * (boson j * star (boson i)) = if i = j then 1 else 0
  /-- `q`-deformed fermionic CAR-style relation. -/
  fermion_q_relation : ∀ i j : Ferm,
    star (fermion i) * fermion j + q * (fermion j * star (fermion i)) = if i = j then 1 else 0
  /-- Optional nilpotence of each odd generator, matching the square-free sector. -/
  fermion_sq_zero : ∀ i : Ferm, fermion i * fermion i = 0

namespace DeformedSuperCuntzAlgebra

variable {Op Bos Ferm : Type*} [Ring Op] [StarRing Op]
variable [DecidableEq Bos] [DecidableEq Ferm]
variable (A : DeformedSuperCuntzAlgebra Op Bos Ferm)

/-- Bosonic generators have even grade. -/
def bosonGrade (_A : DeformedSuperCuntzAlgebra Op Bos Ferm) (_i : Bos) : SuperGrade :=
  SuperGrade.even

/-- Fermionic generators have odd grade. -/
def fermionGrade (_A : DeformedSuperCuntzAlgebra Op Bos Ferm) (_i : Ferm) : SuperGrade :=
  SuperGrade.odd

@[simp] theorem boson_grade (i : Bos) : A.bosonGrade i = SuperGrade.even := rfl

@[simp] theorem fermion_grade (i : Ferm) : A.fermionGrade i = SuperGrade.odd := rfl

/-- Readback of the supplied `q`-bosonic relation. -/
theorem boson_q_commutator (i j : Bos) :
    star (A.boson i) * A.boson j - A.q * (A.boson j * star (A.boson i)) =
      if i = j then 1 else 0 :=
  A.boson_q_relation i j

/-- Readback of the supplied `q`-fermionic relation. -/
theorem fermion_q_anticommutator (i j : Ferm) :
    star (A.fermion i) * A.fermion j + A.q * (A.fermion j * star (A.fermion i)) =
      if i = j then 1 else 0 :=
  A.fermion_q_relation i j

/-- Readback: odd generators are nilpotent when the square-free-sector property is supplied. -/
theorem fermion_nilpotent (i : Ferm) : A.fermion i * A.fermion i = 0 :=
  A.fermion_sq_zero i

end DeformedSuperCuntzAlgebra

/-! ## 2. Prime modular flow as edge scaling data -/

/--
A proof-carrying modular-flow socket for prime-labelled generators.

`phase t p` may be a unitary phase (`p^{it}`) or an analytically continued real
scale (`p^τ`), depending on the model.  This file only records the algebraic
scaling law supplied by the model.
-/
structure PrimeModularDilation
    (Op : Type*) [Ring Op] (PrimeLabel : Type*) where
  /-- Prime-labelled edge/Cuntz generator. -/
  generator : PrimeLabel → Op
  /-- Modular-time action on operators. -/
  sigma : ℝ → Op → Op
  /-- Energy/length readout, e.g. `log p`. -/
  energy : PrimeLabel → ℝ
  /-- Multiplicative phase or analytically continued dilation character. -/
  phase : ℝ → PrimeLabel → Op
  /-- The supplied modular-flow scaling law. -/
  sigma_generator : ∀ (t : ℝ) (p : PrimeLabel),
    sigma t (generator p) = phase t p * generator p

namespace PrimeModularDilation

variable {Op PrimeLabel : Type*} [Ring Op]
variable (D : PrimeModularDilation Op PrimeLabel)

/-- Readback of the modular-flow scaling action on a prime-labelled edge. -/
theorem scales_generator (t : ℝ) (p : PrimeLabel) :
    D.sigma t (D.generator p) = D.phase t p * D.generator p :=
  D.sigma_generator t p

/-- The edge energy/length observable is the supplied modular Hamiltonian readout. -/
def edgeEnergy (p : PrimeLabel) : ℝ :=
  D.energy p

@[simp] theorem edgeEnergy_eq (p : PrimeLabel) : D.edgeEnergy p = D.energy p := rfl

end PrimeModularDilation

/-! ## 3. `q`-warped tessellation and deficit angle -/

/--
A finite local tessellation packet with both flat and `q`-warped angle readouts.

The deficit angle is defined as the mismatch between the flat local angle sum
and the `q`-warped local angle sum around a vertex.
-/
structure QWarpedTessellation (Cell Vertex : Type*) where
  /-- Incidence relation: the cell is incident to the vertex. -/
  incident : Cell → Vertex → Prop
  /-- Flat/local Euclidean angle contribution. -/
  flatAngle : Cell → Vertex → ℝ
  /-- `q`-warped angle contribution. -/
  qAngle : Cell → Vertex → ℝ

namespace QWarpedTessellation

variable {Cell Vertex : Type*} [Fintype Cell]
variable (T : QWarpedTessellation Cell Vertex)

/-- Cells incident to a vertex. -/
def incidentCells (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)] : Finset Cell :=
  Finset.univ.filter (fun c => T.incident c v)

/-- Flat angle sum around a vertex. -/
def flatAngleSum (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)] : ℝ :=
  Finset.sum (T.incidentCells v) (fun c => T.flatAngle c v)

/-- `q`-warped angle sum around a vertex. -/
def qAngleSum (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)] : ℝ :=
  Finset.sum (T.incidentCells v) (fun c => T.qAngle c v)

/-- Discrete deficit angle: flat sum minus `q`-warped sum. -/
def deficitAngle (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)] : ℝ :=
  T.flatAngleSum v - T.qAngleSum v

/-- Curvature vanishes at a vertex when the supplied flat and `q` angle sums agree. -/
theorem deficitAngle_eq_zero_of_angle_sums_eq
    (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)]
    (h : T.qAngleSum v = T.flatAngleSum v) :
    T.deficitAngle v = 0 := by
  simp [deficitAngle, h]

/-- A nonzero mismatch is exactly a nonzero deficit angle. -/
theorem deficitAngle_ne_zero_iff_angle_sums_ne
    (v : Vertex) [DecidablePred (fun c : Cell => T.incident c v)] :
    T.deficitAngle v ≠ 0 ↔ T.flatAngleSum v ≠ T.qAngleSum v := by
  constructor
  · intro h hsum
    exact h (by simp [deficitAngle, hsum])
  · intro h hzero
    apply h
    have : T.flatAngleSum v - T.qAngleSum v = 0 := by
      simpa [deficitAngle] using hzero
    exact sub_eq_zero.mp this

end QWarpedTessellation

/-! ## 4. Combined finite model packet -/

/--
Finite data packet for the algebraic mechanism:
`q`-super-Cuntz relations + modular edge scaling + `q`-warped local curvature.
-/
structure DeformedSuperCuntzWarpPacket
    (Op Bos Ferm PrimeLabel Cell Vertex : Type*)
    [Ring Op] [StarRing Op] [DecidableEq Bos] [DecidableEq Ferm] where
  algebra : DeformedSuperCuntzAlgebra Op Bos Ferm
  modular : PrimeModularDilation Op PrimeLabel
  tessellation : QWarpedTessellation Cell Vertex

namespace DeformedSuperCuntzWarpPacket

variable {Op Bos Ferm PrimeLabel Cell Vertex : Type*}
variable [Ring Op] [StarRing Op] [DecidableEq Bos] [DecidableEq Ferm]
variable (P : DeformedSuperCuntzWarpPacket Op Bos Ferm PrimeLabel Cell Vertex)

/-- The packet exposes the even/odd unification layer. -/
theorem boson_even (i : Bos) : P.algebra.bosonGrade i = SuperGrade.even := rfl

/-- The packet exposes the square-free odd layer. -/
theorem fermion_odd (i : Ferm) : P.algebra.fermionGrade i = SuperGrade.odd := rfl

/-- The packet exposes modular scaling of prime-labelled edges. -/
theorem modular_scales_edge (t : ℝ) (p : PrimeLabel) :
    P.modular.sigma t (P.modular.generator p) =
      P.modular.phase t p * P.modular.generator p :=
  P.modular.sigma_generator t p

end DeformedSuperCuntzWarpPacket

end InfoGeometry.Canonical.DeformedSuperCuntzWarp

end noncomputable section
