import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import Mathlib.Tactic

namespace InfoGeometry.Algebra.Zorn.G2TwoExactSixGenerators

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/- The six matrices exported by the carrier-level CAS artifact, written as
   coordinate maps.  The coordinate order is (a,b,x0,x1,x2,y0,y1,y2). -/
def g1 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y2, X.y1, X.y0, X.x2, X.x1, X.x0⟩

def g2 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y1 ^^ X.y2, X.y0 ^^ X.y1, X.y0, X.x2,
    X.x1 ^^ X.x2, X.x0 ^^ X.x1 ^^ X.x2⟩

def g3 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b ^^ X.x2 ^^ X.y0, X.a ^^ X.x2 ^^ X.y0,
    X.a ^^ X.b ^^ X.x1 ^^ X.x2 ^^ X.y2, X.x2 ^^ X.y1,
    X.y0, X.x2, X.x1 ^^ X.y0, X.a ^^ X.b ^^ X.x0 ^^ X.x2 ^^ X.y0 ^^ X.y1⟩

def g4 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, X.x0, X.x1 ^^ X.x2, X.x2, X.y0, X.y1, X.y1 ^^ X.y2⟩

def g5 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a ^^ X.x2, X.b ^^ X.x2, X.x0 ^^ X.y1, X.x1 ^^ X.y0,
    X.x2, X.y0, X.y1, X.a ^^ X.b ^^ X.x2 ^^ X.y2⟩

def g6 (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.b, X.a, X.y1, X.y0, X.y2, X.x1, X.x0, X.x2⟩

private theorem map_add (f : SplitOctF2 → SplitOctF2)
    (hf : ∀ X Y, f (add X Y) = add (f X) (f Y)) :
    ∀ X Y, f (add X Y) = add (f X) (f Y) := hf

theorem g1_add (X Y : SplitOctF2) : g1 (add X Y) = add (g1 X) (g1 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g1, add, add2]

theorem g2_add (X Y : SplitOctF2) : g2 (add X Y) = add (g2 X) (g2 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g2, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g3_add (X Y : SplitOctF2) : g3 (add X Y) = add (g3 X) (g3 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g3, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g4_add (X Y : SplitOctF2) : g4 (add X Y) = add (g4 X) (g4 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g4, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g5_add (X Y : SplitOctF2) : g5 (add X Y) = add (g5 X) (g5 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g5, add, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g6_add (X Y : SplitOctF2) : g6 (add X Y) = add (g6 X) (g6 Y) := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  ext <;> simp [g6, add, add2]

theorem g1_involutive (X : SplitOctF2) : g1 (g1 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rfl

theorem g2_involutive (X : SplitOctF2) : g2 (g2 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [g2, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g3_involutive (X : SplitOctF2) : g3 (g3 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [g3, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g4_involutive (X : SplitOctF2) : g4 (g4 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [g4, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g5_involutive (X : SplitOctF2) : g5 (g5 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  ext <;> simp [g5, add2, Bool.xor_left_comm, Bool.xor_comm]

theorem g6_involutive (X : SplitOctF2) : g6 (g6 X) = X := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rfl

end InfoGeometry.Algebra.Zorn.G2TwoExactSixGenerators
