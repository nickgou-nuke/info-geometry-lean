import InfoGeometry.Exceptional.FreudenthalGenericJacobiClosure

namespace InfoGeometry.Exceptional.Freudenthal

def laneOfFin : Fin 6 → JacobiLane
  | 0 => .minus2
  | 1 => .minus1
  | 2 => .zeroSymp
  | 3 => .zeroScale
  | 4 => .plus1
  | 5 => .plus2

def finOfLane : JacobiLane → Fin 6
  | .minus2 => 0
  | .minus1 => 1
  | .zeroSymp => 2
  | .zeroScale => 3
  | .plus1 => 4
  | .plus2 => 5

def laneFinEquiv : Fin 6 ≃ JacobiLane where
  toFun := laneOfFin
  invFun := finOfLane
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; cases i <;> rfl

noncomputable instance : Fintype JacobiLane :=
  Fintype.ofEquiv (Fin 6) laneFinEquiv

@[simp] theorem laneFinEquiv_apply (i : Fin 6) :
    laneFinEquiv i = laneOfFin i := rfl

@[simp] theorem laneFinEquiv_symm_apply (l : JacobiLane) :
    laneFinEquiv.symm l = finOfLane l := rfl

end InfoGeometry.Exceptional.Freudenthal
