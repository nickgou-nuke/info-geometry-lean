structure CCCState where
  D : Int
  D_dagger : Int
  is_balanced : D + D_dagger = 1

def InfinityState : CCCState := {
  D := 1,
  D_dagger := 0,
  is_balanced := rfl
}

def ZeroState : CCCState := {
  D := 0,
  D_dagger := 1,
  is_balanced := rfl
}

def conformal_inversion (s : CCCState) : CCCState := {
  D := s.D_dagger,
  D_dagger := s.D,
  is_balanced := by 
    have h : s.D_dagger + s.D = s.D + s.D_dagger := Int.add_comm s.D_dagger s.D
    rw [h]
    exact s.is_balanced
}

theorem inversion_involution (s : CCCState) : conformal_inversion (conformal_inversion s) = s := by
  cases s
  rfl

theorem inversion_maps_infinity_to_zero : conformal_inversion InfinityState = ZeroState := by
  rfl

theorem inversion_maps_zero_to_infinity : conformal_inversion ZeroState = InfinityState := by
  rfl
