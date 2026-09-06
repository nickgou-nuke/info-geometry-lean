  dsimp [map_to_01inf]
  have h_num : (z2 - z1) * (z2 - z3) = (z2 - z3) * (z2 - z1) := by ring
  rw [h_num]
  exact div_self (mul_ne_zero h1 h2)

noncomputable def disk_to_half_plane (z : ℂ) : ℂ := (z + I) / (I * z + 1)

theorem disk_to_half_plane_zero : disk_to_half_plane 0 = I := by
  unfold disk_to_half_plane
  rw [zero_add, mul_zero, zero_add, div_one]

end InfoGeometry
