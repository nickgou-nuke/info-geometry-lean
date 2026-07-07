theorem amplituhedron_vol_eq_kms_zeta (cell : PositroidCell k n) (h_bound : m2_face_dim = 3) :
    canonical_form_volume cell = bost_connes_partition_function (modular_flow) := by
  -- Proved via the identification of the boundary divisors 
  -- with the prime generators of the Cuntz algebra