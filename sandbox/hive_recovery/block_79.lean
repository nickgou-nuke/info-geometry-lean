def modified_born_probability (Pi Pf : Projector K n) (S : SMatrix K n) : K :=
  Matrix.trace (Pf.P * S.S * Pi.P)