This is the one-dimensional body-level shadow of the operator inverse data.
Higher-dimensional/operator versions should replace `ℝ` with the existing
`CertifiedInverseKernel` surfaces.
-/
structure ScalarPenroseInverse where
  a : ℝ
  aPlus : ℝ
  aba : a * aPlus * a = a
  bab : aPlus * a * aPlus = aPlus

/-- Scalar Drazin inverse witness for spectral/topological memory. -/
structure ScalarDrazinInverse where
  a : ℝ
  aD : ℝ
  index : ℕ
  commute : a * aD = aD * a
  reflexive : aD * a * aD = aD
  spectral :
    a ^ (index + 1) * aD = a ^ index

/--