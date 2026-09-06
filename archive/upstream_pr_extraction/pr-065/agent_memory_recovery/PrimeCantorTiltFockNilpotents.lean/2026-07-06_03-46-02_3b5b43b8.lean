  calc
    (Complex.I * B) * (Complex.I * B)
        = (Complex.I * Complex.I) * (B * B) := by ring
    _ = (-1) * 1 := by rw [Complex.I_mul_I, hB]
    _ = -1 := by simp

/--
Hyperbolic-to-elliptic class transport under the Wick map `B ↦ I*B`
in the scalar-square model.
-/
@[rep_depth thermo]
theorem wickRotate_squareClass_transport
    :
    classifySquareValue (Int.ofNat 1) = some OpSquareClass.hyperbolic ∧
    classifySquareValue (-1) = some OpSquareClass.elliptic := by
  constructor
  · simpa using classifySquareValue_one
  · simpa using classifySquareValue_neg_one

end InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents
