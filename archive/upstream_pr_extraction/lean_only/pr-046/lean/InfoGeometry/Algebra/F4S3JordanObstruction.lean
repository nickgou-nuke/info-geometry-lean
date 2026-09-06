import InfoGeometry.Algebra.F4Derivations

namespace InfoGeometry.Algebra

noncomputable section

/-!
  A concrete obstruction to treating the raw Peirce permutation `s12` as an
  automorphism of the Albert/Jordan data.  This theorem deliberately targets
  the quadratic adjoint already used by `H3Zorn.U`; it does not claim a
  conclusion about `candidateJordanMul` without a separate calculation.
-/

/-- The conjugated `s12` transport preserves the verified quadratic adjoint.
The proof uses the Zorn conjugation anti-multiplicativity and norm invariance;
it does not assume a Jordan product that is not defined on this carrier. -/
theorem s12_preserve_h3zorn_adjointQuad (X : H3Zorn ℝ) :
    S3OnH3Zorn S3Perm.s12 X.adjointQuad =
      (S3OnH3Zorn S3Perm.s12 X).adjointQuad := by
  cases X
  apply H3Zorn.ext_h3
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.norm_conj]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.norm_conj]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.norm_conj]
    ring
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.norm_conj]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.norm_conj]
  · simp [H3Zorn.adjointQuad, S3OnH3Zorn, S3OnH3ZornPeirce,
      h3zornFromPeirce, h3zornPeirce, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.norm_conj]

/-- The Hermitian transposition of the first two diagonal slots conjugates all
off-diagonal Zorn entries.  This is the coordinate transport dictated by the
displayed Albert matrix layout, not the raw Peirce-slot permutation. -/
def twistedS12OnH3ZornPeirce (P : H3ZornPeirce) : H3ZornPeirce :=
  { diag₁ := P.diag₂
    diag₂ := P.diag₁
    diag₃ := P.diag₃
    off₁₂ := ZornVectorMatrix.conj P.off₂₃
    off₂₃ := ZornVectorMatrix.conj P.off₁₂
    off₃₁ := ZornVectorMatrix.conj P.off₃₁ }

@[simp] theorem twistedS12OnH3ZornPeirce_involutive (P : H3ZornPeirce) :
    twistedS12OnH3ZornPeirce (twistedS12OnH3ZornPeirce P) = P := by
  cases P
  simp [twistedS12OnH3ZornPeirce]

/-- The corresponding linear transport on the verified `H3Zorn` carrier. -/
def twistedS12OnH3Zorn (X : H3Zorn ℝ) : H3Zorn ℝ :=
  h3zornFromPeirce (twistedS12OnH3ZornPeirce (h3zornPeirce X))

@[simp] theorem twistedS12OnH3Zorn_involutive (X : H3Zorn ℝ) :
    twistedS12OnH3Zorn (twistedS12OnH3Zorn X) = X := by
  unfold twistedS12OnH3Zorn
  rw [h3zornPeirce_h3zornFromPeirce]
  rw [twistedS12OnH3ZornPeirce_involutive]
  exact h3zornFromPeirce_h3zornPeirce X

/-- The scalar trace of a triple Zorn product is cyclic.  The proof uses
the symmetric two-factor trace and the vanishing trace of the associator,
so it does not assume associativity of the Zorn multiplication. -/
theorem ZornVectorMatrix.trace_mul_mul_cyclic
    (X Y Z : ZornVectorMatrix ℝ) :
    ZornVectorMatrix.trace (ZornVectorMatrix.mul
      (ZornVectorMatrix.mul X Y) Z) =
      ZornVectorMatrix.trace (ZornVectorMatrix.mul
        (ZornVectorMatrix.mul Y Z) X) := by
  calc
    ZornVectorMatrix.trace (ZornVectorMatrix.mul
        (ZornVectorMatrix.mul X Y) Z) =
        ZornVectorMatrix.trace (ZornVectorMatrix.mul Z
          (ZornVectorMatrix.mul X Y)) :=
      ZornVectorMatrix.trace_mul_comm (ZornVectorMatrix.mul X Y) Z
    _ = ZornVectorMatrix.trace (ZornVectorMatrix.mul
          (ZornVectorMatrix.mul Z X) Y) := by
      apply sub_eq_zero.mp
      have h := ZornVectorMatrix.trace_associator Z X Y
      simp [ZornVectorMatrix.associator] at h
      linarith
    _ = ZornVectorMatrix.trace (ZornVectorMatrix.mul Y
          (ZornVectorMatrix.mul Z X)) :=
      ZornVectorMatrix.trace_mul_comm (ZornVectorMatrix.mul Z X) Y
    _ = ZornVectorMatrix.trace (ZornVectorMatrix.mul
          (ZornVectorMatrix.mul Y Z) X) := by
      apply sub_eq_zero.mp
      have h := ZornVectorMatrix.trace_associator Y Z X
      simp [ZornVectorMatrix.associator] at h
      linarith

end

end InfoGeometry.Algebra
