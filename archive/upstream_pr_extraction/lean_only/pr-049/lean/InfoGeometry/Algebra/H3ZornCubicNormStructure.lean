import InfoGeometry.Algebra.QuadraticJordanH3Zorn

/-!
# Cubic norm structure identity for the split Albert carrier

The formulas and cyclic convention follow Example 6.14 of
Garibaldi--Petersson--Racine, *Albert Algebras over Commutative Rings*.
This module proves the global adjoint identity structurally from the Zorn
composition laws; it performs no coordinate enumeration.
-/

namespace InfoGeometry.Algebra.H3Zorn

variable {R : Type*} [CommRing R]

/-- The cubic adjoint identity `(X#)# = N(X) X` for the split-Albert carrier. -/
theorem adjointQuad_adjointQuad (X : H3Zorn R) :
    adjointQuad (adjointQuad X) = normCubic X • X := by
  rcases X with ⟨a1, a2, a3, a, b, c⟩
  apply ext_h3
  · simpa only [adjointQuad, normCubic, smul_readback, sub_readback,
      sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] using
      (ZornVectorMatrix.adjoint_diagonal_composition a1 a2 a3 a b c)
  · have h := ZornVectorMatrix.adjoint_diagonal_composition a2 a3 a1 b c a
    have ht := ZornVectorMatrix.trace_mul_cyclic a b c
    change ZornVectorMatrix.trace ((a * b) * c) =
      ZornVectorMatrix.trace ((b * c) * a) at ht
    rw [← ht] at h
    simp only [adjointQuad, normCubic, smul_readback, sub_readback,
      sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] at h ⊢
    convert h using 1 <;> ring
  · have h := ZornVectorMatrix.adjoint_diagonal_composition a3 a1 a2 c a b
    have ht := ZornVectorMatrix.trace_mul_cyclic c a b
    change ZornVectorMatrix.trace ((c * a) * b) =
      ZornVectorMatrix.trace ((a * b) * c) at ht
    rw [ht] at h
    simp only [adjointQuad, normCubic, smul_readback, sub_readback,
      sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] at h ⊢
    convert h using 1 <;> ring
  · simp only [adjointQuad, normCubic]
    rw [ZornVectorMatrix.conj_sub, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_smul, ZornVectorMatrix.conj_sub,
      ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_smul]
    simpa only [sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] using
      (ZornVectorMatrix.adjoint_component_composition a1 a2 a3 a b c)
  · simp only [adjointQuad, normCubic]
    rw [ZornVectorMatrix.conj_sub, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_smul, ZornVectorMatrix.conj_sub,
      ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_smul]
    have h := ZornVectorMatrix.adjoint_component_composition a2 a3 a1 b c a
    have ht := ZornVectorMatrix.trace_mul_cyclic a b c
    change ZornVectorMatrix.trace ((a * b) * c) =
      ZornVectorMatrix.trace ((b * c) * a) at ht
    rw [← ht] at h
    simp only [adjointQuad, normCubic, smul_readback, sub_readback,
      sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] at h ⊢
    convert h using 1 <;> ring
  · simp only [adjointQuad, normCubic]
    rw [ZornVectorMatrix.conj_sub, ZornVectorMatrix.conj_mul,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_smul, ZornVectorMatrix.conj_sub,
      ZornVectorMatrix.conj_mul, ZornVectorMatrix.conj_conj,
      ZornVectorMatrix.conj_conj, ZornVectorMatrix.conj_smul]
    have h := ZornVectorMatrix.adjoint_component_composition a3 a1 a2 c a b
    have ht := ZornVectorMatrix.trace_mul_cyclic c a b
    change ZornVectorMatrix.trace ((c * a) * b) =
      ZornVectorMatrix.trace ((a * b) * c) at ht
    rw [ht] at h
    simp only [adjointQuad, normCubic, smul_readback, sub_readback,
      sub_eq_add_neg, ZornVectorMatrix.sub_eq_add_neg, ← zvm_add_def, ← zvm_neg_def,
      ← zvm_smul_def, ← zvm_mul_def] at h ⊢
    convert h using 1 <;> ring

/-- Polarization of the cubic norm.  Equivalently, the coefficient linear in
`Y` in `N(X + Y)` is `traceBilin (X#) Y`. -/
theorem normCubic_add (X Y : H3Zorn R) :
    normCubic (X + Y) = normCubic X + normCubic Y +
      traceBilin (adjointQuad X) Y + traceBilin (adjointQuad Y) X := by
  rcases X with ⟨x1, x2, x3, a, b, c⟩
  rcases Y with ⟨y1, y2, y3, d, e, f⟩
  simp only [add_readback, normCubic, traceBilin, adjointQuad]
  rw [ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj b e,
    ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj c f,
    ZornVectorMatrix.norm_add_eq_norm_add_norm_add_trace_mul_conj a d]
  simp only [ZornVectorMatrix.add_mul, ZornVectorMatrix.mul_add,
    ZornVectorMatrix.trace_add, ZornVectorMatrix.sub_mul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.trace_sub,
    ZornVectorMatrix.trace_smul]
  rw [ZornVectorMatrix.trace_conj_triple_reverse d b c,
    ZornVectorMatrix.trace_conj_triple_reverse e c a,
    ZornVectorMatrix.trace_conj_triple_reverse f a b,
    ZornVectorMatrix.trace_conj_triple_reverse a e f,
    ZornVectorMatrix.trace_conj_triple_reverse b f d,
    ZornVectorMatrix.trace_conj_triple_reverse c d e]
  rw [ZornVectorMatrix.trace_mul_cyclic e c a,
    ZornVectorMatrix.trace_mul_cyclic c a e,
    ZornVectorMatrix.trace_mul_cyclic f a b,
    ZornVectorMatrix.trace_mul_cyclic b f d,
    ZornVectorMatrix.trace_mul_cyclic f d b,
    ZornVectorMatrix.trace_mul_cyclic c d e]
  rw [ZornVectorMatrix.trace_mul_conj_comm a d,
    ZornVectorMatrix.trace_mul_conj_comm b e,
    ZornVectorMatrix.trace_mul_conj_comm c f]
  ring

/-- The split-Albert norm is homogeneous of degree three. -/
theorem normCubic_smul (r : R) (X : H3Zorn R) :
    normCubic (r • X) = r ^ 3 * normCubic X := by
  rw [smul_readback]
  simp only [normCubic, ZornVectorMatrix.norm_smul,
    ZornVectorMatrix.smul_mul, ZornVectorMatrix.mul_smul,
    ZornVectorMatrix.trace_smul]
  ring

end InfoGeometry.Algebra.H3Zorn
