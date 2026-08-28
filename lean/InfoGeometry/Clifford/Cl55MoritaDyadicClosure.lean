import InfoGeometry.Algebra.Clifford55DyadicMatrixClosure

namespace InfoGeometry.Clifford.Cl55

/-!
# Cl(5,5) Morita Dyadic Closure (Twistor Operator Holography)

This module exports the formal proof that the tensor product of left ideals (Twistors $\mathcal{I}_L$)
and right ideals (Dual twistors $\mathcal{I}_R$) spans the full 1024-dimensional
conformal matrix algebra $\operatorname{Cl}(5,5) \cong \operatorname{Mat}_{32}(\mathbb{R})$.
-/

open InfoGeometry.Algebra.Clifford55

abbrev Dim32 := InfoGeometry.Algebra.Clifford55.Dim32
abbrev Cl55Mat := InfoGeometry.Algebra.Clifford55.Cl55Mat

abbrev P_vac : Cl55Mat := Pvac
abbrev LeftIdeal : Submodule ℝ Cl55Mat := InfoGeometry.Algebra.Clifford55.LeftIdeal
abbrev RightIdeal : Submodule ℝ Cl55Mat := InfoGeometry.Algebra.Clifford55.RightIdeal

abbrev ket : Dim32 → Cl55Mat := InfoGeometry.Algebra.Clifford55.ket
abbrev bra : Dim32 → Cl55Mat := InfoGeometry.Algebra.Clifford55.bra

theorem ket_mem_left (i : Dim32) : ket i ∈ LeftIdeal :=
  InfoGeometry.Algebra.Clifford55.ket_mem_left i

theorem bra_mem_right (j : Dim32) : bra j ∈ RightIdeal :=
  InfoGeometry.Algebra.Clifford55.bra_mem_right j

theorem dyad_eq_single (i j : Dim32) : ket i * bra j = Matrix.single i j 1 :=
  InfoGeometry.Algebra.Clifford55.dyad_eq_single i j

/--
MAIN THEOREM (The Dyadic Span Theorem):
The space of all dyads $|Z\rangle\langle W|$ between the left and right ideals
spans the full 1024-dimensional matrix algebra $\operatorname{Cl}(5,5)$.
-/
theorem dyadic_span_eq_top :
    Submodule.span ℝ (Set.range (fun p : Dim32 × Dim32 => ket p.1 * bra p.2)) = ⊤ :=
  InfoGeometry.Algebra.Clifford55.dyadic_span_eq_top

end InfoGeometry.Clifford.Cl55
