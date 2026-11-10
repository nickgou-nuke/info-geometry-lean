import Omega.Conclusion.LeyangLattesHypercubeExactFormZeroCurvature

/-!
# Cube potential reconstruction from curl control

This owner exposes the finite Boolean-hypercube potential result in the SPG
namespace. The carrier is the `2k`-dimensional Boolean cube, the potential is
the weighted coordinate sum, and the two-form boundary is its discrete curl.
-/

namespace Omega.SPG

/-- A weighted coordinate potential has the prescribed increment on every
oriented edge from a zero coordinate to a one coordinate, and its discrete
curl vanishes on every coordinate square. -/
theorem paper_spg_cube_potential_reconstruction_by_curl
    {k : Nat} (weight : Fin (2 * k) → Real) :
    (∀ (x : Omega.Conclusion.conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k)
        (i : Fin (2 * k)),
      x i = false →
        Omega.Conclusion.conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment
          weight i x = weight i) ∧
      (∀ (x : Omega.Conclusion.conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex k)
          (i j : Fin (2 * k)),
        i ≠ j → x i = false → x j = false →
          Omega.Conclusion.conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_boundary
            weight i j x = 0) := by
  exact Omega.Conclusion.paper_conclusion_leyang_lattes_hypercube_exact_form_zero_curvature
    weight

end Omega.SPG
