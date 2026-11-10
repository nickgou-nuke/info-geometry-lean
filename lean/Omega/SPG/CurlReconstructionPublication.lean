import Omega.SPG.CubePotentialCurl

open Omega.Conclusion

namespace Omega.SPG

/-- On a four-coordinate Boolean cube, vanishing discrete curl makes the two
two-step coordinate paths to the same vertex have equal accumulated increment.
This is path independence for the explicit weighted-coordinate potential. -/
theorem paper_cubical_stokes_curl_reconstruction
    (weight : Fin (2 * 2) → Real)
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex 2)
    (i j : Fin (2 * 2))
    (hij : i ≠ j) (hxi : x i = false) (hxj : x j = false) :
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i x +
        conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight j
          (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i x) =
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight j x +
        conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment weight i
          (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) := by
  have hcurl := (paper_spg_cube_potential_reconstruction_by_curl (k := 2) weight).2
    x i j hij hxi hxj
  dsimp [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_boundary] at hcurl
  linear_combination hcurl

/-- The same curl-controlled potential reconstructs its value after switching
two initially zero coordinates: the endpoint difference is the sum of the two
coordinate weights, independent of the order of the switches. -/
theorem paper_spg_square_potential_endpoint_reconstruction
    (weight : Fin (2 * 2) → Real)
    (x : conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_vertex 2)
    (i j : Fin (2 * 2))
    (hij : i ≠ j) (hxi : x i = false) (hxj : x j = false) :
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i
          (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x)) -
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight x =
        weight i + weight j := by
  have hInc := (paper_spg_cube_potential_reconstruction_by_curl (k := 2) weight).1
  have hji :
      (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) i = false := by
    simp [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue,
      hij, hxi]
  have hi := hInc
    (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) i hji
  have hj := hInc x j hxj
  dsimp [conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_increment] at hi hj
  calc
    conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i
          (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x)) -
      conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight x =
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
            (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue i
              (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x)) -
          conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
            (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x)) +
        (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight
            (conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_setTrue j x) -
          conclusion_leyang_lattes_hypercube_exact_form_zero_curvature_potential weight x) := by ring
    _ = weight i + weight j := by rw [hi, hj]

end Omega.SPG
