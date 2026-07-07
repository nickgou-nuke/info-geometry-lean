/-- 
THE DUAL ENGINE THEOREM (Kähler Compatibility):
The universe uses the real part of the metric (Riemannian, g) to run the 
Radial Engine (descending the thermodynamic gradient to create space). 
Upon reaching the Cramér-Rao bound, it rotates via J, where the metric 
is identical to the Symplectic Rotational Engine (ω).

g(u, v) = ω(u, -Jv)
-/
theorem dual_engine_of_reality (u v : Fin 2 → ℤ) :
  RiemannianMetric u v = SymplecticForm u (mulVec (-ComplexStructure) v) := by
  unfold RiemannianMetric SymplecticForm ComplexStructure dotProduct mulVec
  simp [Fin.sum_univ_two]