
/--
The structural Lie bracket identity between two bivectors.
This governs the Wigner-Inönü contractions natively.
For example, $[e_i e_j, e_j e_k] = \kappa_j e_i e_k$.
-/
theorem kinematicBivector_bracket_identity (i j k : Fin n) 
  (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
  ⁅kinematicBivector kappa i j, kinematicBivector kappa j k⁆ = 
    2 * kappa j • kinematicBivector kappa i k := by
  sorry

end InfoGeometry.Algebra

The above content does NOT show the entire file contents. If you need to view any lines of the file which were not shown to complete your task, call this tool again to view those lines.