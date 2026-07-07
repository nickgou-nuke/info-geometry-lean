/-- THEOREM: Equivalence of Torsion-Free states.
    If the full spin connection is equal to the Levi-Civita connection, 
    the contorsion tensor must be identically zero. -/
theorem torsion_free_contorsion {S : Type*} [AddCommGroup S] [Module ℝ S] (spin_conn : SpinConnection S) 
    (h_torsion_free : modified_spin_connection spin_conn = spin_conn.omega_LC) :
    spin_conn.K = 0