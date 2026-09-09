import InfoGeometry.Canonical.CantorCylinderChiral

namespace InfoGeometry.Canonical.CantorCylinderChiralCapstone

open InfoGeometry.Canonical.CantorCylinderChiral

theorem capstone_cantor_cylinder_chiral_synthesis
    {R : Type*} [CommRing R]
    (a : ChiralArrow) (past future : ℕ → Bool) (n : ℕ)
    (w : BitWord n) (C : ChiralCuntzPair R) (N_L N_R : ℝ) (h_bal : N_L = N_R)
    (σ : ℝ) (h_crit : σ - 1 / 2 = 0) :
    (chirality (chiralConj a) = -chirality a) ∧
    (PastCone (BiInfinitePathMk past future) n = past n) ∧
    (FutureCone (BiInfinitePathMk past future) n = future n) ∧
    (chiralBranchTruncate (chiralBranchPrefix a w) = w) ∧
    (C.S_L_star * C.S_L = 1 ∧ C.S_R_star * C.S_R = 1 ∧ C.S_L_star * C.S_R = 0) ∧
    (chiralKMSWeight ChiralArrow.L n ≠ chiralKMSWeight ChiralArrow.R n) ∧
    (chiralRapidity N_L N_R = 0) ∧
    (σ = 1 / 2) := by
  exact ⟨chirality_conj a,
    pastCone_BiInfinitePathMk past future n,
    futureCone_BiInfinitePathMk past future n,
    chiralBranch_truncate_prefix a w,
    ⟨C.isometry_L, C.isometry_R, C.orthogonal_LR⟩,
    chiralKMS_asymmetry n,
    chiral_rapidity_balance N_L N_R h_bal,
    critical_line_from_chiral_balance σ h_crit⟩

end InfoGeometry.Canonical.CantorCylinderChiralCapstone
