This represents the physical observable after projection onto the Drazin support
and the singular defect/harmonic-zero block.
-/
structure DrazinHodgeEnvelope
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  drazin :
    DrazinData Op

  /-- Harmonic/Hodge Drazin data for the background flow L. -/
  hodge :
    DrazinData Op

  x :
    Op

  /-- The physical envelope: x_phys = (1 - LLᴰ)(AAᴰ) x (AAᴰ)(1 - LLᴰ). -/
  x_phys :
    Op

  x_phys_def :
    x_phys = hodge.Q₀ * drazin.P_D * x * drazin.P_D * hodge.Q₀

/--
Fierz–Klein invariants of the Drazin–Hodge envelope.
-/
structure FierzKleinInvariants
    (Op : Type*)
    [Ring Op]
    [Star Op] where

  envelope :
    DrazinHodgeEnvelope Op

  /-- The state used to measure the invariants. -/
  phi :
    InfoGeometry.OperatorAlgebra.OperatorThermodynamics.AlgebraicState Op

  /-- The Fierz channel coefficients C_alpha. -/
  channels :
    ℕ → Op → Op

  /-- The measured coordinates F_alpha. -/
  coords :
    ℕ → ℂ

  coords_def :
    ∀ n : ℕ, coords n = phi.eval (channels n envelope.x_phys)

/--
The square of the Drazin supercharge decomposes into kinetic and defect
shadows when a split witness is supplied.
-/
theorem drazin_supercharge_square_split
    {Op : Type*}
    [Ring Op]
    [Star Op]
    [SMul ℝ Op]
    (S : DrazinKineticDefectSplit Op) :
    S.supercharge.Q_alg * S.supercharge.Q_alg =
      S.T_D + (0.5 : ℝ) • S.Z_D :=
  S.split_True

/--
If the Moore--Penrose range and domain supports agree, the dilation gap
vanishes.
-/
theorem dilation_gap_zero_of_supports_equal
    {Op : Type*}
    [Ring Op]
    [Star Op]
    [SMul ℝ Op]
    (G : DilationGapData Op)
    (h : G.mp.P_range = G.mp.P_domain)
    (hzero : G.halfScalar • (0 : Op) = 0) :
    G.G = 0 := by
  rw [G.G_def, h]
  simp only [sub_self]
  exact hzero

/--
If two self-adjoint operators generate a commutator, that commutator is
skew-adjoint.
-/
theorem star_commutator_eq_neg_of_self_adjoint
    {Op : Type*} [Ring Op] [StarRing Op] {P G : Op}
    (hP : star P = P) (hG : star G = G) :
    star (commutator P G) = -commutator P G := by
  simp [commutator, hP, hG]

end InfoGeometry.Canonical.DrazinDilationGap

namespace InfoGeometry.Canonical.DrazinDilationGap

/-- Export alias for the Drazin defect support readback. -/
theorem defectSupport_eq_one_sub_regularSupport
    {Op : Type*} [Ring Op] [Star Op] (D : DrazinData Op) :
    D.Q₀ = 1 - D.P_D :=
  DrazinData.defectSupport_eq_one_sub_regularSupport D