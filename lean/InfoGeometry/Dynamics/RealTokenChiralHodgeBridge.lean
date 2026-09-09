import InfoGeometry.Dynamics.RealTokenKreinTrialityBridge

/-!
# Hodge--Dirac bridge for the doubled real token carrier

This file is deliberately witness-gated.  The doubled carrier supplies the
real split/Krein coordinates, but it does not canonically determine an
exterior differential or a Hodge involution.  Given continuous witnesses for
those operators, the existing generic Hodge owner supplies the Dirac and
Laplacian theorems.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealTokenDoubledOperator :=
  RealTokenDoubledSpace (V := V) →ₗ[ℝ] RealTokenDoubledSpace (V := V)

structure RealTokenChiralHodgeWitness where
  J : RealTokenDoubledOperator (V := V)
  Gamma : RealTokenDoubledOperator (V := V)
  d : RealTokenDoubledOperator (V := V)
  J_sq : J.comp J = LinearMap.id
  Gamma_sq : Gamma.comp Gamma = LinearMap.id
  J_Gamma_anticomm : J.comp Gamma = -(Gamma.comp J)
  d_sq : d.comp d = 0
  d_odd : Gamma.comp d = -(d.comp Gamma)
  delta : RealTokenDoubledOperator (V := V)
  delta_sq : delta.comp delta = 0
  delta_odd : Gamma.comp delta = -(delta.comp Gamma)

def RealTokenChiralHodgeWitness.hodgeDirac
    (W : RealTokenChiralHodgeWitness (V := V)) : RealTokenDoubledOperator (V := V) :=
  W.d + W.delta

def RealTokenChiralHodgeWitness.hodgeLaplacian
    (W : RealTokenChiralHodgeWitness (V := V)) : RealTokenDoubledOperator (V := V) :=
  W.d.comp W.delta + W.delta.comp W.d

theorem realTokenChiralHodge_hodgeDirac_sq
    (W : RealTokenChiralHodgeWitness (V := V)) :
    (W.hodgeDirac.comp W.hodgeDirac) = W.hodgeLaplacian := by
  dsimp [RealTokenChiralHodgeWitness.hodgeDirac,
    RealTokenChiralHodgeWitness.hodgeLaplacian]
  calc
    (W.d + W.delta).comp (W.d + W.delta) =
        W.d.comp W.d + W.d.comp W.delta + W.delta.comp W.d + W.delta.comp W.delta := by
          rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
          module
    _ = W.d.comp W.delta + W.delta.comp W.d := by
      rw [W.d_sq, W.delta_sq]
      simp

theorem realTokenChiralHodge_hodgeDirac_odd
    (W : RealTokenChiralHodgeWitness (V := V)) :
    W.Gamma.comp W.hodgeDirac =
      -(W.hodgeDirac.comp W.Gamma) := by
  dsimp [RealTokenChiralHodgeWitness.hodgeDirac]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply]
  have hd := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) W.d_odd
  have hdelta := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x)
    W.delta_odd
  have hd' : W.Gamma (W.d x) = -(W.d (W.Gamma x)) := by
    simpa [LinearMap.comp_apply] using hd
  have hdelta' : W.Gamma (W.delta x) = -(W.delta (W.Gamma x)) := by
    simpa [LinearMap.comp_apply] using hdelta
  change W.Gamma (W.d x + W.delta x) =
    -(W.d (W.Gamma x) + W.delta (W.Gamma x))
  rw [map_add, hd', hdelta']
  module

theorem realTokenChiralHodge_gamma_preserves_dirac_kernel
    (W : RealTokenChiralHodgeWitness (V := V))
    {x : RealTokenDoubledSpace (V := V)}
    (hx : W.hodgeDirac x = 0) :
    W.hodgeDirac (W.Gamma x) = 0 := by
  have hodd := realTokenChiralHodge_hodgeDirac_odd W
  have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) hodd
  have h' : W.Gamma (W.hodgeDirac x) =
      -W.hodgeDirac (W.Gamma x) := by
    simpa [LinearMap.comp_apply] using h
  rw [← neg_eq_zero, ← h', hx]
  simp

theorem realTokenChiralHodge_dirac_range_gamma_eq
    (W : RealTokenChiralHodgeWitness (V := V)) :
    LinearMap.range (W.hodgeDirac.comp W.Gamma) =
      LinearMap.range W.hodgeDirac := by
  apply le_antisymm
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨W.Gamma x, ?_⟩
    have hodd := realTokenChiralHodge_hodgeDirac_odd W
    have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) hodd
    simpa [LinearMap.comp_apply] using h.symm
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨W.Gamma x, ?_⟩
    have hgamma : W.Gamma (W.Gamma x) = x := by
      have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x)
        W.Gamma_sq
      simpa [LinearMap.comp_apply] using h
    have hodd := realTokenChiralHodge_hodgeDirac_odd W
    have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T (W.Gamma x)) hodd
    rw [LinearMap.comp_apply, hgamma]

/-! The square of an odd operator is even.  This is the precise algebraic
    invariant available before choosing a Hilbert or Krein adjoint. -/

theorem realTokenChiralHodge_hodgeLaplacian_even
    (W : RealTokenChiralHodgeWitness (V := V)) :
    W.Gamma.comp W.hodgeLaplacian =
      W.hodgeLaplacian.comp W.Gamma := by
  have hodd := realTokenChiralHodge_hodgeDirac_odd W
  rw [← realTokenChiralHodge_hodgeDirac_sq W]
  apply LinearMap.ext
  intro x
  have h_at_dirac := congrArg
    (fun T : RealTokenDoubledOperator (V := V) => T (W.hodgeDirac x)) hodd
  have h_at_x := congrArg
    (fun T : RealTokenDoubledOperator (V := V) => T x) hodd
  change W.Gamma (W.hodgeDirac (W.hodgeDirac x)) =
    W.hodgeDirac (W.hodgeDirac (W.Gamma x))
  calc
    W.Gamma (W.hodgeDirac (W.hodgeDirac x)) =
        -W.hodgeDirac (W.Gamma (W.hodgeDirac x)) := by
          simpa [LinearMap.comp_apply] using h_at_dirac
    _ = -W.hodgeDirac (-W.hodgeDirac (W.Gamma x)) := by
          rw [show W.Gamma (W.hodgeDirac x) =
            -W.hodgeDirac (W.Gamma x) by
            simpa [LinearMap.comp_apply] using h_at_x]
    _ = W.hodgeDirac (W.hodgeDirac (W.Gamma x)) := by simp

theorem realTokenChiralHodge_gamma_preserves_harmonic
    (W : RealTokenChiralHodgeWitness (V := V))
    {x : RealTokenDoubledSpace (V := V)}
    (hx : W.hodgeLaplacian x = 0) :
    W.hodgeLaplacian (W.Gamma x) = 0 := by
  have h_even := realTokenChiralHodge_hodgeLaplacian_even W
  have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) h_even
  have h' : W.Gamma (W.hodgeLaplacian x) =
      W.hodgeLaplacian (W.Gamma x) := by
    simpa [LinearMap.comp_apply] using h
  rw [← h', hx, map_zero]

theorem realTokenChiralHodge_gamma_preserves_laplacian_range
    (W : RealTokenChiralHodgeWitness (V := V))
    {x : RealTokenDoubledSpace (V := V)} :
    x ∈ LinearMap.range W.hodgeLaplacian →
      W.Gamma x ∈ LinearMap.range W.hodgeLaplacian := by
  intro hx
  rcases hx with ⟨y, hy⟩
  refine ⟨W.Gamma y, ?_⟩
  have h_even := realTokenChiralHodge_hodgeLaplacian_even W
  have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T y) h_even
  rw [← hy]
  simpa [LinearMap.comp_apply] using h.symm

theorem realTokenChiralHodge_laplacian_range_gamma_eq
    (W : RealTokenChiralHodgeWitness (V := V)) :
    LinearMap.range (W.hodgeLaplacian.comp W.Gamma) =
      LinearMap.range W.hodgeLaplacian := by
  apply le_antisymm
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨W.Gamma x, ?_⟩
    have h_even := realTokenChiralHodge_hodgeLaplacian_even W
    have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) h_even
    simpa [LinearMap.comp_apply] using h.symm
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    have hGamma : W.Gamma (W.Gamma x) = x := by
      have h := congrArg (fun T : RealTokenDoubledOperator (V := V) => T x) W.Gamma_sq
      simpa [LinearMap.comp_apply] using h
    refine ⟨W.Gamma x, ?_⟩
    rw [LinearMap.comp_apply]
    rw [hGamma]


end
end InfoGeometry.Dynamics
