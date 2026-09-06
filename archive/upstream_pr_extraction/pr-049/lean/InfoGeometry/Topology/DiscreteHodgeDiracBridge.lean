import InfoGeometry.Topology.DiscreteDiracHodgeChiral

namespace InfoGeometry.Topology.DiscreteHodgeDiracBridge

open InfoGeometry.Topology.DiscreteDiracHodgeChiral
open Matrix

noncomputable section

variable {n : ℕ}

/-- Clifford-analysis convention: `∇ = d - δ`. -/
abbrev hodgeDiracOperator (d δ : EndCochain n) :
    Cochains n →ₗ[ℝ] Cochains n :=
  Matrix.toLin' (cliffordDirac d δ)

/-- Monogenic cochains are the kernel of the Clifford Hodge--Dirac operator. -/
abbrev MonogenicFields (d δ : EndCochain n) : Submodule ℝ (Cochains n) :=
  LinearMap.ker (hodgeDiracOperator d δ)

/-- Dirac cochains are the image of the Clifford Hodge--Dirac operator. -/
abbrev ImageHodgeDirac (d δ : EndCochain n) : Submodule ℝ (Cochains n) :=
  LinearMap.range (hodgeDiracOperator d δ)

theorem hodgeDiracOperator_eq_cliffordDirac (d δ : EndCochain n) :
    hodgeDiracOperator d δ = Matrix.toLin' (cliffordDirac d δ) := rfl

theorem cliffordDirac_eq_diracHodge_neg (d δ : EndCochain n) :
    cliffordDirac d δ = diracHodge d (-δ) := by
  ext i j
  simp [cliffordDirac, diracHodge, sub_eq_add_neg]

theorem hodgeDiracOperator_eq_diracHodge_neg (d δ : EndCochain n) :
    hodgeDiracOperator d δ = Matrix.toLin' (diracHodge d (-δ)) := by
  simpa [hodgeDiracOperator] using
    congrArg Matrix.toLin' (cliffordDirac_eq_diracHodge_neg (d := d) (δ := δ))

theorem diracHodge_square (d δ : EndCochain n)
    (hd : d * d = 0) (hδ : δ * δ = 0) :
    diracHodge d δ * diracHodge d δ = hodgeLaplacian d δ :=
  diracHodge_sq_eq_hodgeLaplacian d δ hd hδ

theorem hodgeDiracOperator_square (d δ : EndCochain n)
    (hd : d * d = 0) (hδ : δ * δ = 0) :
    cliffordDirac d δ * cliffordDirac d δ = -hodgeLaplacian d δ :=
  cliffordDirac_sq_eq_neg_hodgeLaplacian d δ hd hδ

theorem monogenic_iff_diracHodgeNegKernel (d δ : EndCochain n) (x : Cochains n) :
    x ∈ MonogenicFields d δ ↔ (diracHodge d (-δ)).mulVec x = 0 := by
  change (Matrix.toLin' (cliffordDirac d δ)) x = 0 ↔ _
  rw [cliffordDirac_eq_diracHodge_neg d δ]
  rfl

theorem monogenic_iff_kernel (d δ : EndCochain n) (x : Cochains n) :
    x ∈ MonogenicFields d δ ↔ (cliffordDirac d δ).mulVec x = 0 := by
  rfl

theorem cliffordHodgeDecomposition
    (d δ : EndCochain n)
    (hCompl : IsCompl (MonogenicFields d δ) (ImageHodgeDirac d δ))
    (hOrthogonal : ∀ {m y}, m ∈ MonogenicFields d δ →
      y ∈ ImageHodgeDirac d δ → dotProduct m y = 0)
    (x : Cochains n) :
    (∃! u : MonogenicFields d δ × ImageHodgeDirac d δ,
      (u.1 : Cochains n) + (u.2 : Cochains n) = x) ∧
      ∀ {m y}, m ∈ MonogenicFields d δ →
        y ∈ ImageHodgeDirac d δ → dotProduct m y = 0 := by
  constructor
  · exact Submodule.existsUnique_add_of_isCompl_prod hCompl x
  · exact hOrthogonal

theorem monogenic_is_laplaceHarmonic
    (d δ : EndCochain n)
    (hd : d * d = 0) (hδ : δ * δ = 0)
    {x : Cochains n} (hx : x ∈ MonogenicFields d δ) :
    IsLaplaceHarmonic d δ x :=
  cliffordMonogenic_is_laplaceHarmonic d δ hd hδ hx

/-! ## Modular conjugation of the two Dirac sectors -/

structure ModularHodgeConjugationData
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V ≃ₗ[ℝ] V
  J_sq : J.trans J = LinearEquiv.refl ℝ V
  d : V →ₗ[ℝ] V
  delta : V →ₗ[ℝ] V
  d_sq : d.comp d = 0
  delta_sq : delta.comp delta = 0
  J_conjugates_d_to_delta :
    J.toLinearMap.comp d = delta.comp J.toLinearMap

namespace ModularHodgeConjugationData

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def diracPlus (H : ModularHodgeConjugationData V) : V →ₗ[ℝ] V := H.d + H.delta

def diracMinus (H : ModularHodgeConjugationData V) : V →ₗ[ℝ] V := H.d - H.delta

theorem J_sq_apply (H : ModularHodgeConjugationData V) (x : V) :
    H.J (H.J x) = x := by
  have h := congrArg (fun e : V ≃ₗ[ℝ] V => e x) H.J_sq
  simpa using h

theorem J_conjugates_d_apply (H : ModularHodgeConjugationData V) (x : V) :
    H.J (H.d x) = H.delta (H.J x) := by
  exact congrArg (fun f : V →ₗ[ℝ] V => f x) H.J_conjugates_d_to_delta

theorem J_conjugates_delta_to_d (H : ModularHodgeConjugationData V) :
    H.J.toLinearMap.comp H.delta = H.d.comp H.J.toLinearMap := by
  ext x
  apply H.J.injective
  calc
    H.J (H.J (H.delta x)) = H.delta x := H.J_sq_apply (H.delta x)
    _ = H.J (H.d (H.J x)) := by
      rw [H.J_conjugates_d_apply, H.J_sq_apply]

theorem J_conjugates_delta_apply (H : ModularHodgeConjugationData V) (x : V) :
    H.J (H.delta x) = H.d (H.J x) := by
  exact congrArg (fun f : V →ₗ[ℝ] V => f x) H.J_conjugates_delta_to_d

theorem J_intertwines_diracPlus (H : ModularHodgeConjugationData V) :
    H.J.toLinearMap.comp (diracPlus H) = (diracPlus H).comp H.J.toLinearMap := by
  ext x
  change H.J (H.d x + H.delta x) = H.d (H.J x) + H.delta (H.J x)
  rw [H.J.map_add, H.J_conjugates_d_apply, H.J_conjugates_delta_apply]
  exact add_comm _ _

theorem J_antiintertwines_diracMinus (H : ModularHodgeConjugationData V) :
    H.J.toLinearMap.comp (diracMinus H) = -(diracMinus H).comp H.J.toLinearMap := by
  ext x
  change H.J (H.d x - H.delta x) = -(H.d (H.J x) - H.delta (H.J x))
  rw [map_sub H.J, H.J_conjugates_d_apply, H.J_conjugates_delta_apply]
  abel

theorem diracPlus_sq (H : ModularHodgeConjugationData V) :
    (diracPlus H).comp (diracPlus H) = H.d.comp H.delta + H.delta.comp H.d := by
  have hd_sq (x : V) : H.d (H.d x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.d_sq
  have hδ_sq (x : V) : H.delta (H.delta x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.delta_sq
  ext x
  change H.d (H.d x + H.delta x) + H.delta (H.d x + H.delta x) =
    H.d (H.delta x) + H.delta (H.d x)
  rw [H.d.map_add, H.delta.map_add, hd_sq, hδ_sq]
  abel

theorem diracMinus_sq (H : ModularHodgeConjugationData V) :
    (diracMinus H).comp (diracMinus H) = -(H.d.comp H.delta + H.delta.comp H.d) := by
  have hd_sq (x : V) : H.d (H.d x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.d_sq
  have hδ_sq (x : V) : H.delta (H.delta x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.delta_sq
  ext x
  change H.d (H.d x - H.delta x) - H.delta (H.d x - H.delta x) =
    -(H.d (H.delta x) + H.delta (H.d x))
  rw [H.d.map_sub, H.delta.map_sub, hd_sq, hδ_sq]
  abel

theorem diracPlus_diracMinus_anticommute (H : ModularHodgeConjugationData V) :
    (diracPlus H).comp (diracMinus H) + (diracMinus H).comp (diracPlus H) = 0 := by
  have hd_sq (x : V) : H.d (H.d x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.d_sq
  have hδ_sq (x : V) : H.delta (H.delta x) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : V →ₗ[ℝ] V => f x) H.delta_sq
  ext x
  change (H.d (H.d x - H.delta x) + H.delta (H.d x - H.delta x)) +
      (H.d (H.d x + H.delta x) - H.delta (H.d x + H.delta x)) = 0
  rw [H.d.map_sub, H.delta.map_sub, H.d.map_add, H.delta.map_add, hd_sq, hδ_sq]
  abel

end ModularHodgeConjugationData

end

end InfoGeometry.Topology.DiscreteHodgeDiracBridge
