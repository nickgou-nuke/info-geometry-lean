import proofs.HestenesBivectorCarrier

/-!
# An explicit basis of spacetime bivectors

The three relative boosts `σₖ` and their three pseudoscalar multiples
`Ω₄ σₖ` form the real six-element basis of the exact bivector carrier.
-/

noncomputable section
namespace HestenesBivectorBasis

open HestenesCl14 HestenesCliffordCenter HestenesEvenPauliEquiv HestenesKreinMatrixBridge
open HestenesHodgeParityBridge
open HestenesBivectorCarrier
open HestenesPauliSheetBridge
open HestenesCliffordCenter

abbrev Algebra := Cl14
abbrev EvenPart := ClPlus14

def rawBivector : Fin 6 → EvenPart
  | 0 => sigmaEven 0
  | 1 => sigmaEven 1
  | 2 => sigmaEven 2
  | 3 => volumeEven * sigmaEven 0
  | 4 => volumeEven * sigmaEven 1
  | 5 => volumeEven * sigmaEven 2

@[simp] theorem reverse_sigmaEven (k : Fin 3) :
    CliffordAlgebra.reverse ((sigmaEven k : EvenPart) : Algebra) =
      -(sigmaEven k : Algebra) := by
  fin_cases k
  · change CliffordAlgebra.reverse (gamma 1 * gamma 0) = -(gamma 1 * gamma 0)
    rw [CliffordAlgebra.reverse.map_mul]
    simp only [gamma, CliffordAlgebra.reverse_ι]
    exact eq_neg_of_add_eq_zero_left
      (gamma_anticomm (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide))
  · change CliffordAlgebra.reverse (gamma 2 * gamma 0) = -(gamma 2 * gamma 0)
    rw [CliffordAlgebra.reverse.map_mul]
    simp only [gamma, CliffordAlgebra.reverse_ι]
    exact eq_neg_of_add_eq_zero_left
      (gamma_anticomm (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide))
  · change CliffordAlgebra.reverse (gamma 3 * gamma 0) = -(gamma 3 * gamma 0)
    rw [CliffordAlgebra.reverse.map_mul]
    simp only [gamma, CliffordAlgebra.reverse_ι]
    exact eq_neg_of_add_eq_zero_left
      (gamma_anticomm (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide))

@[simp] theorem reverse_volumeEven :
    CliffordAlgebra.reverse ((volumeEven : EvenPart) : Algebra) =
      (volumeEven : Algebra) := by
  rw [← spacetimePseudoscalar_eq_volumeEven]
  exact reverse_spacetimePseudoscalar

theorem reverse_rawBivector (i : Fin 6) :
    CliffordAlgebra.reverse ((rawBivector i : EvenPart) : Algebra) =
      -(rawBivector i : Algebra) := by
  fin_cases i
  · exact reverse_sigmaEven 0
  · exact reverse_sigmaEven 1
  · exact reverse_sigmaEven 2
  · change CliffordAlgebra.reverse
      ((volumeEven : Algebra) * (sigmaEven 0 : Algebra)) =
        -((volumeEven : Algebra) * (sigmaEven 0 : Algebra))
    rw [CliffordAlgebra.reverse.map_mul,
      reverse_sigmaEven, reverse_volumeEven]
    rw [← spacetimePseudoscalar_eq_volumeEven]
    simpa [neg_mul] using congrArg Neg.neg
      ((spacetimePseudoscalar_comm_even (sigmaEven 0).property).symm)
  · change CliffordAlgebra.reverse
      ((volumeEven : Algebra) * (sigmaEven 1 : Algebra)) =
        -((volumeEven : Algebra) * (sigmaEven 1 : Algebra))
    rw [CliffordAlgebra.reverse.map_mul,
      reverse_sigmaEven, reverse_volumeEven]
    rw [← spacetimePseudoscalar_eq_volumeEven]
    simpa [neg_mul] using congrArg Neg.neg
      ((spacetimePseudoscalar_comm_even (sigmaEven 1).property).symm)
  · change CliffordAlgebra.reverse
      ((volumeEven : Algebra) * (sigmaEven 2 : Algebra)) =
        -((volumeEven : Algebra) * (sigmaEven 2 : Algebra))
    rw [CliffordAlgebra.reverse.map_mul,
      reverse_sigmaEven, reverse_volumeEven]
    rw [← spacetimePseudoscalar_eq_volumeEven]
    simpa [neg_mul] using congrArg Neg.neg
      ((spacetimePseudoscalar_comm_even (sigmaEven 2).property).symm)

def basisBivector (i : Fin 6) : Bivector :=
  ⟨rawBivector i, (rawBivector i).property, reverse_rawBivector i⟩

@[simp] theorem basisBivector_val (i : Fin 6) :
    ((basisBivector i : Bivector) : Algebra) = rawBivector i := rfl

/-! The explicit Lorentzian Hodge table in the chosen six-element basis. -/

@[simp] theorem hodge_basis_0 :
    hodgeBivector (basisBivector 0) = -basisBivector 3 := by
  apply Subtype.ext
  change hodge (rawBivector 0 : Algebra) = -(rawBivector 3 : Algebra)
  calc
    hodge (rawBivector 0 : Algebra) =
        -(rawBivector 0 : Algebra) * spacetimePseudoscalar := by
      rw [hodge, reverse_rawBivector]
    _ = -((spacetimePseudoscalar : Algebra) * rawBivector 0) := by
      rw [spacetimePseudoscalar_comm_even (rawBivector 0).property]
      simp [neg_mul]
    _ = -(rawBivector 3 : Algebra) := by
      rw [spacetimePseudoscalar_eq_volumeEven]
      rfl

@[simp] theorem hodge_basis_1 :
    hodgeBivector (basisBivector 1) = -basisBivector 4 := by
  apply Subtype.ext
  change hodge (rawBivector 1 : Algebra) = -(rawBivector 4 : Algebra)
  calc
    hodge (rawBivector 1 : Algebra) =
        -(rawBivector 1 : Algebra) * spacetimePseudoscalar := by
      rw [hodge, reverse_rawBivector]
    _ = -((spacetimePseudoscalar : Algebra) * rawBivector 1) := by
      rw [spacetimePseudoscalar_comm_even (rawBivector 1).property]
      simp [neg_mul]
    _ = -(rawBivector 4 : Algebra) := by
      rw [spacetimePseudoscalar_eq_volumeEven]
      rfl

@[simp] theorem hodge_basis_2 :
    hodgeBivector (basisBivector 2) = -basisBivector 5 := by
  apply Subtype.ext
  change hodge (rawBivector 2 : Algebra) = -(rawBivector 5 : Algebra)
  calc
    hodge (rawBivector 2 : Algebra) =
        -(rawBivector 2 : Algebra) * spacetimePseudoscalar := by
      rw [hodge, reverse_rawBivector]
    _ = -((spacetimePseudoscalar : Algebra) * rawBivector 2) := by
      rw [spacetimePseudoscalar_comm_even (rawBivector 2).property]
      simp [neg_mul]
    _ = -(rawBivector 5 : Algebra) := by
      rw [spacetimePseudoscalar_eq_volumeEven]
      rfl

@[simp] theorem hodge_basis_3 :
    hodgeBivector (basisBivector 3) = basisBivector 0 := by
  simpa using hodge_sq_bivector (basisBivector 0)

@[simp] theorem hodge_basis_4 :
    hodgeBivector (basisBivector 4) = basisBivector 1 := by
  simpa using hodge_sq_bivector (basisBivector 1)

@[simp] theorem hodge_basis_5 :
    hodgeBivector (basisBivector 5) = basisBivector 2 := by
  simpa using hodge_sq_bivector (basisBivector 2)

theorem rawBivector_linearIndependent :
    LinearIndependent ℝ rawBivector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hm : ∑ j, g j • clPlusToPauli (rawBivector j) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using
      congrArg clPlusToPauli hg
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp [Fin.sum_univ_six, rawBivector, pauli1, pauli2, pauli3]
    at h00 h01 h10
  have h00re := congrArg Complex.re h00
  have h00im := congrArg Complex.im h00
  have h01re := congrArg Complex.re h01
  have h01im := congrArg Complex.im h01
  have h10re := congrArg Complex.re h10
  have h10im := congrArg Complex.im h10
  norm_num at h00re h00im h01re h01im h10re h10im
  fin_cases i
  · change g 0 = 0; linarith
  · change g 1 = 0; linarith
  · change g 2 = 0; exact h00re
  · change g 3 = 0; linarith
  · change g 4 = 0; linarith
  · change g 5 = 0; exact h00im

theorem basisBivector_linearIndependent :
    LinearIndependent ℝ basisBivector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hraw : ∑ j, g j • rawBivector j = 0 := by
    apply Subtype.ext
    simpa [basisBivector] using
      congrArg (fun z : Bivector => (z : Algebra)) hg
  apply (Fintype.linearIndependent_iff.mp rawBivector_linearIndependent g)
  exact hraw

def scalarPseudoscalar : Fin 2 → EvenPart
  | 0 => 1
  | 1 => volumeEven

theorem scalarPseudoscalar_linearIndependent :
    LinearIndependent ℝ scalarPseudoscalar := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hm : ∑ j, g j • clPlusToPauli (scalarPseudoscalar j) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using
      congrArg clPlusToPauli hg
  have h00 := congrFun (congrFun hm 0) 0
  simp [Fin.sum_univ_two, scalarPseudoscalar] at h00
  fin_cases i
  · simpa using congrArg Complex.re h00
  · simpa using congrArg Complex.im h00

def scalarPseudoscalarAlg (i : Fin 2) : Algebra := scalarPseudoscalar i

def scalarPseudoscalarSubmodule : Submodule ℝ Algebra :=
  Submodule.span ℝ (Set.range scalarPseudoscalarAlg)

theorem reverse_eq_self_of_mem_scalarPseudoscalar
    {x : Algebra} (hx : x ∈ scalarPseudoscalarSubmodule) :
    CliffordAlgebra.reverse x = x := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [scalarPseudoscalarAlg, scalarPseudoscalar]
  · simp
  · intro x y _ _ hx hy
    simpa using congrArg₂ (· + ·) hx hy
  · intro r x _ hx
    simpa using congrArg (r • ·) hx

theorem bivector_disjoint_scalarPseudoscalar :
    Disjoint Bivector13 scalarPseudoscalarSubmodule := by
  rw [Submodule.disjoint_def]
  intro x hxB hxS
  have hfix := reverse_eq_self_of_mem_scalarPseudoscalar hxS
  have hneg := hxB.2
  rw [hfix] at hneg
  have hxadd : x + x = 0 := eq_neg_iff_add_eq_zero.mp hneg
  have hs : (2 : ℝ) • x = 0 := by simpa [two_smul] using hxadd
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

theorem finrank_scalarPseudoscalarSubmodule :
    Module.finrank ℝ scalarPseudoscalarSubmodule = 2 := by
  have hli : LinearIndependent ℝ scalarPseudoscalarAlg := by
    simpa [scalarPseudoscalarAlg] using
      scalarPseudoscalar_linearIndependent.map'
        (Submodule.subtype (CliffordAlgebra.evenOdd Q14 0))
        (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  let b := Module.Basis.span hli
  exact Module.finrank_eq_card_basis b

theorem finrank_bivector_le_six : Module.finrank ℝ Bivector13 ≤ 6 := by
  have hsup : Bivector13 ⊔ scalarPseudoscalarSubmodule ≤
      CliffordAlgebra.evenOdd Q14 0 := by
    apply sup_le
    · intro x hx
      exact hx.1
    · apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      exact (scalarPseudoscalar i).property
  have hamb : Module.finrank ℝ ↥(Bivector13 ⊔ scalarPseudoscalarSubmodule) ≤ 8 := by
    calc
      Module.finrank ℝ ↥(Bivector13 ⊔ scalarPseudoscalarSubmodule) ≤
          Module.finrank ℝ ↥(CliffordAlgebra.evenOdd Q14 0) :=
        Submodule.finrank_mono hsup
      _ = 8 := clPlus14_finrank
  have heq := Submodule.finrank_sup_add_finrank_inf_eq
    Bivector13 scalarPseudoscalarSubmodule
  rw [bivector_disjoint_scalarPseudoscalar.eq_bot] at heq
  simp [finrank_scalarPseudoscalarSubmodule] at heq
  rw [heq] at hamb
  omega

theorem finrank_bivector_ge_six : 6 ≤ Module.finrank ℝ Bivector13 := by
  simpa using basisBivector_linearIndependent.fintype_card_le_finrank

@[simp] theorem finrank_bivector13 : Module.finrank ℝ Bivector13 = 6 :=
  le_antisymm finrank_bivector_le_six finrank_bivector_ge_six

def bivectorBasis : Module.Basis (Fin 6) ℝ Bivector13 :=
  Module.Basis.mk basisBivector_linearIndependent <| by
    rw [basisBivector_linearIndependent.span_eq_top_of_card_eq_finrank]
    simp [finrank_bivector13]

@[simp] theorem bivectorBasis_apply (i : Fin 6) :
    bivectorBasis i = basisBivector i := by
  simp [bivectorBasis]

theorem bivector_basis_packet :
    LinearIndependent ℝ basisBivector ∧
      Module.finrank ℝ Bivector13 = 6 :=
  ⟨basisBivector_linearIndependent, finrank_bivector13⟩

end HestenesBivectorBasis
end noncomputable section
