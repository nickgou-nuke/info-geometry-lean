import InfoGeometry.Canonical.HestenesRealMirror
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V]

theorem continuous_doubledSheetExchange :
    Continuous (doubledSheetExchange (V := V)) := by
  exact continuous_snd.prodMk continuous_fst

def doubledSheetExchangeHomeomorph :
    (V × V) ≃ₜ (V × V) :=
  { toFun := doubledSheetExchange
    invFun := doubledSheetExchange
    left_inv := by
      intro p
      rfl
    right_inv := by
      intro p
      rfl
    continuous_toFun := continuous_doubledSheetExchange
    continuous_invFun := continuous_doubledSheetExchange }

@[simp] theorem doubledSheetExchangeHomeomorph_apply (p : V × V) :
    doubledSheetExchangeHomeomorph (V := V) p = (p.2, p.1) := rfl

@[simp] theorem doubledSheetExchangeHomeomorph_symm_apply (p : V × V) :
    (doubledSheetExchangeHomeomorph (V := V)).symm p = (p.2, p.1) := rfl

def realMirrorHomeomorph
    (J : V ≃ₗ[ℝ] V) (hJ : IsRealMirror J)
    (hJ_cont : Continuous J) : V ≃ₜ V :=
  { toFun := J
    invFun := J
    left_inv := by
      intro v
      exact realMirror_is_involutive J hJ v
    right_inv := by
      intro v
      exact realMirror_is_involutive J hJ v
    continuous_toFun := hJ_cont
    continuous_invFun := hJ_cont }

@[simp] theorem realMirrorHomeomorph_apply
    (J : V ≃ₗ[ℝ] V) (hJ : IsRealMirror J)
    (hJ_cont : Continuous J) (v : V) :
    realMirrorHomeomorph J hJ hJ_cont v = J v := rfl

@[simp] theorem realMirrorHomeomorph_symm_apply
    (J : V ≃ₗ[ℝ] V) (hJ : IsRealMirror J)
    (hJ_cont : Continuous J) (v : V) :
    (realMirrorHomeomorph J hJ hJ_cont).symm v = J v := rfl

theorem realMirrorHomeomorph_trans_self
    (J : V ≃ₗ[ℝ] V) (hJ : IsRealMirror J)
    (hJ_cont : Continuous J) :
    (realMirrorHomeomorph J hJ hJ_cont).trans
        (realMirrorHomeomorph J hJ hJ_cont) = Homeomorph.refl V := by
  ext v
  exact realMirror_is_involutive J hJ v

end

end InfoGeometry.Canonical
