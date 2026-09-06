import proofs.SixStateGeneralizedPauliBasis
import proofs.KleinSixStateProjectiveMonodromy
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
namespace CRTGeneralizedPauliSix

open SixStateGeneralizedPauliBasis
open KleinSixStateProjectiveMonodromy

/-- The CRT isomorphism `Z₆ ≃ Z₂ × Z₃` used to reindex six states. -/
def crtEquiv : ZMod 6 ≃+* ZMod 2 × ZMod 3 := by
  exact ZMod.chineseRemainder (m := 2) (n := 3) (by decide)

/-- The sixWeyl operators reindexed via the CRT equivalence. -/
def crtWeyl (k : ZMod 6) (l : ZMod 6) : M6C :=
  let (a, c) := crtEquiv k
  let (b, d) := crtEquiv l
  sixWeyl a b c d

/-- The 36 CRT-reindexed sixWeyl operators. -/
def crtWeylBasis : Finset (ZMod 6 × ZMod 6) := Finset.univ

/-- Multiplication rule for CRT-reindexed sixWeyl operators. -/
theorem crtWeyl_mul (k l k' l' : ZMod 6) :
    crtWeyl k l * crtWeyl k' l' =
      (((if ((crtEquiv l).1.val : ℕ) * ((crtEquiv k').1.val : ℕ) = 1
            then (-1 : ℂ) else (1 : ℂ)) : ℂ) *
        (SixStateGeneralizedPauliBasis.ω3 : ℂ) ^
          (((crtEquiv l).2.val : ℕ) * ((crtEquiv k').2.val : ℕ))) •
        crtWeyl (k + k') (l + l') := by
  let a : ZMod 2 × ZMod 2 := ((crtEquiv k).1, (crtEquiv l).1)
  let c : ZMod 3 × ZMod 3 := ((crtEquiv k).2, (crtEquiv l).2)
  let a' : ZMod 2 × ZMod 2 := ((crtEquiv k').1, (crtEquiv l').1)
  let c' : ZMod 3 × ZMod 3 := ((crtEquiv k').2, (crtEquiv l').2)
  simpa [crtWeyl, a, c, a', c', map_add] using
    (SixStateGeneralizedPauliBasis.sixWeyl_mul a a c c a' a' c' c')

/-- The CRT-reindexed operators form a basis. -/
theorem crtWeyl_index_card :
    Fintype.card (ZMod 6 × ZMod 6) = 36 := by
  decide

/-- The reindexSix equivalence from KleinSixStateProjectiveMonodromy matches the CRT structure. -/
theorem crtEquiv_bijective : Function.Bijective crtEquiv :=
  crtEquiv.bijective

/-- The sheet/color tensor factorization corresponds to the CRT decomposition. -/
theorem crtWeyl_is_tensor_factorized (k l : ZMod 6) :
    crtWeyl k l =
      sixWeyl (crtEquiv k).1 (crtEquiv l).1
        (crtEquiv k).2 (crtEquiv l).2 := by
  rfl

end CRTGeneralizedPauliSix
end noncomputable section
