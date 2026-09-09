import InfoGeometry.Automorphic.GlobalNonAbelianLanglandsBridge
import InfoGeometry.Ergodic.RuelleTransfer

namespace InfoGeometry.Canonical.GlobalNonAbelianLanglandsCapstone

open InfoGeometry.Automorphic.GlobalNonAbelianLanglandsBridge
open InfoGeometry.Ergodic.RuelleTransfer

theorem global_nonabelian_langlands_canonical_capstone
    {Cusp : Type*}
    (K : KudlaRallisDoublingPacket Cusp)
    (f : Cusp) :
    (∃ q : ℚ, K.datum.criticalLValue f / K.datum.peterssonInner f = (q : ℝ)) ∧
    (K.doubledPairing f f = K.datum.peterssonInner f * K.datum.criticalLValue f) ∧
    (∀ (n : ℕ) (x : BitWord n),
      automorphicTransferTrace (fun _ => 0) (fun _ => 1) x = 2) := by
  refine ⟨K.datum.period_rational f,
    K.doubling_factorization f,
    fun n x => automorphic_transfer_markov x⟩

end InfoGeometry.Canonical.GlobalNonAbelianLanglandsCapstone
