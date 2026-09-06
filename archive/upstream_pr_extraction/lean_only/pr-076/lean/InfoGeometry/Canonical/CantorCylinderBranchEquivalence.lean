import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# Binary branch decomposition of finite cylinder observables

The two branch pullbacks jointly recover, and independently prescribe, every
finite diagonal observable.  This is the observable-side counterpart of
`bitWordSuccEquiv`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzCantorBoundaryShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- Restriction to the false and true finite branches. -/
noncomputable def branchPullbackPairEquiv (n : ℕ) :
    DiagAlg (n + 1) ≃ (DiagAlg n × DiagAlg n) :=
  Equiv.ofBijective
    (fun f => (branchPullback n false f, branchPullback n true f))
    ⟨branchPullback_pair_injective n, branchPullback_pair_surjective n⟩

@[simp]
theorem branchPullbackPairEquiv_apply (n : ℕ) (f : DiagAlg (n + 1)) :
    branchPullbackPairEquiv n f =
      (branchPullback n false f, branchPullback n true f) :=
  rfl

@[simp]
theorem branchPullbackPairEquiv_symm_fst (n : ℕ)
    (p : DiagAlg n × DiagAlg n) :
    branchPullback n false ((branchPullbackPairEquiv n).symm p) = p.1 := by
  exact congrArg Prod.fst ((branchPullbackPairEquiv n).apply_symm_apply p)

@[simp]
theorem branchPullbackPairEquiv_symm_snd (n : ℕ)
    (p : DiagAlg n × DiagAlg n) :
    branchPullback n true ((branchPullbackPairEquiv n).symm p) = p.2 := by
  exact congrArg Prod.snd ((branchPullbackPairEquiv n).apply_symm_apply p)

end InfoGeometry.Canonical.CuntzCantorBoundaryShift
