import InfoGeometry.Topology.DiscreteDiracHodgeChiral

/-!
  A theorem-safe finite Hodge-decomposition contract.

  The existence of a decomposition is supplied as finite algebraic data; this
  file does not claim an analytic orthogonal-projection theorem.  The
  previously existing owner used undeclared cochain types and `sorry` proofs,
  so the API is intentionally reduced to the explicit matrix-level contract.
-/

namespace InfoGeometry.Topology.HodgeDecomposition

open InfoGeometry.Topology.DiscreteDiracHodgeChiral

noncomputable section

structure Witness {n : ℕ} (d δ : EndCochain n) (x : Cochains n) where
  exactPart : Cochains n
  coexactPart : Cochains n
  harmonicPart : Cochains n
  decomposition :
    x = d.mulVec exactPart + δ.mulVec coexactPart + harmonicPart
  harmonic :
    (hodgeLaplacian d δ).mulVec harmonicPart = 0

def IsHodgeDecomposition {n : ℕ}
    (d δ : EndCochain n) (x : Cochains n) : Prop :=
  Nonempty (Witness d δ x)

theorem decomposition_readout {n : ℕ}
    (d δ : EndCochain n) (x : Cochains n)
    (w : Witness d δ x) :
    x = d.mulVec w.exactPart + δ.mulVec w.coexactPart + w.harmonicPart ∧
      (hodgeLaplacian d δ).mulVec w.harmonicPart = 0 :=
  ⟨w.decomposition, w.harmonic⟩

theorem decomposition_exists_of_witness {n : ℕ}
    (d δ : EndCochain n) (x : Cochains n)
    (w : Witness d δ x) :
    IsHodgeDecomposition d δ x :=
  ⟨w⟩

theorem exact_closed_of_nilpotent {n : ℕ}
    (d : EndCochain n) (hd : d * d = 0)
    {x : Cochains n} (hx : ∃ y, d.mulVec y = x) :
    d.mulVec x = 0 := by
  rcases hx with ⟨y, rfl⟩
  have h := congrArg (fun M => M.mulVec y) hd
  simpa [Matrix.mulVec_mulVec] using h

theorem coexact_coclosed_of_nilpotent {n : ℕ}
    (δ : EndCochain n) (hδ : δ * δ = 0)
    {x : Cochains n} (hx : ∃ y, δ.mulVec y = x) :
    δ.mulVec x = 0 := by
  rcases hx with ⟨y, rfl⟩
  have h := congrArg (fun M => M.mulVec y) hδ
  simpa [Matrix.mulVec_mulVec] using h

end

end InfoGeometry.Topology.HodgeDecomposition
