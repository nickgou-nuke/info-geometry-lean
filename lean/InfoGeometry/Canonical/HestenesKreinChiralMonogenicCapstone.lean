import InfoGeometry.Canonical.HestenesKreinChiralMonogenicBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.HestenesKreinChiralMonogenicCapstone

open InfoGeometry.Canonical.HestenesChiral

theorem hestenes_krein_chiral_canonical_capstone
    (ψ : Multivector2D) (cell : MonogenicHodgeCell) :
    (EvenMultivector.I * EvenMultivector.I = ⟨-1, 0⟩) ∧
    (Multivector2D.chiralLeft ψ + Multivector2D.chiralRight ψ = ψ) ∧
    (Multivector2D.pseudoscalarSandwich (Multivector2D.chiralLeft ψ) =
      Multivector2D.chiralLeft ψ) ∧
    (Multivector2D.pseudoscalarSandwich (Multivector2D.chiralRight ψ) =
      ⟨-ψ.scalar, 0, 0, -ψ.bivector⟩) ∧
    (cell.laplacian_u = 0) := by
  exact ⟨EvenMultivector.I_sq,
    Multivector2D.chiral_decomposition_complete ψ,
    Multivector2D.chiralLeft_sandwich ψ,
    Multivector2D.chiralRight_sandwich ψ,
    monogenic_cell_harmonic cell⟩

end InfoGeometry.Canonical.HestenesKreinChiralMonogenicCapstone
