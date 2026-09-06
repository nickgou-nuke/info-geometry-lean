import InfoGeometry.Topology.SymbolicLatentPathConcatenationHomotopy
import InfoGeometry.Topology.SymbolicLatentPathReparametrization
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient

namespace InfoGeometry.Topology

/-!
# Reparametrization invariance of canonical concatenation

The canonical midpoint concatenation is unchanged at homotopy-class level if
either component is replaced by an endpoint-preserving reparametrization.
-/

theorem reparametrized_finish_eq
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    (reparametrizeSymbolicLatentPath R γ).finish = γ.finish := by
  change γ (R.parameter 1) = γ 1
  rw [R.at_one]

theorem reparametrized_start_eq
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    (reparametrizeSymbolicLatentPath R γ).start = γ.start := by
  change γ (R.parameter 0) = γ 0
  rw [R.at_zero]

theorem canonicalSymbolicConcatenation_reparametrization_homotopic
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (R₀ R₁ : SymbolicLatentPathReparametrization)
    (hend : γ₀.finish = γ₁.start) :
    SymbolicLatentPathHomotopic
      (canonicalSymbolicConcatenation hend)
      (canonicalSymbolicConcatenation (by
        calc
          (reparametrizeSymbolicLatentPath R₀ γ₀).finish = γ₀.finish :=
            reparametrized_finish_eq R₀ γ₀
          _ = γ₁.start := hend
          _ = (reparametrizeSymbolicLatentPath R₁ γ₁).start :=
            (reparametrized_start_eq R₁ γ₁).symm)) := by
  let hend' :
      (reparametrizeSymbolicLatentPath R₀ γ₀).finish =
        (reparametrizeSymbolicLatentPath R₁ γ₁).start := by
    calc
      (reparametrizeSymbolicLatentPath R₀ γ₀).finish = γ₀.finish :=
        reparametrized_finish_eq R₀ γ₀
      _ = γ₁.start := hend
      _ = (reparametrizeSymbolicLatentPath R₁ γ₁).start :=
        (reparametrized_start_eq R₁ γ₁).symm
  exact concatenatedSymbolicPathHomotopic_of_homotopies
    hend hend'
    (reparametrizeSymbolicLatentPath_homotopic R₀ γ₀).some
    (reparametrizeSymbolicLatentPath_homotopic R₁ γ₁).some

theorem canonicalSymbolicConcatenation_reparametrization_quotient_eq
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (R₀ R₁ : SymbolicLatentPathReparametrization)
    (hend : γ₀.finish = γ₁.start) :
    symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation hend) =
      symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation (by
          calc
            (reparametrizeSymbolicLatentPath R₀ γ₀).finish = γ₀.finish :=
              reparametrized_finish_eq R₀ γ₀
            _ = γ₁.start := hend
            _ = (reparametrizeSymbolicLatentPath R₁ γ₁).start :=
              (reparametrized_start_eq R₁ γ₁).symm)) := by
  apply Quotient.sound
  exact canonicalSymbolicConcatenation_reparametrization_homotopic
    R₀ R₁ hend

end InfoGeometry.Topology
