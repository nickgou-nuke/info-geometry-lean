import InfoGeometry.Topology.SymbolicLatentPathReparametrization
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientFunctoriality

namespace InfoGeometry.Topology

/-!
# Reparametrization on symbolic-latent path homotopy classes

An endpoint-fixing reparametrization acts on representatives by precomposition.
The induced map on the homotopy quotient is well-defined because the same
precomposition can be applied to an endpoint-preserving homotopy.  The explicit
linear homotopy from the reparametrization owner then shows that the quotient
map is the identity.
-/

def reparametrizeSymbolicLatentPathHomotopy
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    {γ₀ γ₁ : SymbolicLatentPath X}
    (H : SymbolicLatentPathHomotopy γ₀ γ₁) :
    SymbolicLatentPathHomotopy
      (reparametrizeSymbolicLatentPath R γ₀)
      (reparametrizeSymbolicLatentPath R γ₁) where
  map := {
    toFun := fun p => H.map (p.1, R.parameter p.2)
    continuous_toFun := H.map.continuous.comp
      (continuous_fst.prodMk
        (R.parameter.continuous.comp continuous_snd)) }
  at_start := by
    intro t
    change H.map (0, R.parameter t) = γ₀ (R.parameter t)
    rw [H.at_start]
  at_finish := by
    intro t
    change H.map (1, R.parameter t) = γ₁ (R.parameter t)
    rw [H.at_finish]
  fixed_start := by
    intro s
    change H.map (s, R.parameter 0) = (reparametrizeSymbolicLatentPath R γ₀).start
    rw [R.at_zero, H.fixed_start]
    change γ₀ 0 = γ₀ (R.parameter 0)
    rw [R.at_zero]
  fixed_finish := by
    intro s
    change H.map (s, R.parameter 1) = (reparametrizeSymbolicLatentPath R γ₀).finish
    rw [R.at_one, H.fixed_finish]
    change γ₀ 1 = γ₀ (R.parameter 1)
    rw [R.at_one]

noncomputable def reparametrizeSymbolicLatentPathHomotopyQuotient
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    SymbolicLatentPathHomotopyQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient (X := X) :=
  Quotient.lift
    (fun γ => symbolicLatentPathHomotopyQuotientMap
      (reparametrizeSymbolicLatentPath R γ))
    (by
      intro γ₀ γ₁ h
      apply Quotient.sound
      exact ⟨reparametrizeSymbolicLatentPathHomotopy R h.some⟩)

@[simp] theorem reparametrizeSymbolicLatentPathHomotopyQuotient_mk
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (γ : SymbolicLatentPath X) :
    reparametrizeSymbolicLatentPathHomotopyQuotient R
        (symbolicLatentPathHomotopyQuotientMap γ) =
      symbolicLatentPathHomotopyQuotientMap
        (reparametrizeSymbolicLatentPath R γ) :=
  rfl

theorem reparametrizeSymbolicLatentPathHomotopyQuotient_id
    {X : Type*} [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization) :
    reparametrizeSymbolicLatentPathHomotopyQuotient R =
      (id : SymbolicLatentPathHomotopyQuotient (X := X) →
        SymbolicLatentPathHomotopyQuotient (X := X)) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro γ
  apply Quotient.sound
  exact (reparametrizeSymbolicLatentPath_homotopic R γ).symm

end InfoGeometry.Topology
