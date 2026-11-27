/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSTomitaClosedOperator
import InfoGeometry.OperatorAlgebra.RealAdjointSquare

/-!
# The modular adjoint square on the original GNS Hilbert space

The existing closed Tomita operator is real-linear on the same completed GNS
carrier. It is packaged as a native `LinearPMap`, with density proved from the
original pre-GNS core and closedness proved from the original graph closure.
The operator `Delta` is its actual unbounded adjoint square, with the exact
composition domain. It is positive and self-adjoint there. The modular-form
quotient and its separate Hilbert completion are not substituted for this
ambient carrier. Closability of the original core remains an explicit input.
-/

noncomputable section

namespace CStarStateColimit.Native.ClosedTomitaAdjointSquare

open CStarStateColimit.Native
open FilteredGNSTomitaCore FilteredGNSTomitaGraph FilteredGNSTomitaClosability
open FilteredGNSTomitaClosedOperator
open InfoGeometry.OperatorAlgebra.RealAdjointSquare
open scoped Topology

universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Restriction of scalars retains the same actual domain and ambient vector. -/
abbrev closedTomitaRealDomain (ω : State A) : Submodule ℝ ω.functional.GNS :=
  (closedTomitaDomain ω).restrictScalars ℝ

/-- The original closed Tomita operation as a real partially defined operator. -/
def closedTomitaRealPMap (ω : State A) (hclos : IsClosableTomitaCore ω) :
    ω.functional.GNS →ₗ.[ℝ] ω.functional.GNS where
  domain := closedTomitaRealDomain ω
  toFun :=
    { toFun := closedTomitaOperator ω hclos
      map_add' := (closedTomitaOperator ω hclos).map_add
      map_smul' := fun r x => by
        change closedTomitaValue ω (r • x) = r • closedTomitaValue ω x
        apply closedTomitaValue_eq_of_mem ω hclos
        have h := tomitaScalarPairMap_mapsTo_closedTomitaCoreGraph ω (r : ℂ)
          (closedTomitaValue_mem_graph ω x)
        simpa [tomitaScalarPairMap] using h }

@[simp] theorem closedTomitaRealPMap_apply (ω : State A)
    (hclos : IsClosableTomitaCore ω) (x : closedTomitaRealDomain ω) :
    closedTomitaRealPMap ω hclos x = closedTomitaOperator ω hclos x := rfl

/-- The real partial map has exactly the original closed graph. -/
theorem closedTomitaRealPMap_graph (ω : State A) (hclos : IsClosableTomitaCore ω) :
    ((closedTomitaRealPMap ω hclos).graph :
      Set (ω.functional.GNS × ω.functional.GNS)) = closedTomitaCoreGraph ω := by
  rw [← closedTomitaOperatorGraph_eq ω hclos]
  ext p
  change p ∈ (closedTomitaRealPMap ω hclos).graph ↔
    p ∈ closedTomitaOperatorGraph ω hclos
  rw [LinearPMap.mem_graph_iff']
  change (∃ x : closedTomitaDomain ω,
      ((x : ω.functional.GNS), closedTomitaOperator ω hclos x) = p) ↔
    ∃ x : closedTomitaDomain ω,
      p = ((x : ω.functional.GNS), closedTomitaOperator ω hclos x)
  exact exists_congr fun _ => eq_comm

theorem closedTomitaRealPMap_isClosed (ω : State A)
    (hclos : IsClosableTomitaCore ω) : (closedTomitaRealPMap ω hclos).IsClosed := by
  change IsClosed ((closedTomitaRealPMap ω hclos).graph :
    Set (ω.functional.GNS × ω.functional.GNS))
  rw [closedTomitaRealPMap_graph]
  exact isClosed_closedTomitaCoreGraph ω

/-- Density follows from inclusion of every original algebraic GNS vector. -/
theorem closedTomitaRealDomain_dense (ω : State A) :
    Dense (closedTomitaRealDomain ω : Set ω.functional.GNS) := by
  apply UniformSpace.Completion.denseRange_coe.mono
  rintro x ⟨v, rfl⟩
  change ∃ y, ((v : ω.functional.GNS), y) ∈ closedTomitaCoreGraph ω
  exact ⟨(tomitaCore ω v : ω.functional.GNS), subset_closure ⟨v, rfl⟩⟩

local instance realGNSInnerProduct (ω : State A) : InnerProductSpace ℝ ω.functional.GNS :=
  InnerProductSpace.complexToReal

/-- The actual modular product on the original realified GNS Hilbert space. -/
def modularOperator (ω : State A) (hclos : IsClosableTomitaCore ω) :
    ω.functional.GNS →ₗ.[ℝ] ω.functional.GNS :=
  adjointSquare (closedTomitaRealPMap ω hclos)

/-- Domain membership means exactly that the closed Tomita image belongs to
the domain of its actual unbounded adjoint. -/
theorem mem_modularOperator_domain (ω : State A) (hclos : IsClosableTomitaCore ω)
    (x : ω.functional.GNS) :
    x ∈ (modularOperator ω hclos).domain ↔
      ∃ hx : x ∈ closedTomitaRealDomain ω,
        closedTomitaOperator ω hclos ⟨x, hx⟩ ∈
          (closedTomitaRealPMap ω hclos).adjoint.domain :=
  mem_adjointSquareDomain (closedTomitaRealPMap ω hclos) x

/-- On the actual product domain the associated form is the original Tomita
form, using the original GNS inner product. -/
theorem modularOperator_form (ω : State A) (hclos : IsClosableTomitaCore ω)
    (x : (modularOperator ω hclos).domain) (y : closedTomitaRealDomain ω) :
    inner ℝ (modularOperator ω hclos x) (y : ω.functional.GNS) =
      inner ℝ
        (closedTomitaOperator ω hclos
          (squareDomainInclusion (closedTomitaRealPMap ω hclos) x))
        (closedTomitaOperator ω hclos y) :=
  adjointSquare_form (closedTomitaRealPMap ω hclos) (closedTomitaRealDomain_dense ω) x y

theorem modularOperator_quadratic (ω : State A) (hclos : IsClosableTomitaCore ω)
    (x : (modularOperator ω hclos).domain) :
    inner ℝ (x : ω.functional.GNS) (modularOperator ω hclos x) =
      ‖closedTomitaOperator ω hclos
        (squareDomainInclusion (closedTomitaRealPMap ω hclos) x)‖ ^ 2 :=
  adjointSquare_quadratic (closedTomitaRealPMap ω hclos) (closedTomitaRealDomain_dense ω) x

theorem modularOperator_nonneg (ω : State A) (hclos : IsClosableTomitaCore ω)
    (x : (modularOperator ω hclos).domain) :
    0 ≤ inner ℝ (x : ω.functional.GNS) (modularOperator ω hclos x) :=
  adjointSquare_nonneg (closedTomitaRealPMap ω hclos) (closedTomitaRealDomain_dense ω) x

theorem modularOperator_dense_domain (ω : State A) (hclos : IsClosableTomitaCore ω) :
    Dense ((modularOperator ω hclos).domain : Set ω.functional.GNS) :=
  adjointSquare_dense_domain (closedTomitaRealPMap ω hclos)
    (closedTomitaRealDomain_dense ω) (closedTomitaRealPMap_isClosed ω hclos)

/-- Self-adjointness is derived from closed graph projection on the original
Hilbert space, without a supplied modular-operator certificate. -/
theorem modularOperator_isSelfAdjoint (ω : State A) (hclos : IsClosableTomitaCore ω) :
    IsSelfAdjoint (modularOperator ω hclos) :=
  adjointSquare_isSelfAdjoint (closedTomitaRealPMap ω hclos)
    (closedTomitaRealDomain_dense ω) (closedTomitaRealPMap_isClosed ω hclos)

theorem modularOperator_isClosed (ω : State A) (hclos : IsClosableTomitaCore ω) :
    (modularOperator ω hclos).IsClosed := (modularOperator_isSelfAdjoint ω hclos).isClosed

end CStarStateColimit.Native.ClosedTomitaAdjointSquare
