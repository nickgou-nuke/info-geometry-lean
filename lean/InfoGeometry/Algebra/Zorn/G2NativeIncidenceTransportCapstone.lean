import InfoGeometry.Algebra.Zorn.G2NativeLineFiber
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native incidence transport for the PC subgroup

This capstone stays on the native three-line fiber.  The exported CAS point
enumeration is used only by the separate intertwining owner; preservation of
the native incidence carrier is proved here from split-octonion multiplication.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeIncidenceTransportCapstone

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2ParabolicLineFiber
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

def NativePreservesIncidence (g : SplitOctF2Aut) : Prop :=
  ∀ L : Finset G2ParabolicLineFiber.OctImF2, L ∈ nativeLines →
    L.image (octImAction g) ∈ nativeLines

theorem nativePreservesIncidence_generator (i : Fin 6) :
    NativePreservesIncidence (pcGenerator i) := by
  intro L hL
  rcases Finset.mem_image.mp hL with ⟨y, hy, rfl⟩
  exact lineSet_action_mem_nativeLines i y hy

theorem nativePreservesIncidence_one :
    NativePreservesIncidence (1 : SplitOctF2Aut) := by
  intro L hL
  have hone : octImAction (1 : SplitOctF2Aut) = id := by
    funext x
    exact octImAction_one x
  rw [hone]
  simpa using hL

theorem nativePreservesIncidence_mul {g h : SplitOctF2Aut}
    (hg : NativePreservesIncidence g)
    (hh : NativePreservesIncidence h) :
    NativePreservesIncidence (g * h) := by
  intro L hL
  have hcomp : octImAction (g * h) =
      octImAction g ∘ octImAction h := by
    funext x
    exact octImAction_mul g h x
  rw [hcomp, ← Finset.image_image]
  exact hg _ (hh L hL)

theorem pcWord_preserves_native_incidence (e : Fin 6 → Bool) :
    NativePreservesIncidence (G2TwoSylowPCAutomorphisms.pcWord e) := by
  unfold G2TwoSylowPCAutomorphisms.pcWord
  have h_all : ∀ i : Fin 6,
      NativePreservesIncidence (if e i then pcGenerator i else 1) := by
    intro i
    by_cases h : e i
    · simp only [h]
      exact nativePreservesIncidence_generator i
    · simp only [h]
      exact nativePreservesIncidence_one
  have h_prod : ∀ L : List SplitOctF2Aut,
      (∀ g ∈ L, NativePreservesIncidence g) →
        NativePreservesIncidence L.prod := by
    intro L
    induction L with
    | nil =>
        intro _
        simpa using nativePreservesIncidence_one
    | cons g gs ih =>
        intro hL
        rw [List.prod_cons]
        apply nativePreservesIncidence_mul
        · exact hL g (List.mem_cons_self)
        · apply ih
          intro x hx
          exact hL x (List.mem_cons_of_mem g hx)
  apply h_prod
  intro g hg
  rw [List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  exact h_all i

theorem unipotentSubgroup_preserves_native_incidence
    (u : SplitOctF2Aut)
    (hu : u ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    NativePreservesIncidence u := by
  change u ∈ Set.range G2TwoSylowSubgroup.pcWord at hu
  obtain ⟨e, rfl⟩ := hu
  exact pcWord_preserves_native_incidence e

end InfoGeometry.Algebra.Zorn.G2NativeIncidenceTransportCapstone
