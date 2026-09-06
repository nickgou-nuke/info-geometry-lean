import InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
import InfoGeometry.Canonical.CantorBoundaryCuntzShift

/-!
# Branch self-similarity on the concrete projective-limit carrier

The categorical inverse-limit owner already transports `prependBit` to its
limit object.  This owner transports the same branch map to the concrete
coherent-family carrier and proves the two descriptions are conjugate.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.CantorBoundaryCuntzShift

def projectivePrependBitTopCatHom (b : Bool) :
    TopCat.of PrefixProjectiveLimit ⟶ TopCat.of PrefixProjectiveLimit :=
  cantorProjectiveLimitTopCatIso.inv ≫ prependBitHom b ≫
    cantorProjectiveLimitTopCatIso.hom

theorem projectivePrependBitTopCatHom_apply (b : Bool)
    (p : PrefixProjectiveLimit) :
    projectivePrependBitTopCatHom b p =
      cantorHomeomorphPrefixProjectiveLimit
        (prependBit b (toCantor p)) := by
  rfl

theorem projectivePrependBitTopCatHom_ofCantor
    (b : Bool) (x : ℕ → Bool) :
    projectivePrependBitTopCatHom b (ofCantor x) =
      ofCantor (prefixBit b x) := by
  rw [projectivePrependBitTopCatHom_apply, toCantor_ofCantor]
  change ofCantor (prependBit b x) = ofCantor (prefixBit b x)
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem projectivePrependBitTopCatHom_injective (b : Bool) :
    Function.Injective (fun p : PrefixProjectiveLimit =>
      projectivePrependBitTopCatHom b p) := by
  intro p q h
  change projectivePrependBitTopCatHom b p =
    projectivePrependBitTopCatHom b q at h
  rw [projectivePrependBitTopCatHom_apply b p,
    projectivePrependBitTopCatHom_apply b q] at h
  have h' : prependBit b (toCantor p) = prependBit b (toCantor q) :=
    cantorHomeomorphPrefixProjectiveLimit.injective h
  have hword : toCantor p = toCantor q :=
    prependBit_injective b h'
  calc
    p = ofCantor (toCantor p) := (ofCantor_toCantor p).symm
    _ = ofCantor (toCantor q) := by rw [hword]
    _ = q := ofCantor_toCantor q

theorem projectivePrependBitTopCatHom_range_cover
    (p : PrefixProjectiveLimit) :
    (∃ q, projectivePrependBitTopCatHom false q = p) ∨
      ∃ q, projectivePrependBitTopCatHom true q = p := by
  rcases prependBit_range_cover (toCantor p) with hfalse | htrue
  · left
    rcases hfalse with ⟨x, hx⟩
    refine ⟨ofCantor x, ?_⟩
    rw [projectivePrependBitTopCatHom_apply,
      toCantor_ofCantor, hx]
    exact ofCantor_toCantor p
  · right
    rcases htrue with ⟨x, hx⟩
    refine ⟨ofCantor x, ?_⟩
    rw [projectivePrependBitTopCatHom_apply,
      toCantor_ofCantor, hx]
    exact ofCantor_toCantor p

theorem projectivePrependBitTopCatHom_ranges_disjoint :
    Disjoint
      (Set.range (fun p : PrefixProjectiveLimit =>
        projectivePrependBitTopCatHom false p))
      (Set.range (fun p : PrefixProjectiveLimit =>
        projectivePrependBitTopCatHom true p)) := by
  refine Set.disjoint_left.2 ?_
  intro p hp hq
  rcases hp with ⟨p₀, hp₀⟩
  rcases hq with ⟨q₀, hq₀⟩
  have heq : projectivePrependBitTopCatHom false p₀ =
      projectivePrependBitTopCatHom true q₀ := hp₀.trans hq₀.symm
  rw [projectivePrependBitTopCatHom_apply,
    projectivePrependBitTopCatHom_apply] at heq
  have hcantor := congrArg
    (fun r : PrefixProjectiveLimit => toCantor r) heq
  change prependBit false (toCantor p₀) =
    prependBit true (toCantor q₀) at hcantor
  apply Set.disjoint_left.1 prependBit_false_true_disjoint
  · exact ⟨toCantor p₀, rfl⟩
  · exact ⟨toCantor q₀, hcantor.symm⟩

theorem projectivePrependBitTopCatHom_ranges_union :
    Set.range (fun p : PrefixProjectiveLimit =>
        projectivePrependBitTopCatHom false p) ∪
      Set.range (fun p : PrefixProjectiveLimit =>
        projectivePrependBitTopCatHom true p) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact projectivePrependBitTopCatHom_range_cover p

theorem projective_categorical_branch_conjugacy (b : Bool) :
    projectiveToCategoricalLimitTopCatIso.hom ≫ prefixLimitPrependBit b =
      projectivePrependBitTopCatHom b ≫
        projectiveToCategoricalLimitTopCatIso.hom := by
  simp [projectiveToCategoricalLimitTopCatIso,
    projectivePrependBitTopCatHom, prefixLimitPrependBit, Category.assoc]

end InfoGeometry.Canonical.CantorProjectiveLimitBranchTopCat
