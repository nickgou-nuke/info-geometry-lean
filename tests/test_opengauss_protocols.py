"""Tests for OpenGauss Native Workflows, Top-Down Protocol, and 15-Trap Screener.

Verifies detection of:
- Trap T1: Raw coordinate extraction off-basepoint.
- Trap T3: Global flatness / locally constant charts.
- Trap T4: Vacuous binders.
- Trap T6: Hypothesis packaging.
- Trap T15: Colimit definitional unfolding.
- Clean verification on valid Lean 4 modules.
"""

from __future__ import annotations

from pathlib import Path
import pytest
from tools.infra.opengauss_screener import (
    TrapViolation,
    _has_closed_noncommutativity_witness,
    check_authored_axioms_and_holes,
    main as screener_main,
    screen_lean_content,
    screen_lean_file,
    serialize_quarantine_packet,
)


def test_screen_clean_module():
    """Verify that a valid, well-formed Lean declaration passes with zero errors."""
    code = """
    import Mathlib.Tactic

    theorem add_comm_real (x y : Real) : x + y = y + x := by
      ring
    """
    violations = screen_lean_content(code)
    errors = [v for v in violations if v.severity == "ERROR"]
    assert len(errors) == 0


def test_t17_dag_basic_graphs_have_constructive_inhabitants():
    target = Path(__file__).resolve().parents[1] / "lean" / "DAG" / "Basic.lean"
    violations = screen_lean_file(target)
    t17 = [v for v in violations if v.trap_id == "T17"]
    assert t17 == []


def test_t17_block_decomposition_has_constructive_empty_model():
    target = Path(__file__).resolve().parents[1] / "lean" / "DAG" / "BlockDecomposition.lean"
    violations = screen_lean_file(target)
    t17 = [v for v in violations if v.trap_id == "T17"]
    assert t17 == []


def test_detect_trap_t4_vacuous_binder():
    """Verify detection of Trap T4 (vacuous binder)."""
    code = """
    theorem trivial_bound (x : Real) (h : 0 = 0) : x ≤ x := by
      linarith
    """
    violations = screen_lean_content(code)
    t4 = [v for v in violations if v.trap_id == "T4"]
    assert len(t4) >= 1
    assert "Vacuous binder" in t4[0].message


def test_detect_trap_t6_hypothesis_packaging():
    """Verify detection of Trap T6 (hypothesis packaging / self-assumption)."""
    code = """
    theorem packaged_claim (P : Prop) (h : P) : P := by
      exact h
    """
    violations = screen_lean_content(code)
    t6 = [v for v in violations if v.trap_id == "T6"]
    assert len(t6) >= 1
    assert "Hypothesis" in t6[0].trap_name
    assert "as proof" in t6[0].message


def test_t6_detects_implicit_packaged_hypothesis_across_lines():
    code = """
    theorem packaged_implicit
        {P : Prop} {h : P} :
        P := by
      exact h
    """
    t6 = [v for v in screen_lean_content(code) if v.trap_id == "T6"]
    assert len(t6) == 1
    assert "packaged_implicit" in t6[0].message


def test_t4_detects_prop_true_surrogate():
    code = "def tautology : Prop := True"
    assert any(v.trap_id == "T4" for v in screen_lean_content(code))


def test_t4_warns_on_unused_hypothesis_binder():
    code = "theorem unused_hypothesis (h : P) (x : Nat) : x = x := by rfl"
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert len(t4) == 1


def test_t4_rejects_used_but_reflexive_quantified_hypothesis():
    code = """
    theorem reflexive_quantified_hypothesis {X : Type} (f : X → Nat)
        (h : ∀ x, f x = f x) : ∀ x, f x = f x ∧ True := by
      intro x
      exact ⟨h x, trivial⟩
    """
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert len(t4) == 1
    assert "reflexive" in t4[0].message


def test_t4_preserves_identifier_boundaries_in_reflexivity_check():
    code = """
    theorem distinct_identifiers {X : Type} (f : X → Nat) (fx : Nat)
        (h : ∀ x, f x = fx) : ∀ x, f x = fx := by
      exact h
    """
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert t4 == []


def test_t4_detects_reflexivity_under_grouped_forall_binders():
    code = """
    theorem grouped_reflexive_hypothesis {X : Type} (f : X → X → Nat)
        (h : ∀ x y, f x y = f x y) : ∀ x y, f x y = f x y := by
      exact h
    """
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert len(t4) == 1
    assert "reflexive" in t4[0].message


def test_t4_detects_parenthesized_reflexive_quantified_hypothesis():
    code = """
    theorem parenthesized_reflexive_hypothesis {X : Type} (f : X → Nat)
        (h : ∀ x, f x = (f x)) : ∀ x, f x = f x := by
      intro x
      exact h x
    """
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert len(t4) == 1
    assert "reflexive" in t4[0].message


def test_t4_recognizes_used_apostrophe_suffixed_hypothesis():
    code = "theorem used_primed_hypothesis {x y : Nat} (h' : x = y) : y = x := by exact h'.symm"
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert t4 == []


def test_t4_still_detects_unused_apostrophe_suffixed_hypothesis():
    code = "theorem unused_primed_hypothesis (h' : 0 = 0) (n : Nat) : n = n := by rfl"
    t4 = [v for v in screen_lean_content(code) if v.trap_id == "T4"]
    assert len(t4) == 1
    assert "h'" in t4[0].message


def test_t4_recognizes_equality_hypothesis_consumed_by_subst():
    code = """
    theorem subst_uses_equality {a u n : Nat}
        (ha : a = u + n) (h_unused : n = n) : a = u + n := by
      subst a
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert len(t4) == 1
    assert "h_unused" in t4[0].message


def test_t4_does_not_hide_unused_equality_when_subst_uses_local_equality():
    code = """
    theorem subst_uses_local_equality {x : Nat}
        (h_unused : x = x) (h : x = 0) : x = 0 := by
      have hx : x = 0 := h
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    reported_binders = [v.matched_text.split(":", 1)[0].strip("( ") for v in t4]
    assert reported_binders == ["h_unused"]
    assert t4[0].severity == "WARNING"


def test_t4_keeps_declaration_equality_consumed_after_unrelated_have():
    code = """
    theorem subst_after_unrelated_have {x y : Nat} (h : x = y) : x = y := by
      have hy : y = y := by
        rfl
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert t4 == []


def test_t4_keeps_subst_after_unrelated_simp_have():
    code = """
    theorem subst_after_simp_have {x y : Nat} (h : x = y) : x = y := by
      have hy : y = y := by simp
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert t4 == []


def test_t4_keeps_subst_after_unrelated_exact_have():
    code = """
    theorem subst_after_exact_have {x y : Nat} (h : x = y) : x = y := by
      have hy : y = y := by exact rfl
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert t4 == []


def test_t4_keeps_subst_after_multiline_unrelated_have():
    code = """
    theorem subst_after_multiline_have {x y : Nat} (h : x = y) : x = y := by
      have hy : y = y := by
        simp
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert t4 == []


def test_t4_does_not_credit_subst_inside_fallback_branch():
    code = """
    theorem subst_failure_fallback {x : Nat} (h_unused : x = x + 1) : True := by
      first | subst x | trivial
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert len(t4) == 1
    assert "h_unused" in t4[0].message


def test_t4_does_not_hide_unused_equality_after_intro_before_subst():
    code = """
    theorem subst_uses_intro_equality {x y : Nat}
        (h_unused : x = y) : x = y → x = y := by
      intro hx
      subst x
      rfl
    """
    t4 = [
        v for v in screen_lean_content(code)
        if v.trap_id == "T4" and "unused hypothesis binder" in v.message
    ]
    assert len(t4) == 1
    assert "h_unused" in t4[0].message
    assert t4[0].severity == "WARNING"


def test_t4_subst_exemption_requires_bare_top_level_equality_side():
    for binder_type in ("P = (Q = x)", "(x = P) = Q"):
        code = f"""
        theorem nested_subst_equality (P Q x : Prop)
            (h_unused : {binder_type}) : True := by
          first | subst x | trivial
        """
        t4 = [
            violation for violation in screen_lean_content(code)
            if violation.trap_id == "T4"
            and "unused hypothesis binder" in violation.message
        ]
        assert len(t4) == 1, (binder_type, t4)
        assert "h_unused" in t4[0].message


def test_t4_subst_recognizes_explicit_eq_and_parenthesized_identifier_sides():
    for binder_type in ("Eq x y", "Eq (x) y", "(x) = y"):
        code = f"""
        theorem subst_equality_syntax (x y : Nat) (h : {binder_type}) : x = y := by
          subst x
          rfl
        """
        t4 = [
            violation for violation in screen_lean_content(code)
            if violation.trap_id == "T4"
            and "unused hypothesis binder" in violation.message
        ]
        assert t4 == [], (binder_type, t4)


def test_t10_warns_on_top_smoothness_over_closed_interval():
    code = "theorem bad_regularity (f : ℝ → ℝ) : ContDiff ℝ ⊤ f on Set.Icc (0 : ℝ) 1 := by sorry"
    assert any(v.trap_id == "T10" for v in screen_lean_content(code))


def test_t13_rejects_positive_definite_krein_signature_mix():
    code = "variable [KreinSpace V] [InnerProductSpace ℝ V]"
    assert any(v.trap_id == "T13" for v in screen_lean_content(code))


def test_t17_accepts_multiline_typed_model_witness():
    code = """
    structure NonemptyCarrier where
      value : Nat

    def standardCarrier :
        NonemptyCarrier := ⟨0⟩
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert t17 == []


def test_t17_accepts_where_model_witness():
    code = """
    structure WhereCarrier where
      value : Nat

    def standardWhereCarrier : WhereCarrier where
      value := 0
    """
    assert not any(v.trap_id == "T17" for v in screen_lean_content(code))


def test_t17_safe_inhabited_instance_does_not_crash():
    code = """
    structure SafeInhabitedCarrier where
      value : Nat
    instance : Inhabited SafeInhabitedCarrier := ⟨⟨0⟩⟩
    """
    assert not any(v.trap_id == "T17" for v in screen_lean_content(code))


@pytest.mark.parametrize("axiom_name", ["κ", "«fakeModel»"])
def test_t17_rejects_axiom_backed_witness_with_non_ascii_or_quoted_name(axiom_name):
    code = f"""
    structure UnicodeAxiomCarrier where
      value : Nat
    axiom {axiom_name} : UnicodeAxiomCarrier
    def apparentModel : UnicodeAxiomCarrier := {axiom_name}
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert t17


def test_t17_does_not_accept_witness_from_hidden_section_variable():
    code = """
    structure HiddenContextCarrier where
      value : Nat
    section
    variable (model : HiddenContextCarrier)
    theorem claimedModel : HiddenContextCarrier := by assumption
    end
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert t17


def test_t17_still_flags_unwitnessed_structure():
    code = """
    structure UnwitnessedCarrier where
      value : Nat
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert len(t17) == 1
    assert "UnwitnessedCarrier" in t17[0].message


def test_t17_discovers_modified_structures_and_attribute_prefixed_structures():
    code = """
    private structure HiddenCarrier where
      value : Nat

    @[to_additive] structure AttributedCarrier where
      value : Nat
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert any("HiddenCarrier" in v.message for v in t17)
    assert any("AttributedCarrier" in v.message for v in t17)


def test_t17_does_not_treat_implication_domain_as_model_witness():
    code = """
    structure EmptyByContract where
      value : Nat

    theorem only_if_empty (x : EmptyByContract) : True := by
      trivial
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert len(t17) == 1


def test_t17_rejects_same_type_echo_as_model_witness():
    code = """
    structure EchoCarrier where
      value : Nat

    theorem echo (x : EchoCarrier) : EchoCarrier := x
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert len(t17) == 1


def test_t17_rejects_same_type_echo_through_strict_implicit_binder():
    code = """
    structure StrictEchoCarrier where
      value : Nat

    theorem echo ⦃x : StrictEchoCarrier⦄ : StrictEchoCarrier := x
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(code))


def test_t17_rejects_section_variable_echo_and_existence_typeclass():
    section_echo = """
    structure SectionCarrier where
      value : Nat

    variable (x : SectionCarrier)
    theorem echo : SectionCarrier := x
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(section_echo))

    assumed_nonempty = """
    structure ConditionalCarrier where
      value : Nat

    theorem model [Nonempty ConditionalCarrier] : ConditionalCarrier :=
      Classical.choice ‹Nonempty ConditionalCarrier›
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(assumed_nonempty))


def test_t17_accepts_closed_model_independent_of_ambient_target_variable():
    independent = """
    structure AmbientCarrier where
      value : Nat

    section
    variable (x : AmbientCarrier)
    def canonicalAmbientModel : AmbientCarrier := ⟨0⟩
    end
    """
    assert not any(v.trap_id == "T17" for v in screen_lean_content(independent))


def test_t17_rejects_model_forwarding_to_local_axiom_or_hole_helper():
    axiom_backed = """
    structure AxiomCarrier where
      value : Nat

    axiom fakeAxiomCarrier : AxiomCarrier
    def fakeCarrierHelper : AxiomCarrier := fakeAxiomCarrier
    def apparentCarrierModel : AxiomCarrier := fakeCarrierHelper
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(axiom_backed))

    hole_helper = """
    structure HoleHelperCarrier where
      value : Nat

    def fakeHoleHelper : HoleHelperCarrier := by sorry
    def apparentHoleModel : HoleHelperCarrier := fakeHoleHelper
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(hole_helper))


def test_t17_rejects_target_providing_typeclass_and_abbrev_axiom_chain():
    supplied = """
    structure SuppliedCarrier where
      value : Nat
    class CarrierProvider where
      get : SuppliedCarrier
    def allegedModel [CarrierProvider] : SuppliedCarrier := CarrierProvider.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(supplied))

    hidden_axiom = """
    structure PrivateAxiomCarrier where
      value : Nat
    private axiom privateBadModel : PrivateAxiomCarrier
    abbrev privateModelAlias : PrivateAxiomCarrier := privateBadModel
    def apparentPrivateModel : PrivateAxiomCarrier := privateModelAlias
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(hidden_axiom))


def test_t17_tracks_ambient_aliases_and_nested_section_scopes():
    code = """
    structure NestedAmbientCarrier where
      value : Nat
    abbrev NestedCarrierAlias := NestedAmbientCarrier
    section Outer
    variable (x : NestedCarrierAlias)
    section Inner
    end Inner
    def apparentNestedModel : NestedAmbientCarrier := x
    end Outer
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(code))


def test_t17_rejects_product_result_and_proof_hole_as_direct_model():
    product_result = """
    structure ProductCarrier where
      value : Nat

    def productModel : ProductCarrier × Nat := sorry
    """
    hole_result = """
    structure HoleCarrier where
      value : Nat

    def holeModel : HoleCarrier := by
      sorry
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(product_result))
    assert any(v.trap_id == "T17" for v in screen_lean_content(hole_result))

    closed_product = """
    structure ProductCarrier where
      value : Nat

    def productModel : ProductCarrier × Nat := (⟨0⟩, 0)
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(closed_product))


def test_t17_accepts_uniform_model_over_type_and_law_parameters():
    code = """
    structure GenericCarrier (α : Type*) where
      value : α

    def standardCarrier {α : Type*} [Inhabited α] : GenericCarrier α :=
      ⟨default⟩
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert t17 == []


def test_t17_ambient_polymorphic_and_multiple_variables_are_tracked_correctly():
    polymorphic = """
    structure PolyCarrier where
      value : Nat
    variable α : Type
    def standardPolyCarrier : PolyCarrier := ⟨0⟩
    """
    assert not any(v.trap_id == "T17" for v in screen_lean_content(polymorphic))

    borrowed = """
    structure BorrowedCarrier where
      value : Nat
    variable x y : BorrowedCarrier
    def allegedModel : BorrowedCarrier := y
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(borrowed))


def test_t17_rejects_alias_hidden_and_unresolved_provider_classes():
    local_alias_provider = """
    structure Foo where
      value : Nat
    abbrev FooAlias := Foo
    class Provider where
      get : FooAlias
    def allegedModel [Provider] : Foo := Provider.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(local_alias_provider))

    imported_provider = """
    structure Foo where
      value : Nat
    def allegedModel [ExternalProvider] : Foo := ExternalProvider.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(imported_provider))


def test_t17_rejects_def_alias_and_multiline_superclass_provider():
    def_alias = """
    structure Foo where
      value : Nat
    def FooAlias := Foo
    class Provider where
      get : FooAlias
    def allegedModel [Provider] : Foo := Provider.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(def_alias))

    inherited = """
    structure Bar where
      value : Nat
    class HasBar where
      get : Bar
    class Child
      extends HasBar where
      marker : Unit
    def allegedModel [Child] : Bar := HasBar.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(inherited))


def test_t17_rejects_imported_axiom_backed_model(tmp_path):
    module = tmp_path / "lean" / "WitnessPkg" / "Unsafe.lean"
    module.parent.mkdir(parents=True)
    module.write_text("""
    axiom genericInhabitant {α : Type} : α
    """, encoding="utf-8")
    target = """
    import WitnessPkg.Unsafe
    structure ImportedAxiomCarrier where
      value : Nat
    def apparentModel : ImportedAxiomCarrier := genericInhabitant
    """
    assert any(
        v.trap_id == "T17"
        for v in screen_lean_content(target, filename="Target.lean", import_root=tmp_path)
    )


def test_t17_resolves_typed_def_aliases_and_alias_inhabited_assumptions():
    typed_provider = """
    structure TypedFoo where
      value : Nat
    def TypedFooAlias : Type := TypedFoo
    class TypedProvider where
      get : TypedFooAlias
    def allegedModel [TypedProvider] : TypedFoo := TypedProvider.get
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(typed_provider))

    typed_inhabited = """
    structure TypedAliasCarrier where
      value : Nat
    def TypedCarrierAlias : Type := TypedAliasCarrier
    theorem borrowedModel [Inhabited TypedCarrierAlias] : TypedAliasCarrier := default
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(typed_inhabited))


def test_t17_taints_local_named_and_anonymous_inhabited_instances_used_by_default():
    named = """
    structure Foo where
      value : Nat
    axiom badFoo : Foo
    instance instFoo : Inhabited Foo := ⟨badFoo⟩
    def apparentModel : Foo := default
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(named))

    anonymous = """
    structure Bar where
      value : Nat
    axiom badBar : Bar
    instance : Inhabited Bar := ⟨badBar⟩
    def apparentModel : Bar := default
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(anonymous))


def test_t17_import_closure_follows_grouped_imports_and_alias_taint(tmp_path):
    unsafe = tmp_path / "lean" / "WitnessPkg" / "Unsafe.lean"
    other = tmp_path / "lean" / "WitnessPkg" / "Other.lean"
    unsafe.parent.mkdir(parents=True)
    unsafe.write_text("""
    axiom genericInhabitant {α : Type} : α
    abbrev genericAlias {α : Type} : α := genericInhabitant
    def genericHelper {α : Type} : α := genericAlias
    """, encoding="utf-8")
    other.write_text("theorem harmless : True := True.intro\n", encoding="utf-8")
    target = """
    import WitnessPkg.Unsafe WitnessPkg.Other
    structure ImportedCarrier where
      value : Nat
    def apparentModel : ImportedCarrier := genericHelper
    """
    assert any(
        v.trap_id == "T17"
        for v in screen_lean_content(target, import_root=tmp_path)
    )


def test_t17_detects_unsafe_inhabited_instance_through_type_alias():
    code = """
    structure AliasFoo where
      value : Nat
    abbrev AliasFooName := AliasFoo
    axiom badFoo : AliasFooName
    instance : Inhabited AliasFooName := ⟨badFoo⟩
    def apparentModel : AliasFoo := default
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(code))


def test_t17_imported_unsafe_name_does_not_taint_unrelated_local_name(tmp_path):
    imported = tmp_path / "lean" / "WitnessPkg" / "Unsafe.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("""
    namespace Imported
    axiom model : False
    end Imported
    """, encoding="utf-8")
    target = """
    import WitnessPkg.Unsafe
    structure LocalCarrier where
      value : Nat
    namespace Local
    def model : LocalCarrier := ⟨0⟩
    end Local
    """
    assert not any(
        v.trap_id == "T17"
        for v in screen_lean_content(target, filename="Target.lean", import_root=tmp_path)
    )


def test_t17_qualified_imported_taint_survives_leaf_name_collision(tmp_path):
    imported = tmp_path / "lean" / "WitnessPkg" / "Unsafe.lean"
    imported.parent.mkdir(parents=True)
    imported.write_text("""
    namespace Imported
    axiom model {α : Type} : α
    end Imported
    """, encoding="utf-8")
    target = """
    import WitnessPkg.Unsafe
    structure LocalCarrier where
      value : Nat
    namespace Local
    def model : Nat := 0
    def apparentModel : LocalCarrier := Imported.model
    end Local
    """
    assert any(
        v.trap_id == "T17"
        for v in screen_lean_content(target, import_root=tmp_path)
    )


def test_t17_rejects_inhabited_alias_as_a_model_assumption():
    code = """
    structure InhabitedAliasCarrier where
      value : Nat
    abbrev CarrierAlias := InhabitedAliasCarrier
    theorem borrowedModel [Inhabited CarrierAlias] : InhabitedAliasCarrier := default
    """
    assert any(v.trap_id == "T17" for v in screen_lean_content(code))


def test_t17_does_not_borrow_inhabited_deriving_from_next_structure():
    code = """
    structure FirstCarrier where
      value : Nat

    structure SecondCarrier where
      value : Nat
    deriving Inhabited
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert len(t17) == 1
    assert "FirstCarrier" in t17[0].message


def test_t17_accepts_derived_inhabited_instance():
    code = """
    structure InhabitedCarrier where
      value : Nat
    deriving Inhabited
    """
    t17 = [v for v in screen_lean_content(code) if v.trap_id == "T17"]
    assert t17 == []



def test_detect_trap_t3_global_flatness():
    """Verify detection of Trap T3 (locally constant chart / global flatness)."""
    code = """
    theorem manifold_flatness (M : Type*) [HasLocallyConstantChartAt M] : True := by
      trivial
    """
    violations = screen_lean_content(code)
    t3 = [v for v in violations if v.trap_id == "T3"]
    assert len(t3) >= 1
    assert "HasLocallyConstantChartAt" in t3[0].message


def test_detect_trap_t1_raw_chart_extraction():
    """Verify detection of Trap T1 (raw coordinate extraction with moving chart)."""
    code = """
    def bad_curve (x : M) := extChartAt I (achart x) x
    """
    violations = screen_lean_content(code)
    t1 = [v for v in violations if v.trap_id == "T1"]
    assert len(t1) >= 1
    assert "Raw coordinate change" in t1[0].message


def test_quarantine_packet_is_written_without_staging_repo_state(tmp_path):
    source = tmp_path / "Bad.lean"
    source.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
    out_dir = tmp_path / "quarantine"
    violation = TrapViolation("T-test", "test", 1, "sorry", "test finding")

    out = serialize_quarantine_packet(violation, source, out_dir, tmp_path)

    assert out.is_file()
    assert "T-test" in out.name


def test_missing_screener_target_returns_error(capsys):
    assert screener_main(["missing-target.lean"]) == 1
    assert "Target not found" in capsys.readouterr().err


def test_detect_trap_t16_homomorphism_rejection():
    """Verify Trap T16 Homomorphism Rejection: collapsing algebra into scalar field before commutator."""
    code_commutator_trace = """
    def badComm (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
      commutator (Matrix.trace A) (Matrix.trace B)
    """
    v1 = screen_lean_content(code_commutator_trace)
    t16_1 = [v for v in v1 if v.trap_id == "T16" and "Homomorphism" in v.trap_name]
    assert len(t16_1) >= 1
    assert "pre-commutator" in t16_1[0].trap_name.lower() or "homomorphism" in t16_1[0].trap_name.lower()

    code_trace_diff = """
    def fakeComm (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
      Matrix.trace A * Matrix.trace B - Matrix.trace B * Matrix.trace A
    """
    v2 = screen_lean_content(code_trace_diff)
    t16_2 = [v for v in v2 if v.trap_id == "T16" and "Homomorphism" in v.trap_name]
    assert len(t16_2) >= 1


def test_detect_trap_t16_missing_noncommutative_witness():
    """Require a witness when square matrices are used as an operator algebra."""
    code_no_witness = """
    theorem matrix_product_without_witness (A B : Matrix (Fin 2) (Fin 2) ℝ) :
        A * B = B * A := by
      sorry
    """
    v1 = screen_lean_content(code_no_witness)
    t16_1 = [v for v in v1 if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert len(t16_1) >= 1
    assert "lacks an explicit non-commutativity witness" in t16_1[0].message

    code_with_witness = """
    def matA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def matB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem mat_noncomm : matA * matB ≠ matB * matA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [matA, matB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    v2 = screen_lean_content(code_with_witness)
    t16_2 = [v for v in v2 if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert len(t16_2) == 0

    code_name_only = """
    theorem matrix_product_without_witness (A B : Matrix (Fin 2) (Fin 2) ℝ) :
        A * B = B * A := by
      trivial
    theorem named_noncommutative : True := by trivial
    """
    v3 = screen_lean_content(code_name_only)
    t16_3 = [v for v in v3 if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert len(t16_3) >= 1

    assumed_witness = """
    theorem assumedWitness (A B : Matrix (Fin 2) (Fin 2) ℝ)
        (h : A * B ≠ B * A) : A * B ≠ B * A := h
    """
    v4 = screen_lean_content(assumed_witness)
    assert any(v.trap_id == "T16" and "Witness" in v.trap_name for v in v4)

    aliased_assumption = """
    abbrev NoncommClaim (A B : Matrix (Fin 2) (Fin 2) ℝ) := A * B ≠ B * A
    theorem assumedAlias (A B : Matrix (Fin 2) (Fin 2) ℝ)
        (h : NoncommClaim A B) : A * B ≠ B * A := h
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(aliased_assumption)
    )

    false_elimination = """
    def A : Matrix (Fin 2) (Fin 2) ℝ := 0
    def B : Matrix (Fin 2) (Fin 2) ℝ := 0
    theorem falseWitness (h : False) : A * B ≠ B * A := False.elim h
    """
    assert not _has_closed_noncommutativity_witness(false_elimination)


def test_t16_tracks_ambient_matrix_binders_and_local_type_aliases():
    ambient = """
    variable (A B : Matrix (Fin 2) (Fin 2) ℝ)
    theorem ambient_commutativity_claim : A * B = B * A := by ring
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(ambient)
    )

    aliased = """
    abbrev Op := Matrix (Fin 2) (Fin 2) ℝ
    def operatorProduct (A B : Op) := A * B
    theorem claimed_commutativity (A B : Op) : A * B = B * A := by
      simp [operatorProduct]
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(aliased)
    )


def test_t16_function_valued_matrix_operands_require_a_carrier_witness():
    code = """
    def operatorProduct {α : Type} (f g : α → Matrix (Fin 2) (Fin 2) ℝ)
        (x y : α) := f x * g y
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )


def test_t16_ignores_unrelated_class_token_when_witness_is_independent():
    code = """
    class Provider where
      witness : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ), A * B ≠ B * A
    def E01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def E10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem independentWitness [Provider] : E01 * E10 ≠ E10 * E01 := by
      let _ := (inferInstance : Provider)
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [E01, E10, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    assert not any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )

def test_t16_ignores_unused_class_witness_with_aliased_other_carrier():
    code = """
    abbrev OtherOp := Matrix (Fin 3) (Fin 3) ℝ
    class Provider where
      witness : ∀ (A B : OtherOp), A * B ≠ B * A
    def E01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def E10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem independentWitness [Provider] : E01 * E10 ≠ E10 * E01 := by
      let _ := Provider.witness
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [E01, E10, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    assert not any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )

    dependent = """
    class SameCarrierProvider where
      witness : ∀ (A B : Matrix (Fin 2) (Fin 2) ℝ), A * B ≠ B * A
    def F01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def F10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem borrowedWitness [SameCarrierProvider] : F01 * F10 ≠ F10 * F01 := by
      let _ := SameCarrierProvider.witness F01 F10; exact SameCarrierProvider.witness F01 F10
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(dependent)
    )


def test_t16_tracks_applied_and_projected_matrix_operands():
    code = """
    abbrev Op := Matrix (Fin 2) (Fin 2) ℝ
    variable (f g : Nat → Op)
    theorem applied_commutativity (x y : Nat) : f x * g y = g y * f x := by
      ring
    """
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )


def test_t16_cartan_coefficient_matrix_is_not_operator_algebra():
    code = """
    def cartanMatrix : Matrix (Fin 4) (Fin 4) ℤ := fun i j => dot (root i) (root j)
    theorem cartan_diagonal (i : Fin 4) : cartanMatrix i i = 2 := by
      exact root_norm i
    theorem cartan_symmetric : Matrix.transpose cartanMatrix = cartanMatrix := by
      ext i j
      simp [cartanMatrix, dot, mul_comm]
    """
    violations = screen_lean_content(code)
    t16 = [v for v in violations if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16 == []


def test_t16_accepts_closed_witness_parametrized_by_matrix_dimension():
    code = """
    def matrixUnit01 {n : Nat} : Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
      Matrix.single 0 1 1
    def matrixUnit10 {n : Nat} : Matrix (Fin 2) (Fin 2) (SplitClNNAlg n) :=
      Matrix.single 1 0 1
    def operatorProduct {n : Nat}
        (A B : Matrix (Fin 2) (Fin 2) (SplitClNNAlg n)) := A * B
    theorem dimensionwiseWitness {n : Nat} :
        matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
      intro h
      have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
      norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.single_apply] at h00
    """
    assert _has_closed_noncommutativity_witness(code)


def test_t16_resolves_imported_concrete_noncommutativity_witness():
    code = """
    import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
    def operatorProduct (A B : Matrix (Fin 2) (Fin 2) ℝ) := A * B
    """
    violations = screen_lean_content(code, filename=__file__)
    t16 = [v for v in violations if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16 == []

    unresolved = code.replace(
        "InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness",
        "Fake.NoncommutativeWitness",
    )
    violations = screen_lean_content(unresolved, filename=__file__)
    t16 = [v for v in violations if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16

    mismatched_carrier = """
    import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
    def operatorProduct (A B : Matrix (Fin 3) (Fin 3) ℚ) := A * B
    """
    violations = screen_lean_content(mismatched_carrier, filename=__file__)
    assert any(v.trap_id == "T16" and "Witness" in v.trap_name for v in violations)


def test_t16_imported_witness_requires_exported_code_not_comments():
    commented = """
    /- theorem fake (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B ≠ B * A := by sorry -/
    """
    private = """
    private theorem fake (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B ≠ B * A := by
      exact sorry
    """
    assert not _has_closed_noncommutativity_witness(commented, exported_only=True)
    assert not _has_closed_noncommutativity_witness(private, exported_only=True)

    protected = """
    def matrixUnit01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def matrixUnit10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    protected theorem publicWitness :
        matrixUnit01 * matrixUnit10 ≠ matrixUnit10 * matrixUnit01 := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [matrixUnit01, matrixUnit10, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    assert _has_closed_noncommutativity_witness(protected, exported_only=True)


def test_t16_local_witness_must_match_operator_carrier():
    code = """
    def targetProduct (A B : Matrix (Fin 2) (Fin 2) ℂ) := A * B
    def realA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def realB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem real_noncomm : realA * realB ≠ realB * realA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [realA, realB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert len(t16) == 1


def test_t16_lowercase_operator_carrier_does_not_borrow_other_carrier_witness():
    code = """
    def targetProduct (a b : Matrix (Fin 2) (Fin 2) ℂ) := a * b
    def applyTarget (a : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) := Matrix.mulVec a v
    def realA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def realB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem real_noncomm : realA * realB ≠ realB * realA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [realA, realB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert len(t16) == 1


def test_t16_requires_witness_coverage_for_each_matrix_carrier():
    code = """
    def realProduct (A B : Matrix (Fin 2) (Fin 2) ℝ) := A * B
    def complexProduct (C D : Matrix (Fin 2) (Fin 2) ℂ) := C * D
    def realA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def realB : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    theorem real_noncomm : realA * realB ≠ realB * realA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
      norm_num [realA, realB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16


def test_t16_matrix_carrier_keeps_multi_token_coefficient_type():
    code = """
    def targetProduct (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) := a * b
    def wrongA : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 0, 0]
    def wrongB : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 0; 1, 0]
    theorem wrong_ring_noncomm : wrongA * wrongB ≠ wrongB * wrongA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 2) => M 0 0) h
      norm_num [wrongA, wrongB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16


def test_t16_nested_coefficient_type_mismatch_is_rejected():
    code = """
    def targetProduct (a b : Matrix (Fin 2) (Fin 2) (Polynomial (ZMod 3))) := a * b
    def wrongA : Matrix (Fin 2) (Fin 2) (Polynomial (ZMod 2)) := 0
    def wrongB : Matrix (Fin 2) (Fin 2) (Polynomial (ZMod 2)) := 0
    theorem wrong_ring_noncomm : wrongA * wrongB ≠ wrongB * wrongA := by
      intro h
      exact absurd h (by decide)
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16


def test_t16_ignores_unrelated_matrix_binders_in_product_declaration():
    code = """
    def complexMul (A B : Matrix (Fin 2) (Fin 2) ℂ)
        (C : Matrix (Fin 2) (Fin 2) ℝ) := A * B
    def complexA : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    def complexB : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
    theorem complex_noncomm : complexA * complexB ≠ complexB * complexA := by
      intro h
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
      norm_num [complexA, complexB, Matrix.mul_apply, Fin.sum_univ_two] at h00
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16 == []


def test_t16_rejects_local_typeclass_that_supplies_noncommutativity_witness():
    code = """
    def A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    def B : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    class Provider where
      witness : A * B ≠ B * A
    theorem fake [Provider] : A * B ≠ B * A := Provider.witness
    """
    assert not _has_closed_noncommutativity_witness(
        code, required_carriers={("2", "2", "ℝ")}
    )
    assert any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )


def test_t16_scalar_product_does_not_activate_matrix_witness_gate():
    code = """
    def gram : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
    theorem scalar_mul_comm (a b : ℤ) : a * b = b * a := by omega
    """
    assert not any(
        v.trap_id == "T16" and "Witness" in v.trap_name
        for v in screen_lean_content(code)
    )


def test_t16_imported_witness_must_match_lowercase_operator_carrier():
    code = """
    import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
    def targetProduct (a b : Matrix (Fin 2) (Fin 2) UncheckedRing) := a * b
    def applyTarget (a : Matrix (Fin 2) (Fin 2) UncheckedRing) (v : Fin 2 → UncheckedRing) := Matrix.mulVec a v
    """
    t16 = [
        v for v in screen_lean_content(code, filename=__file__)
        if v.trap_id == "T16" and "Witness" in v.trap_name
    ]
    assert len(t16) == 1


def test_t16_imported_witness_must_cover_every_matrix_dimension():
    code = """
    import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
    def complexProduct (A B : Matrix (Fin 2) (Fin 2) ℂ) := A * B
    def largerProduct (C D : Matrix (Fin 3) (Fin 3) ℝ) := C * D
    """
    t16 = [
        v for v in screen_lean_content(code, filename=__file__)
        if v.trap_id == "T16" and "Witness" in v.trap_name
    ]
    assert t16


def test_t16_witness_result_carrier_is_bound_to_its_operands():
    imported_source = """
    def unrelated : Matrix (Fin 2) (Fin 2) ℝ := 0
    theorem falseCarrierWitness (A B : Matrix (Fin 3) (Fin 3) ℝ) :
        A * B ≠ B * A := by
      sorry
    """
    assert not _has_closed_noncommutativity_witness(
        imported_source,
        exported_only=True,
        required_carriers={("2", "2", "ℝ")},
    )

    section_assumption = """
    variable (A B : Matrix (Fin 2) (Fin 2) ℝ)
    theorem borrowedWitness : A * B ≠ B * A := by assumption
    """
    assert not _has_closed_noncommutativity_witness(section_assumption)


def test_t16_rejects_witness_proof_forwarding_to_local_axiom():
    axiom_backed = """
    def A : Matrix (Fin 2) (Fin 2) ℝ := 0
    def B : Matrix (Fin 2) (Fin 2) ℝ := 0
    axiom impossibleFact : False
    def fakeHelper : A * B ≠ B * A := False.elim impossibleFact
    theorem fakeNoncommWitness : A * B ≠ B * A := fakeHelper
    """
    assert not _has_closed_noncommutativity_witness(axiom_backed)

    t16 = [
        v for v in screen_lean_content(axiom_backed)
        if v.trap_id == "T16" and "Witness" in v.trap_name
    ]
    assert t16


def test_t16_block_construction_alone_is_not_operator_product():
    code = """
    def assembled (A B C D : Matrix (Fin 2) (Fin 2) ℝ) := Matrix.fromBlocks A B C D
    """
    t16 = [v for v in screen_lean_content(code) if v.trap_id == "T16" and "Witness" in v.trap_name]
    assert t16 == []


def test_t16_stationary_weight_scalar_product_is_not_a_matrix_product():
    code = """
    theorem stationary_weight (D : Module.End ℝ (Fin 2 → ℝ))
        (π : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) :
        (∑ i, π i * P i 0) = 1 := by
      simp
    """
    witness_violations = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Witness" in violation.trap_name
    ]
    assert witness_violations == []


def test_t16_does_not_combine_operator_names_from_separate_declarations():
    code = """
    def unusedMatrix : Matrix (Fin 2) (Fin 2) ℝ := 0
    theorem operator_a (A : Module.End ℝ (Fin 2 → ℝ)) : True := trivial
    theorem operator_b (B : Module.End ℝ (Fin 2 → ℝ)) : True := trivial
    theorem scalar_commutes (A B : ℝ) : A * B = B * A := mul_comm _ _
    """
    witness_violations = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Witness" in violation.trap_name
    ]
    assert witness_violations == []


def test_t16_local_scalar_binders_shadow_operator_section_variables():
    code = """
    def unusedMatrix : Matrix (Fin 2) (Fin 2) ℝ := 0
    variable (A B : Module.End ℝ (Fin 2 → ℝ))
    theorem scalar_commutes (A B : ℝ) : A * B = B * A := mul_comm _ _
    """
    witness_violations = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Witness" in violation.trap_name
    ]
    assert witness_violations == []


def test_detect_trap_t16_tactic_misuse_on_operators():
    """Verify Trap T16: direct application of scalar/commutative tactics on operator carriers."""
    code_matrix_ring = """
    theorem bad_mat_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B = B * A := by
      ring
    """
    v1 = screen_lean_content(code_matrix_ring)
    t16_1 = [v for v in v1 if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name]
    assert len(t16_1) >= 1
    assert "unprojected operator carrier" in t16_1[0].message

    anonymous_example = """
    example (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B = B * A := by
      ring
    """
    anonymous = [
        v for v in screen_lean_content(anonymous_example)
        if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
    ]
    assert anonymous

    abbrev_proof = """
    abbrev badOperatorClaim (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B = B * A := by
      ring
    """
    assert any(
        v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
        for v in screen_lean_content(abbrev_proof)
    )

    adjacent_examples = """
    example (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B = B * A := by
      trivial
    example (A B : Matrix (Fin 2) (Fin 2) ℝ) : A * B = B * A := by
      ring
    """
    assert any(
        v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
        for v in screen_lean_content(adjacent_examples)
    )

    code_end_linarith = """
    theorem bad_end (A B : End ℝ V) : A * B = B * A := by
      linarith
    """
    v2 = screen_lean_content(code_end_linarith)
    t16_2 = [v for v in v2 if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name]
    assert len(t16_2) >= 1

    code_inline_have = """
    theorem bad_have (A B : Matrix (Fin 2) (Fin 2) ℝ) : A = B := by
      have hcomm : A * B = B * A := by ring
      exact sorry
    """
    v3 = screen_lean_content(code_inline_have)
    t16_3 = [v for v in v3 if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name]
    assert len(t16_3) >= 1

    code_alias = """
    abbrev Op := Matrix (Fin 2) (Fin 2) ℝ
    theorem alias_bad (A B : Op) : A * B = B * A := by
      ring
    """
    v4 = screen_lean_content(code_alias)
    assert any(v.trap_id == "T16" and "Tactic Misuse" in v.trap_name for v in v4)

    code_mixed = """
    theorem mixed (A B : Matrix (Fin 2) (Fin 2) ℝ)
        (C : Matrix (Fin 2) (Fin 4) ℝ) :
        A * B = B * A ∧ pluckerMinor C 0 1 = 0 := by
      ring
    """
    v5 = screen_lean_content(code_mixed)
    assert any(v.trap_id == "T16" and "Tactic Misuse" in v.trap_name for v in v5)


def test_t16_allows_scalar_inner_product_proofs_in_matrix_theorems():
    code = """
    theorem quadratic_form_nonneg (A : Matrix (Fin 2) (Fin 2) ℚ) (x : Fin 2 → ℚ) :
        0 ≤ innerProduct x ((A * Aᵀ).mulVec x) := by
      have h0 : innerProduct x ((A * Aᵀ).mulVec x) = 0 := by linarith
      exact h0.le
    """
    violations = screen_lean_content(code)
    misuse = [
        v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
    ]
    assert misuse == []


def test_t16_scalar_projection_name_cannot_shadow_operator_carrier():
    code = """
    theorem shadowed_inner_product
        (innerProduct : Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ)
        (A B : Matrix (Fin 2) (Fin 2) ℚ) : A * B = B * A := by
      have h : innerProduct A B = A * B := by ring
      ring
    """
    misuse = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse


def test_t16_scalar_projection_name_cannot_be_an_implicit_operator_binder():
    code = """
    theorem implicit_shadow
        {innerProduct : Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ}
        (A B : Matrix (Fin 2) (Fin 2) ℚ) : A * B = B * A := by
      have h : innerProduct A B = A * B := by ring
      ring
    """
    misuse = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse


def test_t16_implicit_scalar_name_does_not_hide_matrix_valued_target():
    code = """
    theorem implicit_matrix_shadow
        {innerProduct : Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ}
        (A B C : Matrix (Fin 2) (Fin 2) ℚ) : innerProduct A B = C := by
      ring
    """
    misuse = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse


def test_t16_section_variable_cannot_shadow_scalar_projection_name():
    code = """
    section
    variable (innerProduct : Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ)
    variable (A B C : Matrix (Fin 2) (Fin 2) ℚ)
    theorem section_shadow : innerProduct A B = C := by
      ring
    end
    """
    misuse = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse


def test_t16_closed_section_variable_does_not_shadow_global_scalar_projection():
    code = """
    def innerProduct (x y : Fin 2 → ℚ) : ℚ := ∑ i, x i * y i
    section
    variable (innerProduct : Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ)
    end
    theorem scalar_projection_after_section
        (A : Matrix (Fin 2) (Fin 2) ℚ) (x : Fin 2 → ℚ) :
        0 ≤ innerProduct x ((A * Aᵀ).mulVec x) := by
      linarith
    """
    misuse = [
        violation for violation in screen_lean_content(code)
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse == []


def test_t16_direct_scalar_goal_may_contain_matrix_product_projection():
    code = """
    theorem quadratic_form_nonneg (A : Matrix (Fin 2) (Fin 2) ℚ) (x : Fin 2 → ℚ) :
        0 ≤ innerProduct x ((A * Aᵀ).mulVec x) := by
      linarith
    """
    violations = screen_lean_content(code)
    misuse = [
        violation for violation in violations
        if violation.trap_id == "T16" and "Tactic Misuse" in violation.trap_name
    ]
    assert misuse == []


def test_t16_allows_scalar_local_helpers_in_matrix_theorems():
    code = """
    theorem matrix_identity (A : Matrix (Fin 2) (Fin 2) ℚ) : A * 1 = A := by
      have h_coeff : (2 : ℚ) + 3 = 5 := by
        ring
      simpa [h_coeff]
    """
    violations = screen_lean_content(code)
    misuse = [
        v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
    ]
    assert misuse == []


def test_t16_allows_scalar_calc_after_matrix_entry_projection():
    code = """
    theorem scaled_entry (A : Matrix (Fin 2) (Fin 2) ℚ)
        (pivotVal : ℚ) (pr j : Fin 2) :
        (A * 1) pr j = pivotVal * A pr j := by
      calc
        (1 + (pivotVal⁻¹ - 1)) * pivotVal = pivotVal⁻¹ * pivotVal := by ring
        _ = 1 := by rw [inv_mul_cancel (by assumption)]
    """
    violations = screen_lean_content(code)
    misuse = [
        v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
    ]
    assert misuse == []


def test_t16_allows_scalar_calc_in_let_indexed_matrix_result():
    code = """
    theorem matrix_entry (A : Matrix (Fin 2) (Fin 2) ℚ) (x : ℚ) :
        let B : Matrix (Fin 2) (Fin 2) ℚ := A
        B 0 0 = A 0 0 := by
      calc
        (1 + (x - 1)) * 1 = x := by ring
        _ = x := rfl
    """
    violations = screen_lean_content(code)
    misuse = [
        v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name
    ]
    assert misuse == []


def test_t16_valid_ext_with_ring_allowed():
    """Verify that extensionality-projected matrix proofs with ring are allowed."""
    code = """
    import proofs.WavefrontKMSKleinDuality
    theorem mat_add_comm (A B : Matrix (Fin 2) (Fin 2) ℝ) : A + B = B + A := by
      ext i j
      ring
    """
    violations = screen_lean_content(code)
    t16_misuse = [v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name]
    assert len(t16_misuse) == 0

    code_scalar_plucker = """
    theorem plucker_scalar (C : Matrix (Fin 2) (Fin 4) ℝ) :
        pluckerMinor C 0 1 * pluckerMinor C 2 3 = 0 := by
      ring
    """
    violations = screen_lean_content(code_scalar_plucker)
    t16_misuse = [v for v in violations if v.trap_id == "T16" and "Tactic Misuse" in v.trap_name]
    assert t16_misuse == []


def test_screen_wavefront_kms_klein_duality_clean():
    """Verify proofs/WavefrontKMSKleinDuality.lean passes screener cleanly with 0 errors."""
    repo_root = Path(__file__).resolve().parent.parent
    target = repo_root / "proofs" / "WavefrontKMSKleinDuality.lean"
    assert target.is_file()
    violations = screen_lean_file(target)
    errors = [v for v in violations if v.severity == "ERROR"]
    assert len(errors) == 0, f"Expected 0 errors, found: {errors}"


def test_qms_source_gate_rejects_repo_axioms_and_holes_but_ignores_comments():
    code = '''
/- axiom commentAxiom : True
   theorem fake : True := by sorry -/
axiom localAxiom : True
theorem unfinished : True := by
  sorry
'''
    violations = check_authored_axioms_and_holes(code)
    assert [v.trap_id for v in violations] == ["QMS_AXIOM", "QMS_HOLE"]


def test_qms_source_gate_ignores_admit_in_trace_class_names():
    code = """
    initialize registerTraceClass `DAG.Morphism.admit
    def record : Unit := by
      trace[DAG.Morphism.admit] "diagnostic only"
      exact ()
    """
    assert check_authored_axioms_and_holes(code) == []


def test_qms_source_gate_ignores_foundational_axiom_names_in_comments():
    code = "-- allowed kernel footprint: propext, Classical.choice, Quot.sound\n"
    assert check_authored_axioms_and_holes(code) == []


def test_qms_source_gate_allows_kernel_placeholder_detector_references():
    code = """
    def isKernelPlaceholder (n : Name) : Bool := n == ``sorryAx || n == ``admitAx || n == ``Lean.sorryAx
    theorem finished : True := by trivial
    """
    assert check_authored_axioms_and_holes(code) == []


def test_qms_source_gate_rejects_kernel_placeholder_proof_terms():
    for term in ("sorryAx", "_root_.sorryAx", "_root_.admitAx", "Lean.sorryAx", "Lean.admitAx"):
        code = f"theorem fake : True := ({term} : True)"
        violations = check_authored_axioms_and_holes(code)
        assert [v.trap_id for v in violations] == ["QMS_HOLE"]
