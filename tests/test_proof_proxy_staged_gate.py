from tools.quality.proof_proxy_staged_gate import aggregate_prop_constructors


def test_aggregate_prop_proof_wrapper_is_detected_without_name_keywords():
    source = """
structure Output : Prop where
  first_claim : FirstClaim
  second_claim : SecondClaim

theorem assemble_output : Output where
  first_claim := first_claim_proved
  second_claim := second_claim_proved
"""
    found = aggregate_prop_constructors(source)
    assert len(found) == 1
    assert found[0][0] == "Output"


def test_mathematical_predicate_structure_is_not_a_proof_bundle():
    source = """
structure IsDrazinOperator (A D : R) (k : Nat) : Prop where
  drazin_one : D * A * D = D
  comm : A * D = D * A
  index_law : A ^ (k + 1) * D = A ^ k
"""
    assert aggregate_prop_constructors(source) == []


def test_prop_structure_with_non_keyword_fields_is_caught_by_assembly():
    source = """
structure CarrierInvariant : Prop where
  alpha : Alpha
  beta : Beta

theorem build_invariant : CarrierInvariant where
  alpha := alpha_owner
  beta := beta_owner
"""
    assert aggregate_prop_constructors(source) == [("CarrierInvariant", "theorem build_invariant : CarrierInvariant where")]
