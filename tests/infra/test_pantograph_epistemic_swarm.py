from datetime import datetime, timedelta, timezone
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
from tools.infra.pantograph_epistemic_swarm import (
    COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE,
    COGNITIVE_MODE_MISSING_LEMMA,
    COGNITIVE_MODE_TIMEOUT,
    COGNITIVE_MODE_TYPE_MISMATCH,
    DEFAULT_SUGGESTED_ACTIONS,
    CandidatePacket,
    EpistemicSwarmEngine,
    MockEpistemicSwarmStore,
    MockPantographReplSession,
    PantographReplSession,
    build_socratic_packet,
    classify_question_type,
    extract_goal_state_from_messages,
    format_goal_ast,
    infer_cognitive_mode_and_actions,
    run_dry_run_verification,
)


def test_candidate_packet_parsing() -> None:
    # 1. From standard dictionary with formal_target object
    data1 = {
        "id": "cand-001",
        "kind": "TheoremCandidatePacket",
        "formal_target": {
            "lean_statement": "1 + 1 = 2",
            "claim": "Arithmetic",
        },
        "candidate_tactics": ["rfl"],
    }
    cand1 = CandidatePacket.from_dict(data1)
    assert cand1.packet_id == "cand-001"
    assert cand1.formal_target == "1 + 1 = 2"
    assert cand1.tactics == ["rfl"]

    # 2. From raw expr and string tactics
    data2 = {
        "expr": "forall (n : Nat), n = n",
        "tactics": "intro n\nrfl\n",
    }
    cand2 = CandidatePacket.from_dict(data2)
    assert cand2.formal_target == "forall (n : Nat), n = n"
    assert cand2.tactics == ["intro n", "rfl"]


def test_extract_goal_state_from_messages() -> None:
    messages = [
        {
            "severity": "error",
            "data": (
                "Tactic `rfl` failed: The left-hand side is not definitionally equal\n"
                "n : Nat\n"
                "h : n > 0\n"
                "⊢ n + 1 = 1 + n"
            ),
        }
    ]
    extracted = extract_goal_state_from_messages(messages)
    assert "n : Nat" in extracted
    assert "⊢ n + 1 = 1 + n" in extracted


def test_format_goal_ast() -> None:
    goal_obj = {
        "target": {"pp": "n + 1 = 1 + n"},
        "vars": [
            {"userName": "n", "type": {"pp": "Nat"}},
            {"userName": "h", "type": {"pp": "n > 0"}},
        ],
    }
    formatted = format_goal_ast(goal_obj)
    assert "n : Nat" in formatted
    assert "h : n > 0" in formatted
    assert "⊢ n + 1 = 1 + n" in formatted


def test_classify_question_type() -> None:
    assert classify_question_type("parse error", is_elaboration=True) == "definition_pressure"
    assert classify_question_type("Expected the goal to be a binary relation") == "counterexample_pressure"
    assert classify_question_type("unknown identifier 'omega'") == "hidden_hypothesis"
    assert classify_question_type("type mismatch") == "admissibility_pressure"
    assert classify_question_type("tactic failed") == "falsification_pressure"


def test_socratic_packet_schema_compliance() -> None:
    schema_store = build_store()
    schema = SCHEMA_BY_KIND["SocraticQuestionPacket"]

    pkt = build_socratic_packet(
        candidate_id="cand-123",
        session_id="session-xyz",
        formal_target="1 + 1 = 2",
        question="Why did tactic fail?",
        question_type="counterexample_pressure",
        exact_goal_state="⊢ 1 + 1 = 2",
        failed_tactic="rfl",
        error_message="mismatch",
        state_id=0,
        request_key="prq_1",
        response_key="prs_1",
    )
    errs = validate_packet(pkt, schema, schema_store)
    assert not errs, f"Validation errors: {errs}"
    assert pkt["kind"] == "SocraticQuestionPacket"
    assert pkt["status"] == "open"
    assert pkt["authority"] == "semantic"
    assert pkt["epistemic_layer"] == "cognitive_process"


def test_engine_process_candidate_proved() -> None:
    store = MockEpistemicSwarmStore("sess-test-proved")
    store.start(["repl", "Init"], "1.0", None)
    repl = MockPantographReplSession(store)
    engine = EpistemicSwarmEngine(repl, store)

    cand = CandidatePacket("cand-p", "TheoremCandidatePacket", "1 + 1 = 2", ["rfl"])
    res = engine.process_candidate(cand)
    assert res.status == "proved"
    assert res.final_state_id == 1
    assert res.socratic_packet is None
    assert len(store.collections["pantograph_requests"]) == 2
    assert len(store.collections["pantograph_responses"]) == 2
    assert len(store.collections["pantograph_states"]) == 2


def test_engine_process_candidate_tactic_failure() -> None:
    store = MockEpistemicSwarmStore("sess-test-fail")
    store.start(["repl", "Init"], "1.0", None)
    repl = MockPantographReplSession(store)
    engine = EpistemicSwarmEngine(repl, store)

    cand = CandidatePacket("cand-f", "TheoremCandidatePacket", "forall (n : Nat), n + 1 = 1 + n", ["rfl"])
    res = engine.process_candidate(cand)
    assert res.status == "tactic_failure"
    assert res.socratic_packet is not None
    assert res.socratic_packet["failed_tactic"] == "rfl"
    assert "⊢ n + 1 = 1 + n" in res.socratic_packet["exact_goal_state"]
    assert len(store.collections["pantograph_socratic_questions"]) == 1


def test_engine_process_candidate_elaboration_failure() -> None:
    store = MockEpistemicSwarmStore("sess-test-elab")
    store.start(["repl", "Init"], "1.0", None)
    repl = MockPantographReplSession(store)
    engine = EpistemicSwarmEngine(repl, store)

    cand = CandidatePacket("cand-e", "TheoremCandidatePacket", "1 + = 2", ["rfl"])
    res = engine.process_candidate(cand)
    assert res.status == "elaboration_failure"
    assert res.socratic_packet is not None
    assert res.socratic_packet["question_type"] == "definition_pressure"
    assert "ELABORATION_ERROR" in res.socratic_packet["exact_goal_state"]
    assert len(store.collections["pantograph_socratic_questions"]) == 1


def test_extract_typed_diagnostic() -> None:
    from tools.infra.pantograph_epistemic_swarm import (
        DIAGNOSTIC_MISSING_LEMMA,
        DIAGNOSTIC_TYPE_MISMATCH,
        DIAGNOSTIC_UNFOLDING_BLOCKED,
        DIAGNOSTIC_INSUFFICIENT_HYPOTHESIS,
        extract_typed_diagnostic,
    )
    # 1. Type mismatch
    err1 = (
        "The left-hand side\n"
        "  n + 1\n"
        "is not definitionally equal to the right-hand side\n"
        "  1 + n\n"
    )
    kind1, p1 = extract_typed_diagnostic(err1)
    assert kind1 == DIAGNOSTIC_TYPE_MISMATCH
    assert p1["inferred"] == "n + 1"
    assert p1["expected"] == "1 + n"

    # 2. Missing lemma
    err2 = "unknown identifier 'MyMissingLemma'"
    kind2, p2 = extract_typed_diagnostic(err2)
    assert kind2 == DIAGNOSTIC_MISSING_LEMMA
    assert p2["missing_identifier"] == "MyMissingLemma"

    # 3. Unfolding blocked
    err3 = "cannot unfold 'NonUnfoldableDef'"
    kind3, p3 = extract_typed_diagnostic(err3)
    assert kind3 == DIAGNOSTIC_UNFOLDING_BLOCKED
    assert p3["opaque_constant"] == "NonUnfoldableDef"

    # 4. Insufficient hypothesis
    err4 = "tactic 'apply' failed, no goals to solve"
    kind4, _ = extract_typed_diagnostic(err4, "⊢ P ∧ Q")
    assert kind4 == DIAGNOSTIC_INSUFFICIENT_HYPOTHESIS


def test_normalize_goal_alpha_and_hash() -> None:
    from tools.infra.pantograph_epistemic_swarm import compute_subgoal_hash, normalize_goal_alpha

    # Goal 1 with variables x, y
    g1 = "x : Nat\ny : Nat\n⊢ x + y = y + x"
    # Goal 2 with variables a, b (alpha-equivalent)
    g2 = "a : Nat\nb : Nat\n⊢ a + b = b + a"

    norm1 = normalize_goal_alpha(g1)
    norm2 = normalize_goal_alpha(g2)
    assert norm1 == norm2, f"Alpha normalization mismatch: {norm1} != {norm2}"
    assert compute_subgoal_hash(g1) == compute_subgoal_hash(g2)


def test_engine_process_candidate_subgoal_cache_hit() -> None:
    store = MockEpistemicSwarmStore("sess-cache-test")
    store.start(["repl", "Init"], "1.0", None)
    repl = MockPantographReplSession(store)
    engine = EpistemicSwarmEngine(repl, store)

    # First run: proves and populates cache
    cand = CandidatePacket("cand-1", "TheoremCandidatePacket", "1 + 1 = 2", ["rfl"])
    res1 = engine.process_candidate(cand)
    assert res1.status == "proved"
    assert len(store.collections["pantograph_subgoal_cache"]) == 1

    # Second run: empty tactics, hits cache directly!
    cand_repeat = CandidatePacket("cand-2", "TheoremCandidatePacket", "1 + 1 = 2", [])
    res2 = engine.process_candidate(cand_repeat)
    assert res2.status == "proved_via_subgoal_cache"
    assert res2.executed_tactics == ["rfl"]


def test_build_socratic_packet_enriched_fields() -> None:
    schema_store = build_store()
    schema = SCHEMA_BY_KIND["SocraticQuestionPacket"]

    # 1. Automatic inference for type mismatch
    pkt1 = build_socratic_packet(
        candidate_id="cand-type-mismatch",
        session_id="sess-001",
        formal_target="n = n + 1",
        question="Why did rfl fail?",
        question_type="falsification_pressure",
        exact_goal_state="⊢ n = n + 1",
        failed_tactic="rfl",
        error_message="The left-hand side n is not definitionally equal to right-hand side n + 1",
    )
    assert pkt1["tactic_attempted"] == "rfl"
    assert pkt1["cognitive_mode"] == COGNITIVE_MODE_TYPE_MISMATCH
    assert pkt1["lean_error_code"] == "LEAN_TYPE_MISMATCH"
    assert pkt1["suggested_actions"] == ["CAST_EQUALITY", "COERCE_TYPES", "REWRITE_DEF"]
    assert len(pkt1["parent_goal_hash"]) == 64
    errs1 = validate_packet(pkt1, schema, schema_store)
    assert not errs1, f"Validation errors: {errs1}"

    # 2. Automatic inference for missing lemma
    pkt2 = build_socratic_packet(
        candidate_id="cand-missing-lemma",
        session_id="sess-002",
        formal_target="Complex.I * Complex.I = -1",
        question="Why did simp fail?",
        question_type="hidden_hypothesis",
        exact_goal_state="⊢ Complex.I * Complex.I = -1",
        failed_tactic="simp [I_sq]",
        error_message="unknown identifier 'I_sq'",
    )
    assert pkt2["cognitive_mode"] == COGNITIVE_MODE_MISSING_LEMMA
    assert pkt2["lean_error_code"] == "LEAN_UNKNOWN_IDENTIFIER"
    assert pkt2["suggested_actions"] == ["EXTRACT_LEMMAS", "IMPORT_MATHLIB_MODULE", "SEARCH_LEANSEARCH"]
    errs2 = validate_packet(pkt2, schema, schema_store)
    assert not errs2, f"Validation errors: {errs2}"

    # 3. Explicit override for insufficient carrier structure
    pkt3 = build_socratic_packet(
        candidate_id="cand-carrier",
        session_id="sess-003",
        formal_target="dist x y = dist y x",
        question="How to synthesize metric space?",
        question_type="admissibility_pressure",
        exact_goal_state="⊢ dist x y = dist y x",
        failed_tactic="apply MetricSpace.dist_comm",
        error_message="failed to synthesize instance MetricSpace α",
        cognitive_mode=COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE,
        suggested_actions=["EXTRACT_LEMMAS", "WEAKEN_TARGET", "SUBSTITUTE_MODEL"],
    )
    assert pkt3["cognitive_mode"] == COGNITIVE_MODE_INSUFFICIENT_CARRIER_STRUCTURE
    assert pkt3["suggested_actions"] == ["EXTRACT_LEMMAS", "WEAKEN_TARGET", "SUBSTITUTE_MODEL"]
    errs3 = validate_packet(pkt3, schema, schema_store)
    assert not errs3, f"Validation errors: {errs3}"


def test_process_isolation_tactic_timeout() -> None:
    schema_store = build_store()
    schema = SCHEMA_BY_KIND["SocraticQuestionPacket"]

    store = MockEpistemicSwarmStore("sess-timeout-test")
    store.start(["repl", "Init"], "1.0", None)
    repl = MockPantographReplSession(store, step_timeout=5.0)
    engine = EpistemicSwarmEngine(repl, store, step_timeout=5.0)

    # Candidate with a diverging / non-terminating tactic
    cand = CandidatePacket("cand-timeout", "TheoremCandidatePacket", "forall (x : Nat), x = x", ["timeout"])
    res = engine.process_candidate(cand)

    assert res.status == "tactic_failure"
    assert res.socratic_packet is not None
    assert "timeout" in (res.error_message or "").lower()
    assert res.socratic_packet["cognitive_mode"] == COGNITIVE_MODE_TIMEOUT
    assert res.socratic_packet["lean_error_code"] == "LEAN_TIMEOUT"
    assert res.socratic_packet["tactic_attempted"] == "timeout"
    assert "SIMPLIFY_TACTIC" in res.socratic_packet["suggested_actions"]

    errs = validate_packet(res.socratic_packet, schema, schema_store)
    assert not errs, f"Validation errors on timeout packet: {errs}"


def test_process_isolation_reader_timeout_unit() -> None:
    import os
    r_fd, w_fd = os.pipe()
    try:
        r_file = os.fdopen(r_fd, "r")
        # Reading from empty pipe with 0.1s timeout should raise TimeoutError
        try:
            PantographReplSession.read_response_with_timeout(r_file, timeout=0.1)
            assert False, "Expected TimeoutError"
        except TimeoutError as exc:
            assert "timed out" in str(exc)
    finally:
        os.close(w_fd)


def test_epistemic_swarm_store_lease_and_ttl() -> None:
    session_id = "test-lease-session"
    store = MockEpistemicSwarmStore(session_id)
    store.start(["repl", "Init"], "1.0", None, ttl_seconds=180)

    # 1. Heartbeat session
    hb = store.heartbeat_session(session_id, ttl_seconds=180)
    assert hb["status"] == "active"
    assert hb["sessionId"] == session_id
    assert "lastHeartbeatAt" in hb
    assert "leaseExpiresAt" in hb

    # 2. Check active session is not expired
    now = datetime.now(timezone.utc)
    assert not store.is_session_expired(session_id, ttl_seconds=180, reference_time=now)
    assert len(store.check_expired_sessions(ttl_seconds=180, reference_time=now)) == 0

    # 3. Simulate passage of time past TTL
    future_time = now + timedelta(seconds=200)
    assert store.is_session_expired(session_id, ttl_seconds=180, reference_time=future_time)
    expired = store.check_expired_sessions(ttl_seconds=180, reference_time=future_time)
    assert len(expired) == 1
    assert expired[0]["sessionId"] == session_id
    assert expired[0]["isDeadlocked"] is True

    # 4. Reap deadlocked sessions
    reaped = store.reap_deadlocked_sessions(ttl_seconds=180, reference_time=future_time)
    assert len(reaped) == 1
    assert reaped[0]["status"] == "deadlocked"
    assert store.is_session_expired(session_id, reference_time=now)  # Status is deadlocked


def test_dry_run_verification_runner() -> None:
    assert run_dry_run_verification() is True


if __name__ == "__main__":
    test_candidate_packet_parsing()
    test_extract_goal_state_from_messages()
    test_format_goal_ast()
    test_classify_question_type()
    test_socratic_packet_schema_compliance()
    test_extract_typed_diagnostic()
    test_normalize_goal_alpha_and_hash()
    test_engine_process_candidate_proved()
    test_engine_process_candidate_tactic_failure()
    test_engine_process_candidate_elaboration_failure()
    test_engine_process_candidate_subgoal_cache_hit()
    test_build_socratic_packet_enriched_fields()
    test_process_isolation_tactic_timeout()
    test_process_isolation_reader_timeout_unit()
    test_epistemic_swarm_store_lease_and_ttl()
    test_dry_run_verification_runner()
    print("ALL 16 UNIT TESTS PASSED!")



