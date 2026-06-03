from __future__ import annotations

from pathlib import Path

from tools.infra import gepa_evolver
from tools.infra import gepa_real_eval


class FillingEvaluator(gepa_real_eval.RealEvaluator):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.compiled_path: Path | None = None
        self.compiled_text = ""

    def _run_hermes(self, skill_content, task, eval_path, original_lines):
        text = eval_path.read_text(encoding="utf-8")
        eval_path.write_text(text.replace("sorry", "trivial", 1), encoding="utf-8")
        return gepa_real_eval.HermesRun(output="filled")

    def _check_compiles(self, file_path, task):
        self.compiled_path = file_path
        self.compiled_text = file_path.read_text(encoding="utf-8")
        return True


def test_real_eval_uses_temp_file_and_preserves_original(tmp_path, monkeypatch) -> None:
    monkeypatch.setattr(gepa_real_eval, "_REPO", tmp_path)
    monkeypatch.setattr(gepa_real_eval, "CACHE_FILE", tmp_path / ".eval_cache.jsonl")

    target = tmp_path / "Target.lean"
    original = "theorem smoke : True := by\n  sorry\n"
    target.write_text(original, encoding="utf-8")

    task = gepa_real_eval.EvalTask(file="Target.lean", line=2, module="Target")
    evaluator = FillingEvaluator([task], compile_check=True, cache=False)

    result = evaluator.evaluate("replace simple goals with trivial")

    assert result.average_fitness == 1.0
    assert result.n_succeeded == 1
    assert target.read_text(encoding="utf-8") == original
    assert evaluator.compiled_path is not None
    assert evaluator.compiled_path != target
    assert "sorry" not in evaluator.compiled_text


def test_real_eval_in_place_mode_restores_original(tmp_path, monkeypatch) -> None:
    monkeypatch.setattr(gepa_real_eval, "_REPO", tmp_path)
    monkeypatch.setattr(gepa_real_eval, "CACHE_FILE", tmp_path / ".eval_cache.jsonl")

    target = tmp_path / "Target.lean"
    original = "theorem smoke : True := by\n  sorry\n"
    target.write_text(original, encoding="utf-8")

    task = gepa_real_eval.EvalTask(file="Target.lean", line=2, module="Target")
    evaluator = FillingEvaluator([task], compile_check=True, cache=False, isolated=False)

    result = evaluator.evaluate("replace simple goals with trivial")

    assert result.average_fitness == 1.0
    assert target.read_text(encoding="utf-8") == original
    assert evaluator.compiled_path == target


def test_real_evaluator_rejects_ambiguous_sorry_without_explicit_line(tmp_path, monkeypatch) -> None:
    monkeypatch.setattr(gepa_real_eval, "_REPO", tmp_path)
    monkeypatch.setattr(gepa_real_eval, "CACHE_FILE", tmp_path / ".eval_cache.jsonl")

    lean_file = tmp_path / "lean" / "Ambiguous.lean"
    lean_file.parent.mkdir(parents=True)
    lean_file.write_text(
        "import Init\n\ntheorem a : True := by\n  sorry\n\n"
        "theorem b : True := by\n  sorry\n",
        encoding="utf-8",
    )

    evaluator = gepa_real_eval.RealEvaluator(
        [gepa_real_eval.EvalTask(file="lean/Ambiguous.lean", line=0, module="Ambiguous")],
        cache=False,
    )
    result = evaluator.evaluate("skill")

    assert result.average_fitness == 0.0
    assert "Ambiguous sorry task" in result.task_results[0].error


def test_eval_task_normalizes_infogeometry_paths() -> None:
    task = gepa_real_eval.EvalTask(
        file="InfoGeometry/Analysis/Example.lean",
        line=3,
        module="InfoGeometry.Analysis.Example",
    )

    assert task.file == "lean/InfoGeometry/Analysis/Example.lean"


def test_gepa_rollback_archive_loads_highest_fitness_variant(tmp_path, monkeypatch) -> None:
    monkeypatch.setattr(gepa_evolver, "_REPO", tmp_path)

    gepa_evolver.save_rollback_archive(
        skill_name="lean-proof",
        skill_content="low fitness skill",
        fitness=0.25,
        generation=1,
    )
    gepa_evolver.save_rollback_archive(
        skill_name="lean-proof",
        skill_content="high fitness skill",
        fitness=0.75,
        generation=2,
    )

    assert gepa_evolver.load_best_skill("lean-proof") == "high fitness skill"


def test_gepa_extracts_candidate_instruction_from_pred_trace() -> None:
    class Signature:
        instructions = (
            "Respond to the task following these instructions:\n\n"
            "candidate skill body"
        )

    class Predictor:
        signature = Signature()

    inst = gepa_evolver.GEPAEvolver._extract_instructions_from_trace(
        [(Predictor(), {"task_input": "x"}, {"output": "y"})]
    )

    assert gepa_evolver.GEPAEvolver._instructions_to_skill(inst) == "candidate skill body"
