from __future__ import annotations

import os
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[1]
SCRIPT = REPO / "scripts" / "run_archon_superorganism.sh"


def write_fake_python(
    bin_dir: Path,
    invocation_log: Path,
    *,
    resolver_exit: int = 1,
    resolver_output: str = "",
) -> None:
    path = bin_dir / "python3"
    path.write_text(
        """
#!/usr/bin/env bash
set -euo pipefail

printf '[fake-python] %s\\n' "$*" >> "{log}"

case "${1}" in
  *resolve_startup_model_ids.py)
    echo "resolver requested" >> "{log}"
    {resolver_output}
    exit {resolver_exit}
    ;;
  *check_resident_model_endpoint.py)
    echo "endpoint probe requested" >> "{log}"
    exit 0
    ;;
  *)
    exec /usr/bin/python3 "$@"
    ;;
esac
""".replace("{log}", invocation_log.as_posix())
        .replace("{resolver_output}", resolver_output)
        .replace("{resolver_exit}", str(resolver_exit)),
        encoding="utf-8",
    )
    path.chmod(0o755)


def write_fake_archon(bin_dir: Path, env_log: Path) -> None:
    path = bin_dir / "archon"
    path.write_text(
        """
#!/usr/bin/env bash
echo "ARCHON_LEANSTRAL_MODEL=${ARCHON_LEANSTRAL_MODEL:-<missing>}" >> "{log}"
echo "ARCHON_PI_MODEL=${ARCHON_PI_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_LANE_ARCHON_LEANSTRAL_MODEL=${NEMOCLAW_LANE_ARCHON_LEANSTRAL_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_PLANNER_ENGINE_MODEL=${NEMOCLAW_PLANNER_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_LOGIC_ENGINE_MODEL=${NEMOCLAW_LOGIC_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_LANE_PLANNER_ENGINE_MODEL=${NEMOCLAW_LANE_PLANNER_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_LANE_LOGIC_ENGINE_MODEL=${NEMOCLAW_LANE_LOGIC_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_LANE_DISCOVERY_ENGINE_MODEL=${NEMOCLAW_LANE_DISCOVERY_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_DISCOVERY_ENGINE_MODEL=${NEMOCLAW_DISCOVERY_ENGINE_MODEL:-<missing>}" >> "{log}"
echo "NEMOCLAW_EXPERIMENT_LANE_MODEL=${NEMOCLAW_EXPERIMENT_LANE_MODEL:-<missing>}" >> "{log}"
echo "ARCHON_ARGS=$*" >> "{log}"
exit 0
""".replace("{log}", env_log.as_posix()),
        encoding="utf-8",
    )
    path.chmod(0o755)


def test_run_archon_superorganism_uses_fallback_when_resolver_fails(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(bin_dir, resolver_log)
    write_fake_archon(bin_dir, env_log)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"

    proc = subprocess.run(
        ["bash", str(SCRIPT), "--iterations", "1", "--project", str(tmp_path)],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    output = proc.stdout + proc.stderr

    assert proc.returncode == 0
    assert "WARN: model alias resolution failed" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_LOGIC_ENGINE_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=leanstral-gguf" in env_dump
    assert "resolver requested" in resolver_log.read_text(encoding="utf-8")


def test_run_archon_superorganism_uses_fallback_when_resolver_output_is_unusable(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=0,
        resolver_output='printf "not shell at all\\n"',
    )
    write_fake_archon(bin_dir, env_log)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"

    proc = subprocess.run(
        ["bash", str(SCRIPT), "--iterations", "1", "--project", str(tmp_path)],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    output = proc.stdout + proc.stderr

    assert proc.returncode == 0
    assert "WARN: model alias resolution output was not usable" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_LOGIC_ENGINE_MODEL=leanstral-gguf" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=leanstral-gguf" in env_dump


def test_run_archon_superorganism_respects_openrouter_pi_model_override(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=0,
        resolver_output='printf "ARCHON_LEANSTRAL_MODEL=resolved-leanstral\\n'
        'ARCHON_PI_MODEL=resolved-pi\\n"',
    )
    write_fake_archon(bin_dir, env_log)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"
    env["OPENROUTER_PI_MODEL"] = "openrouter/qwen/qwen3-coder:free"

    proc = subprocess.run(
        ["bash", str(SCRIPT), "--iterations", "1", "--project", str(tmp_path)],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    output = proc.stdout + proc.stderr

    assert proc.returncode == 0, output
    assert "Resolved startup model IDs:" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_PI_MODEL=openrouter/qwen/qwen3-coder:free" in env_dump


def test_run_archon_superorganism_exports_resolved_future_lanes(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=0,
        resolver_output=(
            'printf "ARCHON_LEANSTRAL_MODEL=resolved-leanstral\\n'
            'NEMOCLAW_DISCOVERY_ENGINE_MODEL=resolved-discovery\\n'
            'ARCHON_PI_MODEL=resolved-openrouter-pi\\n'
            'NEMOCLAW_EXPERIMENT_LANE_MODEL=resolved-experimental\\n"'
        ),
    )
    write_fake_archon(bin_dir, env_log)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"

    proc = subprocess.run(
        ["bash", str(SCRIPT), "--iterations", "1", "--project", str(tmp_path)],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    output = proc.stdout + proc.stderr

    assert proc.returncode == 0
    assert "Resolved startup model IDs:" in output
    assert "resolver requested" in resolver_log.read_text(encoding="utf-8")
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=resolved-leanstral" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=resolved-discovery" in env_dump
    assert "ARCHON_PI_MODEL=resolved-openrouter-pi" in env_dump
    assert "NEMOCLAW_EXPERIMENT_LANE_MODEL=resolved-experimental" in env_dump
