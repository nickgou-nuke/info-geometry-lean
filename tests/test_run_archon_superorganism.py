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
    defaults_exit: int = 1,
    defaults_output: str = "",
) -> None:
    path = bin_dir / "python3"
    path.write_text(
        """
#!/usr/bin/env bash
set -euo pipefail

printf '[fake-python] %s\\n' "$*" >> "{log}"

case "${1}" in
  *resolve_startup_model_ids.py)
    if [[ "$*" == *"--defaults-only"* ]]; then
      echo "resolver requested defaults-only" >> "{log}"
      {defaults_output}
      exit {defaults_exit}
    else
      echo "resolver requested primary" >> "{log}"
      {resolver_output}
      exit {resolver_exit}
    fi
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
        .replace("{resolver_exit}", str(resolver_exit))
        .replace("{defaults_output}", defaults_output)
        .replace("{defaults_exit}", str(defaults_exit)),
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


def write_fake_probe(bin_dir: Path, probe_log: Path, *, fail_pi_probe: bool = False) -> None:
    path = bin_dir / "python3"
    path.write_text(
        """
#!/usr/bin/env bash
set -euo pipefail

printf '[fake-python] %s\\n' "$*" >> "{log}"

case "${1}" in
  *resolve_startup_model_ids.py)
    if [[ "$*" == *"--defaults-only"* ]]; then
      echo "resolver requested defaults-only" >> "{log}"
      {defaults_output}
      exit {defaults_exit}
    else
      echo "resolver requested primary" >> "{log}"
      {resolver_output}
      exit {resolver_exit}
    fi
    ;;
  *check_resident_model_endpoint.py)
    echo "endpoint probe requested" >> "{log}"
    if [[ "$*" == *"--expected-model "*"broken-pi"* ]]; then
      exit {pi_probe_exit}
    fi
    exit 0
    ;;
  *)
    exec /usr/bin/python3 "$@"
    ;;
esac
""".replace("{log}", probe_log.as_posix())
        .replace("{resolver_output}", "printf \"ARCHON_LEANSTRAL_MODEL=resolved-leanstral\\nARCHON_PI_MODEL=broken-pi\\n\"")
        .replace("{resolver_exit}", "0")
        .replace("{defaults_output}", "printf \"ARCHON_LEANSTRAL_MODEL=fallback-leanstral\\n\"")
        .replace("{defaults_exit}", "0")
        .replace("{pi_probe_exit}", "1" if fail_pi_probe else "0"),
        encoding="utf-8",
    )
    path.chmod(0o755)


def test_run_archon_superorganism_uses_fallback_when_resolver_fails(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=1,
        resolver_output='printf "not shell output\\n"',
        defaults_exit=0,
        defaults_output=(
            'printf "ARCHON_LEANSTRAL_MODEL=fallback-leanstral\\n'
            'NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner\\n'
            'NEMOCLAW_LOGIC_ENGINE_MODEL=fallback-logic\\n'
            'NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery\\n"'
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
    assert "WARN: model alias resolution failed" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=fallback-leanstral" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner" in env_dump
    assert "NEMOCLAW_LOGIC_ENGINE_MODEL=fallback-logic" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery" in env_dump
    resolver_output = resolver_log.read_text(encoding="utf-8")
    assert "resolver requested primary" in resolver_output
    assert "resolver requested defaults-only" in resolver_output


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
        defaults_exit=0,
        defaults_output=(
            'printf "ARCHON_LEANSTRAL_MODEL=fallback-leanstral\\n'
            'NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner\\n'
            'NEMOCLAW_LOGIC_ENGINE_MODEL=fallback-logic\\n'
            'NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery\\n"'
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
    assert "WARN: model alias resolution output was not usable" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=fallback-leanstral" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner" in env_dump
    assert "NEMOCLAW_LOGIC_ENGINE_MODEL=fallback-logic" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery" in env_dump


def test_run_archon_superorganism_uses_fallback_when_resolver_output_is_missing(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=0,
        resolver_output='printf "\\n\\n   \\n"',
        defaults_exit=0,
        defaults_output=(
            'printf "ARCHON_LEANSTRAL_MODEL=fallback-leanstral\\n'
            'NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner\\n'
            'NEMOCLAW_LOGIC_ENGINE_MODEL=fallback-logic\\n'
            'NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery\\n"'
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
    assert "WARN: model alias resolution output was not usable" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=fallback-leanstral" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=fallback-planner" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=fallback-discovery" in env_dump


def test_run_archon_superorganism_uses_configured_startup_defaults(tmp_path: Path) -> None:
    custom_archon = tmp_path / "custom_config.yaml"
    custom_nemoclaw = tmp_path / "custom_nemoclaw.yaml"
    custom_archon.write_text(
        """
assistant: pi
assistants:
  leanstral:
    model: config-leanstral
""",
        encoding="utf-8",
    )
    custom_nemoclaw.write_text(
        """
version: "1.1"
lanes:
  planner_engine:
    model: config-planner
  logic_engine:
    model: config-logic
  discovery_engine:
    model: config-discovery
""",
        encoding="utf-8",
    )

    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=1,
        resolver_output='printf "not shell\\n"',
        defaults_exit=0,
        defaults_output=(
            'printf "ARCHON_LEANSTRAL_MODEL=config-leanstral\\n'
            'NEMOCLAW_PLANNER_ENGINE_MODEL=config-planner\\n'
            'NEMOCLAW_LOGIC_ENGINE_MODEL=config-logic\\n'
            'NEMOCLAW_DISCOVERY_ENGINE_MODEL=config-discovery\\n"'
        ),
    )
    write_fake_archon(bin_dir, env_log)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}:{env['PATH']}"
    env["ARCHON_STARTUP_ARCHON_CONFIG"] = str(custom_archon)
    env["ARCHON_STARTUP_NEMOCLAW_CONFIG"] = str(custom_nemoclaw)

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
    assert "Resolved startup model IDs from local startup defaults:" in output
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=config-leanstral" in env_dump
    assert "NEMOCLAW_PLANNER_ENGINE_MODEL=config-planner" in env_dump
    assert "NEMOCLAW_LOGIC_ENGINE_MODEL=config-logic" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=config-discovery" in env_dump
    log = resolver_log.read_text(encoding="utf-8")
    assert str(custom_archon) in log
    assert str(custom_nemoclaw) in log
    assert "resolver requested defaults-only" in log


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
    assert "Startup model source: resolved_via=alias" in output
    assert "resolver requested" in resolver_log.read_text(encoding="utf-8")
    env_dump = env_log.read_text(encoding="utf-8")
    assert "ARCHON_LEANSTRAL_MODEL=resolved-leanstral" in env_dump
    assert "NEMOCLAW_DISCOVERY_ENGINE_MODEL=resolved-discovery" in env_dump
    assert "ARCHON_PI_MODEL=resolved-openrouter-pi" in env_dump
    assert "NEMOCLAW_EXPERIMENT_LANE_MODEL=resolved-experimental" in env_dump


def test_run_archon_superorganism_warns_on_local_pi_preflight_failure(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    probe_log = tmp_path / "probe.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_probe(bin_dir, probe_log, fail_pi_probe=True)
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
    assert "WARN: Pi model preflight failed for configured model 'broken-pi'" in output
    log = probe_log.read_text(encoding="utf-8")
    assert "--expected-model broken-pi" in log


def test_run_archon_superorganism_skips_local_pi_preflight_for_openrouter(tmp_path: Path) -> None:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    resolver_log = tmp_path / "resolver.log"
    env_log = tmp_path / "archon_env.log"
    write_fake_python(
        bin_dir,
        resolver_log,
        resolver_exit=0,
        resolver_output='printf "ARCHON_LEANSTRAL_MODEL=resolved-leanstral\\nARCHON_PI_MODEL=openrouter/qwen/qwen3-coder:free\\n"',
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
    assert "Skipping local Pi model preflight for remote model: openrouter/qwen/qwen3-coder:free" in output
