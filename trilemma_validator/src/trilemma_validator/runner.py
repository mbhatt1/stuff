"""Subprocess wrapper for invoking ``rethinking-evals`` to produce a heatmap.

This module does not assume rethinking-evals is installed in the same Python
environment. It runs the experiment script as a subprocess in whatever
environment the user points to (typically a uv-managed venv inside the
rethinking-evals checkout). The trilemma validator then loads the resulting
``final_archive.json`` from disk.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass
class ExperimentConfig:
    rethinking_path: Path
    model: str
    iterations: int
    seed_prompts: int
    output_dir: Path
    python: str | None = None  # path to python; defaults to ``uv run``


def _resolve_runner(rethinking_path: Path) -> list[str]:
    """Return the command prefix used to invoke the experiment script.

    Prefers ``uv run`` if a ``uv`` binary is on PATH (rethinking-evals's
    documented installation method); falls back to the current Python.
    """
    if shutil.which("uv") is not None:
        return ["uv", "run", "python"]
    return [sys.executable]


def run_experiment(cfg: ExperimentConfig) -> Path:
    """Run rethinking-evals end-to-end and return the path to ``final_archive.json``.

    Raises ``RuntimeError`` if the subprocess returns non-zero or if the
    expected output file is missing.
    """
    cfg.rethinking_path = cfg.rethinking_path.resolve()
    cfg.output_dir = cfg.output_dir.resolve()
    cfg.output_dir.mkdir(parents=True, exist_ok=True)

    script = cfg.rethinking_path / "experiments" / "run_main_experiment.py"
    if not script.exists():
        raise FileNotFoundError(
            f"rethinking-evals run script not found at {script}. "
            f"Pass --rethinking-path pointing at the repo root."
        )

    if "OPENAI_API_KEY" not in os.environ:
        raise RuntimeError(
            "OPENAI_API_KEY is not set in the environment. "
            "rethinking-evals cannot make API calls without it."
        )

    cmd = [
        *_resolve_runner(cfg.rethinking_path),
        str(script),
        "--model",
        cfg.model,
        "--iterations",
        str(cfg.iterations),
        "--seed-prompts",
        str(cfg.seed_prompts),
        "--output-dir",
        str(cfg.output_dir),
    ]

    print(f"[trilemma] running rethinking-evals: {' '.join(cmd)}", flush=True)
    result = subprocess.run(
        cmd,
        cwd=str(cfg.rethinking_path),
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"rethinking-evals exited with code {result.returncode}. "
            f"See its output above for the failure cause."
        )

    archive = cfg.output_dir / "final_archive.json"
    if not archive.exists():
        raise FileNotFoundError(
            f"rethinking-evals completed but {archive} was not produced. "
            f"Inspect the output directory for partial results."
        )
    return archive
