#!/usr/bin/env python3
"""Experiment 3 driver — Theorem E.3 cone-bound tightness sweep.

Run this OFFLINE against the existing saturated archive. It performs:

1. Read ``G``, ``ell``, ``K_empirical`` from
   ``live_runs/gpt35_turbo_t05_saturated/gp_smooth_result_oblique.json``
   (the non-tautological oblique-defense reference measurement from the
   paper).
2. Compute ``K* = G/ell - 1`` analytically.
3. Pre-register predicted cone bounds for each K in the sweep grid and
   write ``predictions.json`` to disk *before* running the sweep
   (ensuring the file mtime is strictly less than ``sweep.json``'s).
4. For each K in the grid, construct an oblique GP defense whose
   empirical K matches target to within 5 % (via binary search on
   alpha_step), measure the empirical persistent region, and compare
   against the Theorem E.2 cone bound.
5. Emit ``sweep.json`` with per-K rows, a PDF figure, and a LaTeX table.

Offline only. No model calls.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path
from typing import Optional

import matplotlib
matplotlib.use("Agg")  # headless backend — required per experimental protocol
import matplotlib.pyplot as plt
import numpy as np

from trilemma_validator.loader import load_archive_json
from trilemma_validator.optimal_k import (
    build_optimal_k_defense,
    compute_K_star,
    measure_persistent_region,
    predict_cone_bound,
)


REPO = Path(__file__).resolve().parents[2]
DEFAULT_ARCHIVE = (
    REPO
    / "trilemma_validator"
    / "live_runs"
    / "gpt35_turbo_t05_saturated"
    / "source_archive.json"
)
DEFAULT_OBLIQUE_REF = (
    REPO
    / "trilemma_validator"
    / "live_runs"
    / "gpt35_turbo_t05_saturated"
    / "gp_smooth_result_oblique.json"
)


# Sweep grid: multiples of K*. At least 9 values per the spec.
DEFAULT_MULTIPLIERS = [0.3, 0.5, 0.7, 0.9, 1.0, 1.1, 1.5, 2.0, 3.0]


def _load_reference_constants(path: Path) -> dict:
    """Load (G, ell, K_empirical, tau) from the oblique reference run."""
    with path.open() as f:
        d = json.load(f)
    return {
        "G": float(d["G"]),
        "ell": float(d["ell_empirical"]),
        "K_empirical": float(d["K_empirical"]),
        "tau": float(d["tau"]),
    }


def _compute_slice_length(archive_path: Path, tau: float) -> float:
    """Geometric prefactor for Theorem E.2: length of the boundary slice.

    Approximated by ``n_boundary * h`` where ``h`` is the grid cell width
    and ``n_boundary`` is the number of safe/unsafe boundary cells. This is
    the same slice-length convention used throughout the validator.
    """
    heatmap = load_archive_json(archive_path)
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    h = heatmap.cell_width

    n_bdy = 0
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            if vals[i, j] < tau:
                continue
            # A "boundary" cell is an unsafe cell with a 4-neighbor that is
            # filled and safe.
            for di, dj in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                ni, nj = i + di, j + dj
                if 0 <= ni < gs and 0 <= nj < gs:
                    if filled[ni, nj] and vals[ni, nj] < tau:
                        n_bdy += 1
                        break
    return float(max(1, n_bdy) * h)


def preregister_predictions(
    *,
    G: float,
    ell: float,
    K_star: float,
    multipliers: list[float],
    slice_length: float,
    out_path: Path,
) -> dict:
    """Pre-register the cone-bound predictions for the whole grid.

    Must be called *before* any empirical measurement so the file's mtime
    precedes the sweep output.
    """
    rows = []
    for m in multipliers:
        K = m * K_star
        delta_0 = predict_cone_bound(G, ell, K, slice_length)
        rows.append(
            {
                "K_over_K_star": float(m),
                "K_target": float(K),
                "predicted_cone_bound_delta0": float(delta_0),
                "cone_condition_holds": bool(G > ell * (K + 1.0)),
            }
        )
    payload = {
        "registered_at_unix": time.time(),
        "registered_at_iso": time.strftime(
            "%Y-%m-%dT%H:%M:%SZ", time.gmtime()
        ),
        "theorem": "7.2 cone bound + 7.3 design equation",
        "inputs": {
            "G": float(G),
            "ell": float(ell),
            "K_star": float(K_star),
            "slice_length": float(slice_length),
        },
        "predictions": rows,
        "note": (
            "Predictions are fully determined by (G, ell, K, slice_length). "
            "No empirical measurement is used here. The sweep writes "
            "sweep.json STRICTLY AFTER this file — the relative mtimes "
            "prove the pre-registration."
        ),
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        json.dump(payload, f, indent=2)
        f.flush()
        os.fsync(f.fileno())
    return payload


def run_sweep(
    *,
    archive_path: Path,
    oblique_ref_path: Path,
    out_dir: Path,
    multipliers: list[float],
    length_scale: float,
    noise: float,
    sigmoid_steepness: float,
    oblique_angle_deg: float,
    tau: Optional[float],
) -> Path:
    """Run the K sweep, write sweep.json + predictions.json, return sweep path."""
    ref = _load_reference_constants(oblique_ref_path)
    if tau is None:
        tau = ref["tau"]
    G = ref["G"]
    ell = ref["ell"]
    K_star = compute_K_star(G, ell)

    print(f"Loaded reference: G={G:.4f}, ell={ell:.4f}, K_emp_ref={ref['K_empirical']:.4f}")
    print(f"K* = G/ell - 1 = {K_star:.4f}")

    slice_length = _compute_slice_length(archive_path, tau)
    print(f"Slice length (geometric prefactor) = {slice_length:.4f}")

    # 1. Pre-registration: must happen before any measurement.
    predictions_path = out_dir / "predictions.json"
    preregister_predictions(
        G=G,
        ell=ell,
        K_star=K_star,
        multipliers=multipliers,
        slice_length=slice_length,
        out_path=predictions_path,
    )
    print(f"Pre-registered predictions -> {predictions_path}")

    # Small gap to guarantee sweep.json mtime > predictions.json mtime even
    # on coarse-mtime filesystems.
    time.sleep(0.05)

    # 2. Load the heatmap once, reuse across targets.
    heatmap = load_archive_json(archive_path)

    rows = []
    for m in multipliers:
        target_K = m * K_star
        print(f"\n  K-target = {m:.2f} * K* = {target_K:.4f}")
        result = build_optimal_k_defense(
            heatmap,
            tau=tau,
            target_K=target_K,
            G=G,
            ell_reference=ell,
            length_scale=length_scale,
            noise=noise,
            sigmoid_steepness=sigmoid_steepness,
            oblique_angle_deg=oblique_angle_deg,
        )
        meas = measure_persistent_region(result, tau)
        delta_0 = predict_cone_bound(G, ell, result.achieved_K, slice_length)

        ratio = (
            meas["persistent_measure"] / delta_0
            if delta_0 > 0
            else float("inf")
        )
        # "Tight" := empirical is at least the predicted bound AND within 3x.
        tight = bool(
            delta_0 > 0
            and meas["persistent_measure"] >= delta_0
            and ratio <= 3.0
        )
        rows.append(
            {
                "K_over_K_star": float(m),
                "target_K": float(target_K),
                "achieved_K": float(result.achieved_K),
                "within_5pct_of_target": bool(result.within_5pct),
                "alpha_step": float(result.alpha_step),
                "binary_search_iters": int(result.binary_search_iters),
                "ell_empirical": float(result.ell_empirical),
                "n_persistent_cells": int(meas["n_persistent_cells"]),
                "empirical_persistent_measure": float(
                    meas["persistent_measure"]
                ),
                "predicted_cone_bound_delta0": float(delta_0),
                "ratio_empirical_to_predicted": float(ratio)
                if ratio != float("inf")
                else None,
                "cone_condition_holds": bool(G > ell * (result.achieved_K + 1.0)),
                "tight": tight,
            }
        )
        print(
            f"    achieved_K={result.achieved_K:.4f}  "
            f"|S_act|={meas['n_persistent_cells']} cells  "
            f"emp={meas['persistent_measure']:.4f}  "
            f"pred={delta_0:.4f}  tight={tight}"
        )

    sweep = {
        "ran_at_unix": time.time(),
        "ran_at_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "archive": str(archive_path),
        "oblique_reference": str(oblique_ref_path),
        "tau": float(tau),
        "G": float(G),
        "ell": float(ell),
        "K_star": float(K_star),
        "slice_length": float(slice_length),
        "defense_hyperparams": {
            "length_scale": float(length_scale),
            "noise": float(noise),
            "sigmoid_steepness": float(sigmoid_steepness),
            "oblique_angle_deg": float(oblique_angle_deg),
        },
        "multipliers": list(multipliers),
        "rows": rows,
    }

    sweep_path = out_dir / "sweep.json"
    with sweep_path.open("w") as f:
        json.dump(sweep, f, indent=2)
    print(f"\nWrote {sweep_path}")
    return sweep_path


def render_figure(sweep_path: Path, out_path: Path) -> None:
    """Plot empirical persistent-region measure vs K, overlay cone bound."""
    with sweep_path.open() as f:
        sweep = json.load(f)
    rows = sweep["rows"]
    K_star = float(sweep["K_star"])

    K_vals = np.array([r["achieved_K"] for r in rows])
    mults = np.array([r["K_over_K_star"] for r in rows])
    emp = np.array([r["empirical_persistent_measure"] for r in rows])
    pred = np.array([r["predicted_cone_bound_delta0"] for r in rows])

    order = np.argsort(K_vals)
    K_vals = K_vals[order]
    mults = mults[order]
    emp = emp[order]
    pred = pred[order]

    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 10,
            "axes.titlesize": 11,
            "axes.labelsize": 10,
            "xtick.labelsize": 9,
            "ytick.labelsize": 9,
        }
    )
    fig, ax = plt.subplots(figsize=(7.0, 4.0))

    ax.plot(
        K_vals,
        emp,
        marker="o",
        linestyle="-",
        color="#c53030",
        label=r"empirical $|S_{\mathrm{act}}|$",
    )
    ax.plot(
        K_vals,
        pred,
        marker="s",
        linestyle="--",
        color="#2b6cb0",
        label=r"Thm E.2 cone bound $\delta_0$",
    )

    ax.axvline(
        K_star,
        color="#1a202c",
        linestyle=":",
        linewidth=1.2,
        label=rf"$K^*={K_star:.2f}$",
    )
    ax.axhline(0.0, color="#a0aec0", linewidth=0.7)

    ax.set_xlabel(r"defense Lipschitz $K$")
    ax.set_ylabel(r"measure of persistent set")
    ax.set_title(
        r"Theorem E.3 cone bound vs empirical persistent region "
        r"(oblique GP defense, saturated archive)"
    )
    ax.legend(loc="upper right", frameon=True)

    # Also annotate K/K* on a top axis for interpretation.
    ax2 = ax.twiny()
    ax2.set_xlim(ax.get_xlim())
    tick_mults = [0.3, 0.5, 1.0, 1.5, 2.0, 3.0]
    ax2.set_xticks([m * K_star for m in tick_mults])
    ax2.set_xticklabels([f"{m:.1f}" for m in tick_mults])
    ax2.set_xlabel(r"$K / K^*$")

    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="pdf", bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote {out_path}")


def render_latex_table(sweep_path: Path, out_path: Path) -> None:
    """Write the representative-K table for the paper."""
    with sweep_path.open() as f:
        sweep = json.load(f)
    rows = sweep["rows"]
    # Representative multipliers; fall back to nearest if exact absent.
    wanted = [0.5, 1.0, 2.0]
    picks = []
    for w in wanted:
        row = min(rows, key=lambda r: abs(r["K_over_K_star"] - w))
        picks.append(row)

    lines = []
    lines.append(r"% Auto-generated by optimal_k_experiment.py; do not edit.")
    lines.append(r"\begin{tabular}{lrrrrc}")
    lines.append(r"\toprule")
    lines.append(
        r"$K/K^*$ & achieved $K$ & $|S_{\mathrm{act}}|$ (cells) & empirical measure & Thm E.2 $\delta_0$ & tight? \\"
    )
    lines.append(r"\midrule")
    for r in picks:
        ratio_str = (
            f"{r['ratio_empirical_to_predicted']:.2f}"
            if r["ratio_empirical_to_predicted"] is not None
            else r"$\infty$"
        )
        tight_str = r"\checkmark" if r["tight"] else r"--"
        lines.append(
            f"{r['K_over_K_star']:.2f} & "
            f"{r['achieved_K']:.3f} & "
            f"{r['n_persistent_cells']} & "
            f"{r['empirical_persistent_measure']:.4f} & "
            f"{r['predicted_cone_bound_delta0']:.4f} & "
            f"{tight_str} \\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n")
    print(f"Wrote {out_path}")


def render_agent_insert(
    sweep_path: Path, predictions_path: Path, out_path: Path
) -> None:
    """Short markdown insert summarising the Experiment-3 findings."""
    with sweep_path.open() as f:
        sweep = json.load(f)
    G = sweep["G"]
    ell = sweep["ell"]
    K_star = sweep["K_star"]
    rows = sweep["rows"]
    lines = [
        "# Experiment 3 — Theorem E.3 cone-bound tightness (agent 3 insert)",
        "",
        f"- Saturated archive: `{sweep['archive']}`",
        f"- G = {G:.4f}  ell = {ell:.4f}  **K\\* = G/ell - 1 = {K_star:.4f}**",
        f"- Defense family: oblique GP (length\\_scale={sweep['defense_hyperparams']['length_scale']},",
        f"  oblique\\_angle={sweep['defense_hyperparams']['oblique_angle_deg']} deg)",
        "",
        "| K/K\\* | achieved K | cells | empirical | Thm E.2 delta_0 | tight |",
        "|---|---|---|---|---|---|",
    ]
    for r in rows:
        lines.append(
            f"| {r['K_over_K_star']:.2f} "
            f"| {r['achieved_K']:.3f} "
            f"| {r['n_persistent_cells']} "
            f"| {r['empirical_persistent_measure']:.4f} "
            f"| {r['predicted_cone_bound_delta0']:.4f} "
            f"| {'yes' if r['tight'] else 'no'} |"
        )
    with predictions_path.open() as pf:
        preds = json.load(pf)
    lines.append("")
    lines.append(
        "Pre-registration: predictions written at "
        f"{preds['registered_at_iso']} "
        "before any empirical measurement."
    )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n")
    print(f"Wrote {out_path}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive",
        type=Path,
        default=DEFAULT_ARCHIVE,
        help="Saturated source archive JSON.",
    )
    parser.add_argument(
        "--oblique-ref",
        type=Path,
        default=DEFAULT_OBLIQUE_REF,
        help="Reference oblique defense result (for G, ell, tau).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO / "trilemma_validator" / "live_runs" / "optimal_k",
        help="Output directory for sweep.json + predictions.json.",
    )
    parser.add_argument(
        "--figure",
        type=Path,
        default=REPO / "figures" / "optimal_k_sweep.pdf",
    )
    parser.add_argument(
        "--table",
        type=Path,
        default=REPO / "tables" / "optimal_k.tex",
    )
    parser.add_argument(
        "--agent-insert",
        type=Path,
        default=REPO / "outputs" / "agent3_insert.md",
    )
    parser.add_argument(
        "--multipliers",
        type=float,
        nargs="+",
        default=DEFAULT_MULTIPLIERS,
    )
    parser.add_argument("--length-scale", type=float, default=0.20)
    parser.add_argument("--noise", type=float, default=0.02)
    parser.add_argument("--sigmoid-steepness", type=float, default=2.0)
    parser.add_argument("--oblique-angle-deg", type=float, default=89.5)
    parser.add_argument("--tau", type=float, default=None)
    args = parser.parse_args(argv)

    args.out.mkdir(parents=True, exist_ok=True)

    sweep_path = run_sweep(
        archive_path=args.archive,
        oblique_ref_path=args.oblique_ref,
        out_dir=args.out,
        multipliers=list(args.multipliers),
        length_scale=args.length_scale,
        noise=args.noise,
        sigmoid_steepness=args.sigmoid_steepness,
        oblique_angle_deg=args.oblique_angle_deg,
        tau=args.tau,
    )
    render_figure(sweep_path, args.figure)
    render_latex_table(sweep_path, args.table)
    render_agent_insert(sweep_path, args.out / "predictions.json", args.agent_insert)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
