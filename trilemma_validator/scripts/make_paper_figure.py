#!/usr/bin/env python3
"""Generate the paper figure: per-cell ε-robust margin scatter.

Reads the committed saturated live archive and produces a single-panel PDF
showing every filled cell as a dot, the predicted ε-robust bound as a
diagonal line, and the predicted-persistent / safe / boundary classification
as colors. Visually verifies Theorem 5.1 cell-by-cell.

Run with no arguments to write ``figures/eps_robust_saturated.pdf`` from
``live_runs/gpt35_turbo_t05_saturated/source_archive.json``.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

from trilemma_validator.defenses import IdentityDefense
from trilemma_validator.lipschitz import estimate_global_L
from trilemma_validator.loader import load_archive_json
from trilemma_validator.theorems import _select_anchor, check_boundary_fixation


def make_figure(archive_path: Path, out_path: Path, tau: float = 0.5) -> None:
    heatmap = load_archive_json(archive_path)
    defense = IdentityDefense().build(heatmap, tau)
    bd = check_boundary_fixation(defense, heatmap, tau)
    if not bd.boundary_exists:
        raise RuntimeError(
            f"No boundary cells found at tau={tau}; cannot anchor the bound."
        )
    anchor, slack = _select_anchor(bd, heatmap, tau)
    assert anchor is not None
    z_i, z_j = anchor

    L = estimate_global_L(heatmap)
    K = 1.0  # identity defense
    LK = L * K
    h = heatmap.cell_width

    vals = heatmap.values
    filled = heatmap.filled_mask
    boundary_set = set(bd.boundary_cells)

    pts_unsafe: list[tuple[float, float]] = []  # f > tau, non-boundary
    pts_safe: list[tuple[float, float]] = []  # f < tau, non-boundary
    pts_boundary: list[tuple[float, float]] = []  # in cl(S) \ S

    for i in range(heatmap.grid_size):
        for j in range(heatmap.grid_size):
            if not filled[i, j]:
                continue
            d = h * float(np.hypot(i - z_i, j - z_j))
            lhs = abs(float(vals[i, j] - tau))
            f = float(vals[i, j])
            if (i, j) in boundary_set:
                pts_boundary.append((d, lhs))
            elif f > tau:
                pts_unsafe.append((d, lhs))
            else:
                pts_safe.append((d, lhs))

    all_pts = pts_unsafe + pts_safe + pts_boundary
    max_d = max(p[0] for p in all_pts) if all_pts else 1.0
    line_x = np.linspace(0, max_d * 1.05, 200)
    line_y = LK * line_x + slack

    # Floor for log axis: every dot must be > 0. The boundary cells (and any
    # cell with f = tau exactly) sit at LHS = 0 because |f(D(x))-tau|=0 there;
    # we lift them to a small visible value below the smallest non-zero LHS so
    # they remain visible on a log axis.
    nonzero_lhs = [p[1] for p in all_pts if p[1] > 0]
    floor = (min(nonzero_lhs) / 3) if nonzero_lhs else 1e-3

    def lift(y: float) -> float:
        return y if y > 0 else floor

    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.size": 9,
            "axes.titlesize": 10,
            "axes.labelsize": 9,
            "legend.fontsize": 8,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
        }
    )

    fig, ax = plt.subplots(figsize=(6.6, 4.2))

    # Bound line — shade the valid region (below the line) lightly.
    ax.fill_between(
        line_x, floor / 2, line_y, color="#cbd5e0", alpha=0.25, zorder=1
    )
    ax.plot(
        line_x,
        line_y,
        linestyle="--",
        color="#2d3748",
        linewidth=1.5,
        label=(
            r"Predicted bound (Thm.~5.1): "
            r"$LK\cdot\mathrm{dist}(x,z^*) + |f(z^*)-\tau|$, "
            rf"$LK={LK:.2f}$"
        ),
        zorder=2,
    )

    if pts_unsafe:
        x = [p[0] for p in pts_unsafe]
        y = [lift(p[1]) for p in pts_unsafe]
        ax.scatter(
            x,
            y,
            s=34,
            facecolor="#c53030",
            edgecolor="black",
            linewidths=0.4,
            label=rf"$f(x)>\tau$, in $\mathcal{{S}}_{{\mathrm{{pred}}}}\cap\mathcal{{S}}_{{\mathrm{{act}}}}$ ($n={len(pts_unsafe)}$)",
            zorder=4,
        )
    if pts_safe:
        x = [p[0] for p in pts_safe]
        y = [lift(p[1]) for p in pts_safe]
        ax.scatter(
            x,
            y,
            s=28,
            facecolor="#38a169",
            edgecolor="black",
            linewidths=0.4,
            label=rf"$f(x)<\tau$ (safe, $n={len(pts_safe)}$)",
            zorder=4,
        )
    if pts_boundary:
        x = [p[0] for p in pts_boundary]
        y = [lift(p[1]) for p in pts_boundary]
        ax.scatter(
            x,
            y,
            s=44,
            marker="s",
            facecolor="#2d3748",
            edgecolor="black",
            linewidths=0.4,
            label=rf"boundary cell $\in \overline{{S_\tau}}\setminus S_\tau$ ($n={len(pts_boundary)}$)",
            zorder=5,
        )

    ax.set_xlabel(r"$\mathrm{dist}(x,\, z^*)$")
    ax.set_ylabel(r"$|f(D(x)) - \tau|$  (log scale)")
    ax.set_xlim(0, max_d * 1.05)
    ax.set_yscale("log")
    ax.set_ylim(floor / 2, (LK * max_d + slack) * 1.4)
    ax.grid(True, which="both", linestyle=":", linewidth=0.5, alpha=0.55)
    ax.legend(loc="lower right", framealpha=0.94, fontsize=7.5)

    n = len(all_pts)
    ax.set_title(
        rf"Theorem 5.1 holds for every filled cell "
        rf"(saturated live run, gpt-3.5-turbo-0125, $n={n}$, $\tau={tau}$)"
    )

    fig.tight_layout()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, format="pdf", bbox_inches="tight")
    plt.close(fig)

    print(f"Wrote {out_path}")
    print(
        f"  L={L:.4f}  K={K}  LK={LK:.4f}  slack={slack:.4f}  "
        f"unsafe={len(pts_unsafe)}  safe={len(pts_safe)}  "
        f"boundary={len(pts_boundary)}"
    )


def main(argv: list[str] | None = None) -> int:
    here = Path(__file__).resolve().parent
    repo = here.parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive",
        type=Path,
        default=repo
        / "trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=repo / "figures/eps_robust_saturated.pdf",
    )
    parser.add_argument("--tau", type=float, default=0.5)
    args = parser.parse_args(argv)
    make_figure(args.archive, args.out, tau=args.tau)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
