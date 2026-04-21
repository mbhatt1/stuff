"""K-tradeoff curve (Theorem 7.3).

Theorem 7.3 states that the critical defense-path Lipschitz rate is
    K* = G / ell - 1
and that a persistent unsafe region is guaranteed whenever the
empirical K satisfies K < K*.  Equivalently, Theorem 6.2's
transversality condition G > ell*(K+1) holds iff ell*(K+1) < G.

We plot the curve y = ell*(K+1) against K for each defense observed
on the saturated gpt-3.5-turbo archive, together with the horizontal
line y = G = 23.625.  The region y < G (below the line) is where the
theorem guarantees a persistent unsafe set; the region y >= G is the
regime where the theorem cannot rule out defense success.

All numbers are analytical - no new experiment is run.  Values are
read from the live_runs saturated archive's gp_smooth_result_*.json
summaries and from report.md.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
SAT = ROOT / "trilemma_validator" / "live_runs" / "gpt35_turbo_t05_saturated"
OUT_DIR = ROOT / "figures"
OUT_DIR.mkdir(exist_ok=True)


def collect_defenses() -> list[dict]:
    """Gather (ell, K, defense_name) triples from the saturated run."""
    defenses: list[dict] = []

    # identity defense from report.md: ell = 0.0, K = 1.0
    defenses.append({
        "name": "identity",
        "ell": 0.0,
        "K": 1.0,
    })

    # smooth_nearest_safe from live validator output (recorded in
    # report.md / result.json under the default run).  ell = 23.625,
    # K = 3.0 (radius = 3).  We reproduce it via the CLI as well.
    defenses.append({
        "name": "smooth_nearest_safe",
        "ell": 23.625,
        "K": 3.0,
    })

    # gp_smooth_* variants (ell, K from JSON files).
    for stem, label in [
        ("gp_smooth_result_centroid", "gp_centroid"),
        ("gp_smooth_result_grad_step", "gp_grad_step"),
        ("gp_smooth_result_oblique", "gp_oblique"),
    ]:
        path = SAT / f"{stem}.json"
        if not path.exists():
            continue
        with open(path) as fh:
            d = json.load(fh)
        defenses.append({
            "name": label,
            "ell": float(d["ell_empirical"]),
            "K": float(d["K_empirical"]),
        })
    return defenses


def main() -> None:
    G = 23.625  # from saturated run (L = G on this surface)
    defenses = collect_defenses()

    plt.rcParams.update({
        "font.family": "serif",
        "font.size": 10,
    })

    fig, ax = plt.subplots(figsize=(7, 4))
    K_axis = np.linspace(0.0, 10.0, 400)

    # Draw a family of curves y = ell * (K + 1) for each observed ell.
    # Choose a small palette, skipping ell = 0 (the curve would be y = 0).
    palette = plt.cm.viridis(np.linspace(0.15, 0.85, len(defenses)))
    for (info, color) in zip(defenses, palette):
        ell = info["ell"]
        y = ell * (K_axis + 1.0)
        label = f"{info['name']}  ($\\ell$={ell:.2f})"
        ax.plot(K_axis, y, color=color, lw=1.6, label=label)

        # Annotate the (K_obs, ell*(K_obs+1)) point for this defense.
        K_obs = info["K"]
        y_obs = ell * (K_obs + 1.0)
        ax.plot(K_obs, y_obs, marker="o", color=color,
                markersize=6, markeredgecolor="black", markeredgewidth=0.5,
                linestyle="none")

    # G line.
    ax.axhline(G, color="crimson", ls="--", lw=1.4, label=f"G = {G:.3f}")

    # Shade persistent region (y < G).  We shade the whole axes area
    # below y = G to indicate that ANY (K, ell) pair in this zone
    # satisfies Theorem 6.2's hypothesis.
    ax.axhspan(0.0, G, alpha=0.09, color="crimson",
               label="persistent region exists  (y < G)")

    ax.set_xlabel("K  (Lipschitz constant of defense D)")
    ax.set_ylabel(r"$\ell \cdot (K+1)$")
    ax.set_title(r"Theorem E.3 trade-off: persistent region exists iff $\ell(K+1) < G$")
    ax.set_xlim(0.0, 10.0)

    # Reasonable y range: just above G for visibility of crossings.
    y_top = max(G * 2.2, max(info["ell"] for info in defenses) * 6.0)
    ax.set_ylim(0.0, y_top)

    ax.grid(True, alpha=0.25)
    ax.legend(
        loc="center left",
        bbox_to_anchor=(1.02, 0.5),
        frameon=False,
        fontsize=8,
    )

    plt.tight_layout()
    out = OUT_DIR / "k_tradeoff.pdf"
    plt.savefig(out, dpi=200, bbox_inches="tight")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
