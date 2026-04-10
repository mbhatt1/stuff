"""Six-panel matplotlib visualization of a trilemma validation result."""

from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap

from .defenses import DefenseMap
from .loader import Heatmap
from .theorems import TrilemmaResult, _post_defense_values


def _ad_cmap() -> LinearSegmentedColormap:
    """Green → yellow → red colormap matching the paper's surface plots."""
    return LinearSegmentedColormap.from_list(
        "ad", ["#d4f5dd", "#f6ad55", "#c53030"]
    )


def render(
    heatmap: Heatmap,
    defense: DefenseMap,
    tau: float,
    result: TrilemmaResult,
    path: Path,
) -> None:
    """Render the 6-panel diagnostic figure."""
    cmap = _ad_cmap()
    vals = heatmap.values
    post = _post_defense_values(defense, heatmap)
    gs = heatmap.grid_size

    fig, axes = plt.subplots(2, 3, figsize=(15, 10), constrained_layout=True)
    fig.suptitle(
        f"Defense Trilemma Validation  ·  τ = {tau}  ·  defense = {defense.name}",
        fontsize=14,
        fontweight="bold",
    )

    # 1. Original surface
    ax = axes[0, 0]
    im = ax.imshow(vals.T, origin="lower", cmap=cmap, vmin=0, vmax=1, aspect="equal")
    ax.set_title("(a) Alignment-deviation surface  f(x)")
    ax.set_xlabel("indirection a₁")
    ax.set_ylabel("authority a₂")
    plt.colorbar(im, ax=ax, fraction=0.046)

    # 2. Safe / unsafe / boundary classification
    ax = axes[0, 1]
    cls = np.full(vals.shape, np.nan)
    cls[heatmap.filled_mask & (vals < tau)] = 0.0  # safe
    cls[heatmap.filled_mask & (vals >= tau)] = 1.0  # unsafe
    for i, j in result.boundary.boundary_cells:
        cls[i, j] = 0.5  # boundary
    cls_cmap = LinearSegmentedColormap.from_list(
        "cls", ["#38a169", "#2d3748", "#c53030"]
    )
    ax.imshow(cls.T, origin="lower", cmap=cls_cmap, vmin=0, vmax=1, aspect="equal")
    ax.set_title(
        f"(b) Regions  ·  safe={result.safe_count}, "
        f"unsafe={result.unsafe_count}, "
        f"boundary={len(result.boundary.boundary_cells)}"
    )
    ax.set_xlabel("indirection a₁")
    ax.set_ylabel("authority a₂")

    # 3. Defense displacement field
    ax = axes[0, 2]
    ax.imshow(vals.T, origin="lower", cmap=cmap, vmin=0, vmax=1, aspect="equal", alpha=0.35)
    displaced = defense.displaced_mask()
    targets = defense.targets
    ii, jj = np.indices(vals.shape)
    di = (targets[..., 0] - ii)[displaced]
    dj = (targets[..., 1] - jj)[displaced]
    src_i = ii[displaced]
    src_j = jj[displaced]
    if src_i.size > 0:
        ax.quiver(
            src_i,
            src_j,
            di,
            dj,
            angles="xy",
            scale_units="xy",
            scale=1,
            color="#2b6cb0",
            width=0.004,
            alpha=0.8,
        )
    ax.set_title(f"(c) Defense displacements  ({int(displaced.sum())} cells)")
    ax.set_xlabel("indirection a₁")
    ax.set_ylabel("authority a₂")
    ax.set_xlim(-0.5, gs - 0.5)
    ax.set_ylim(-0.5, gs - 0.5)

    # 4. Post-defense surface
    ax = axes[1, 0]
    im = ax.imshow(post.T, origin="lower", cmap=cmap, vmin=0, vmax=1, aspect="equal")
    ax.set_title("(d) Post-defense surface  f(D(x))")
    ax.set_xlabel("indirection a₁")
    ax.set_ylabel("authority a₂")
    plt.colorbar(im, ax=ax, fraction=0.046)

    # 5. Predicted (steep) vs actual persistent — the doubt-eliminator panel
    ax = axes[1, 1]
    pc = result.persistence
    classification = np.full(vals.shape, np.nan)
    for i, j in pc.true_positives:
        classification[i, j] = 0.5  # both — theorem confirmed
    for i, j in pc.false_positives_interior:
        classification[i, j] = 1.0  # predicted but not actual — counterexample
    for i, j in pc.false_positives_boundary:
        classification[i, j] = 0.75  # boundary FP — not a violation
    for i, j in pc.false_negatives:
        classification[i, j] = 0.0  # actual but not predicted — not a violation
    cmp_cmap = LinearSegmentedColormap.from_list(
        "cmp", ["#d69e2e", "#38a169", "#c53030"]
    )
    ax.imshow(vals.T, origin="lower", cmap="Greys", vmin=0, vmax=1, aspect="equal", alpha=0.18)
    if not np.isnan(classification).all():
        ax.imshow(
            np.ma.masked_where(np.isnan(classification), classification).T,
            origin="lower",
            cmap=cmp_cmap,
            vmin=0,
            vmax=1,
            aspect="equal",
            alpha=0.85,
        )
    # Legend
    from matplotlib.patches import Patch

    handles = [
        Patch(color="#38a169", label=f"steep ∩ persistent ({len(pc.true_positives)})"),
        Patch(color="#c53030", label=f"steep \\ persistent ({len(pc.false_positives)})"),
        Patch(color="#d69e2e", label=f"persistent \\ steep ({len(pc.false_negatives)})"),
    ]
    ax.legend(
        handles=handles,
        loc="upper right",
        fontsize=7,
        frameon=True,
        framealpha=0.85,
    )
    title = (
        f"(e) Predicted vs actual persistent"
        f"{'  · VIOLATION' if pc.theorem_violated else ''}"
    )
    ax.set_title(title)
    ax.set_xlabel("indirection a₁")
    ax.set_ylabel("authority a₂")

    # 6. Lipschitz parameter bar chart
    ax = axes[1, 2]
    e = result.estimates
    labels = ["L", "K", "ℓ", "G", "ℓ(K+1)"]
    vals_bar = [e.L, e.K, e.ell, e.G, e.ell * (e.K + 1.0)]
    colors = ["#2b6cb0", "#38a169", "#d69e2e", "#c53030", "#7b341e"]
    bars = ax.bar(labels, vals_bar, color=colors)
    for bar, v in zip(bars, vals_bar):
        ax.text(
            bar.get_x() + bar.get_width() / 2,
            bar.get_height(),
            f"{v:.2f}",
            ha="center",
            va="bottom",
            fontsize=9,
        )
    transversality = e.persistence_condition()
    title = f"(f) Estimates  ·  G > ℓ(K+1)? {'YES' if transversality else 'no'}"
    ax.set_title(title)
    ax.set_ylabel("value")
    ax.grid(axis="y", linestyle=":", alpha=0.5)

    path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(path, dpi=150, bbox_inches="tight")
    plt.close(fig)
