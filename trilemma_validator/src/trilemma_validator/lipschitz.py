"""Empirical estimators for the Lipschitz constants and directional gradients
that appear in the Defense Trilemma theorems.

All estimates use grid-based finite differences. The grid spacing is the
heatmap's ``cell_width`` (defaults to ``1/grid_size`` so the unit square is
covered). Distances between cells are measured in continuous coordinates
(grid index times cell width), Euclidean.

Conventions:

* ``L``       — global Lipschitz constant of the alignment-deviation surface ``f``.
* ``K``       — Lipschitz constant of the defense map ``D``.
* ``ell``     — defense-path Lipschitz constant: how much ``f`` varies along
                the displacement direction ``D(x) - x``. Always ``<= L``.
* ``G``       — maximum directional rate at which ``f`` rises crossing the
                safe-unsafe boundary. Estimated from finite differences across
                neighboring cells where the threshold is crossed.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from .defenses import DefenseMap
from .loader import Heatmap


# 8-neighborhood offsets (Chebyshev/king moves). We use the 8-neighborhood
# rather than 4 because diagonal moves give a tighter L estimate (smaller
# distances are also tested) and they let G be estimated in oblique directions.
_NEIGHBORS = np.array(
    [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)],
    dtype=int,
)


@dataclass
class LipschitzEstimates:
    """Container for the four core estimates."""

    L: float
    K: float
    ell: float
    G: float

    @property
    def K_star(self) -> float:
        """Critical defense Lipschitz constant ``K* = G/ell - 1``.

        Returns ``+inf`` when ``ell == 0`` (the identity defense, where the
        persistence condition ``G > ell(K+1)`` is automatically satisfied for
        any positive ``G``).
        """
        if self.ell <= 0:
            return float("inf")
        return self.G / self.ell - 1.0

    def persistence_condition(self) -> bool:
        """Return True iff the persistence condition ``G > ell * (K + 1)`` holds."""
        return self.G > self.ell * (self.K + 1.0)

    def to_dict(self) -> dict:
        return {
            "L": self.L,
            "K": self.K,
            "ell": self.ell,
            "G": self.G,
            "K_star": self.K_star,
            "persistence_condition_met": self.persistence_condition(),
        }


def _cell_dist(a: tuple[int, int], b: tuple[int, int], cell_width: float) -> float:
    return float(np.hypot(a[0] - b[0], a[1] - b[1]) * cell_width)


def _filled_indices(heatmap: Heatmap) -> np.ndarray:
    """Return an (n, 2) int array of (i, j) for every filled cell."""
    return np.argwhere(heatmap.filled_mask)


def estimate_global_L(heatmap: Heatmap) -> float:
    """Empirical global Lipschitz constant of ``f`` over all pairs of filled cells.

    For each pair ``(a, b)`` of filled cells, computes ``|f(a) - f(b)| / dist(a, b)``
    and returns the maximum. On dense grids this is dominated by adjacent pairs;
    on sparse grids it gracefully handles the case where no two filled cells
    are grid-adjacent.

    Returns 0.0 when fewer than two cells are filled.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0
    fvals = vals[idx[:, 0], idx[:, 1]]
    # All-pairs distance and value-difference matrices.
    di = idx[:, 0:1] - idx[:, 0:1].T
    dj = idx[:, 1:2] - idx[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    diff = np.abs(fvals[:, None] - fvals[None, :])
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(dist > 0, diff / dist, 0.0)
    return float(ratio.max())


def estimate_defense_K(defense: DefenseMap, heatmap: Heatmap) -> float:
    """Empirical Lipschitz constant of the defense map ``D`` over all filled pairs.

    Computes ``K = max dist(D(u), D(v)) / dist(u, v)`` over all pairs ``(u, v)``
    of filled cells. Returns 0.0 if fewer than two cells are filled.
    """
    h = heatmap.cell_width
    targets = defense.targets
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0

    src = idx.astype(float)
    tgt = targets[idx[:, 0], idx[:, 1]].astype(float)

    di = src[:, 0:1] - src[:, 0:1].T
    dj = src[:, 1:2] - src[:, 1:2].T
    in_dist = np.hypot(di, dj) * h

    tdi = tgt[:, 0:1] - tgt[:, 0:1].T
    tdj = tgt[:, 1:2] - tgt[:, 1:2].T
    out_dist = np.hypot(tdi, tdj) * h

    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(in_dist > 0, out_dist / in_dist, 0.0)
    return float(ratio.max())


def estimate_defense_path_ell(defense: DefenseMap, heatmap: Heatmap) -> float:
    """Empirical defense-path Lipschitz constant ``ell``.

    For each cell ``x`` where ``D(x) != x``, compute
    ``|f(D(x)) - f(x)| / dist(D(x), x)`` and take the maximum. Returns 0.0 when
    the defense is the identity (no displaced cells), matching the convention
    in the paper of taking the supremum over the empty set as 0.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    targets = defense.targets

    best = 0.0
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            ti, tj = int(targets[i, j, 0]), int(targets[i, j, 1])
            if (ti, tj) == (i, j):
                continue
            if not filled[ti, tj]:
                continue
            d = h * float(np.hypot(ti - i, tj - j))
            if d <= 0:
                continue
            ratio = abs(float(vals[ti, tj] - vals[i, j])) / d
            if ratio > best:
                best = ratio
    return best


def estimate_boundary_gradient_G(heatmap: Heatmap, tau: float) -> float:
    """Estimate the maximum directional rate at which ``f`` rises across the boundary.

    For every pair of filled cells ``(a, b)`` such that ``f(a) < tau`` and
    ``f(b) > tau`` (i.e., the line from ``a`` to ``b`` crosses the threshold),
    compute the rise per unit distance ``(f(b) - f(a)) / dist(a, b)``. Return
    the maximum. This is the largest empirical directional rate at which the
    surface crosses the threshold — the ``G`` in the transversality condition.

    Uses all-pairs over filled cells (not just grid neighbors), so the estimate
    is meaningful even on very sparse grids.
    """
    h = heatmap.cell_width
    vals = heatmap.values
    idx = _filled_indices(heatmap)
    n = len(idx)
    if n < 2:
        return 0.0
    fvals = vals[idx[:, 0], idx[:, 1]]
    safe = fvals < tau
    unsafe = fvals > tau
    if not safe.any() or not unsafe.any():
        return 0.0

    safe_idx = np.where(safe)[0]
    unsafe_idx = np.where(unsafe)[0]
    sa = idx[safe_idx]
    ub = idx[unsafe_idx]
    sa_f = fvals[safe_idx]
    ub_f = fvals[unsafe_idx]

    di = ub[:, 0:1] - sa[:, 0:1].T
    dj = ub[:, 1:2] - sa[:, 1:2].T
    dist = np.hypot(di, dj).astype(float) * h
    rise = ub_f[:, None] - sa_f[None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        ratio = np.where(dist > 0, rise / dist, 0.0)
    return float(ratio.max())


def estimate_all(
    heatmap: Heatmap, defense: DefenseMap, tau: float
) -> LipschitzEstimates:
    """Run all four estimators and return them as a single dataclass."""
    return LipschitzEstimates(
        L=estimate_global_L(heatmap),
        K=estimate_defense_K(defense, heatmap),
        ell=estimate_defense_path_ell(defense, heatmap),
        G=estimate_boundary_gradient_G(heatmap, tau),
    )
