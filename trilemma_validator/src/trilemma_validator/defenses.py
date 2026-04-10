"""Defense simulators that produce a discrete map ``D : grid → grid``.

Each defense returns a ``DefenseMap``: an int array ``targets`` of shape
``(grid_size, grid_size, 2)`` where ``targets[i, j]`` is the cell that ``(i, j)``
is sent to by the defense. Cells that are unfilled (NaN in the heatmap) are
mapped to themselves and excluded from downstream metrics.

The defenses here are deliberately discrete and operate on the same grid as the
input heatmap. They are *not* meant to be the actual production defenses; they
are stand-ins that let us measure the empirical Lipschitz constants and check
the trilemma's persistence condition on real alignment-deviation surfaces.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Optional

import numpy as np

from .loader import Heatmap


@dataclass
class DefenseMap:
    """Discrete defense ``D``, expressed as a per-cell target on the grid.

    Attributes:
        targets: Int array of shape ``(grid_size, grid_size, 2)``. ``targets[i, j]`` is
            the ``(i', j')`` index of the cell that ``(i, j)`` is sent to by the defense.
        name: Human-readable name of the defense (used in reports).
        params: Free-form dict of parameters used to construct the defense.
    """

    targets: np.ndarray  # shape (G, G, 2), int
    name: str
    params: dict

    @property
    def grid_size(self) -> int:
        return int(self.targets.shape[0])

    def displaced_mask(self) -> np.ndarray:
        """Boolean mask of cells whose target is different from themselves."""
        gs = self.grid_size
        ii, jj = np.indices((gs, gs))
        return (self.targets[..., 0] != ii) | (self.targets[..., 1] != jj)


class Defense(ABC):
    """Base class for defenses. Subclasses implement ``build``."""

    name: str

    @abstractmethod
    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        """Construct the per-cell target map for the given heatmap and threshold."""
        raise NotImplementedError


def _safe_mask(heatmap: Heatmap, tau: float) -> np.ndarray:
    """Return a boolean mask of strictly-safe filled cells (``f(x) < tau``)."""
    return heatmap.filled_mask & (heatmap.values < tau)


def _identity_targets(grid_size: int) -> np.ndarray:
    """Identity target map: ``targets[i, j] = (i, j)``."""
    ii, jj = np.indices((grid_size, grid_size))
    return np.stack([ii, jj], axis=-1).astype(int)


class IdentityDefense(Defense):
    """``D(x) = x`` everywhere. Lipschitz constant 1, defense-path Lipschitz 0."""

    name = "identity"

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        return DefenseMap(
            targets=_identity_targets(heatmap.grid_size),
            name=self.name,
            params={},
        )


class NearestSafeDefense(Defense):
    """``D(x) = arg min_{s ∈ S} dist(s, x)`` for unsafe ``x``; identity on safe.

    The nearest-safe projection is *complete by construction* on the discrete grid
    (every unsafe cell is sent to a safe cell), but it is typically not Lipschitz
    in any useful sense — it has discontinuities along the safe-region cut locus.
    Comparing it against the bounded-step defense shows the trilemma's tradeoff:
    completeness costs an unbounded Lipschitz constant.
    """

    name = "nearest_safe"

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        gs = heatmap.grid_size
        targets = _identity_targets(gs)
        safe = _safe_mask(heatmap, tau)
        if not safe.any():
            # No safe cells: defense cannot do anything; identity by convention.
            return DefenseMap(targets=targets, name=self.name, params={})

        safe_idx = np.argwhere(safe)
        for i in range(gs):
            for j in range(gs):
                if not heatmap.filled_mask[i, j] or safe[i, j]:
                    continue
                d2 = (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
                k = int(np.argmin(d2))
                targets[i, j] = safe_idx[k]
        return DefenseMap(targets=targets, name=self.name, params={})


class BoundedStepDefense(Defense):
    """Like nearest-safe projection, but with a hard cap on displacement.

    For each unsafe filled cell ``(i, j)``:
      1. Find the nearest filled safe cell ``s`` (Euclidean grid distance).
      2. If ``dist(s, (i, j)) <= max_step``, jump to ``s``.
      3. Otherwise, take a single grid step from ``(i, j)`` toward ``s`` and stop.

    Step (3) means that for unsafe cells whose nearest safe cell is more than
    ``max_step`` cells away, the defense moves them by exactly one grid cell —
    they remain unsafe after defense. This is the persistence-theorem regime.
    """

    name = "bounded_step"

    def __init__(self, max_step: int = 2):
        if max_step < 1:
            raise ValueError("max_step must be >= 1 (in grid cells)")
        self.max_step = int(max_step)

    def build(self, heatmap: Heatmap, tau: float) -> DefenseMap:
        gs = heatmap.grid_size
        targets = _identity_targets(gs)
        safe = _safe_mask(heatmap, tau)
        if not safe.any():
            return DefenseMap(
                targets=targets, name=self.name, params={"max_step": self.max_step}
            )

        safe_idx = np.argwhere(safe)
        for i in range(gs):
            for j in range(gs):
                if not heatmap.filled_mask[i, j] or safe[i, j]:
                    continue
                # Nearest filled safe cell.
                d2 = (safe_idx[:, 0] - i) ** 2 + (safe_idx[:, 1] - j) ** 2
                k = int(np.argmin(d2))
                si, sj = safe_idx[k]
                d = float(np.sqrt(d2[k]))
                if d <= self.max_step:
                    targets[i, j] = (si, sj)
                else:
                    # Move one grid step toward (si, sj). We use sign of the difference,
                    # which gives a Chebyshev (king-move) step that's always within the grid.
                    di = int(np.sign(si - i))
                    dj = int(np.sign(sj - j))
                    ti, tj = i + di, j + dj
                    if 0 <= ti < gs and 0 <= tj < gs:
                        targets[i, j] = (ti, tj)
                    # else: clamped, keep identity
        return DefenseMap(
            targets=targets, name=self.name, params={"max_step": self.max_step}
        )


def get_defense(name: str, *, max_step: Optional[int] = None) -> Defense:
    """Factory: build a defense by name."""
    if name == "identity":
        return IdentityDefense()
    if name == "nearest_safe":
        return NearestSafeDefense()
    if name == "bounded_step":
        return BoundedStepDefense(max_step=max_step or 2)
    raise ValueError(
        f"Unknown defense: {name!r}. Choices: identity, nearest_safe, bounded_step."
    )
