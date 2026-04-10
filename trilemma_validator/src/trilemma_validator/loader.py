"""Load alignment-deviation heatmaps from rethinking-evals output formats.

Supported inputs:
- .npy file produced by ``Archive.to_heatmap()`` (a 2D float array, NaN for empty cells).
- final_archive.json produced by ``Archive.export_to_json()`` (cells list with grid_position).
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np


@dataclass
class Heatmap:
    """Container for a 2D alignment-deviation heatmap.

    Attributes:
        values: 2D array of shape (grid_size, grid_size). NaN entries indicate empty cells
            that the experiment never visited; they are treated as "unknown" by the validator,
            not as safe.
        grid_size: Number of cells per dimension. Equal to ``values.shape[0]``.
        cell_width: Width of each grid cell in behavioral coordinates. Default ``1/grid_size``
            so the full grid spans the unit square [0, 1]^2.
        source_path: Where the heatmap was loaded from (for the report).
    """

    values: np.ndarray
    grid_size: int
    cell_width: float
    source_path: Path | None = None

    @property
    def filled_mask(self) -> np.ndarray:
        """Boolean mask of cells with a known (non-NaN) value."""
        return ~np.isnan(self.values)

    @property
    def coverage(self) -> float:
        """Fraction of grid cells with a known value, in [0, 1]."""
        return float(self.filled_mask.mean())


def load_npy(path: Path) -> Heatmap:
    """Load a heatmap from a .npy file (raw output of ``Archive.to_heatmap()``)."""
    arr = np.load(path)
    if arr.ndim != 2 or arr.shape[0] != arr.shape[1]:
        raise ValueError(
            f"Expected a square 2D heatmap, got shape {arr.shape} from {path}"
        )
    return Heatmap(
        values=arr.astype(float),
        grid_size=arr.shape[0],
        cell_width=1.0 / arr.shape[0],
        source_path=path,
    )


def load_archive_json(path: Path) -> Heatmap:
    """Load a heatmap from a final_archive.json (rethinking-evals format).

    The JSON has shape::

        {
            "grid_size": 25,
            "cells": [
                {"grid_position": [i, j], "behavior": [a1, a2], "quality": 0.92, ...},
                ...
            ]
        }

    Empty cells are absent from the list and become NaN in the resulting heatmap.
    """
    with path.open("r") as f:
        data = json.load(f)
    grid_size = int(data["grid_size"])
    arr = np.full((grid_size, grid_size), np.nan, dtype=float)
    for cell in data["cells"]:
        i, j = cell["grid_position"]
        arr[int(i), int(j)] = float(cell["quality"])
    return Heatmap(
        values=arr,
        grid_size=grid_size,
        cell_width=1.0 / grid_size,
        source_path=path,
    )


def load(path: Path) -> Heatmap:
    """Auto-detect the file format from the suffix and load the heatmap."""
    path = Path(path)
    if path.suffix == ".npy":
        return load_npy(path)
    if path.suffix == ".json":
        return load_archive_json(path)
    raise ValueError(
        f"Unsupported heatmap format: {path.suffix}. Use .npy or .json."
    )
