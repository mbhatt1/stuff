"""Generate synthetic alignment-deviation heatmaps that mimic the three model
shapes from the Defense Trilemma paper.

These are *not* meant to be realistic LLM behavior — they exist so that the
validator can be tested end-to-end without spending OpenAI credits, and so that
each branch of the validation logic (applicable / non-applicable, transversality
holds / fails, etc.) has a corresponding fixture.

Three shapes are supported:

* ``mesa``    — large near-uniform high-AD plateau with a sharp boundary
                (Llama-3-8B in the paper). The directional gradient G is large
                relative to the defense-path Lipschitz constant ℓ, so the
                persistence condition holds and the trilemma applies.
* ``mosaic``  — many small basins separated by safe corridors. Resembles
                GPT-OSS-20B in the paper. The trilemma applies but the
                persistent set is fragmented.
* ``flat``    — peak AD just at τ, no points strictly above. Resembles
                GPT-5-Mini. The trilemma is *not* applicable, and the
                validator should report this correctly.
"""

from __future__ import annotations

import numpy as np

from .loader import Heatmap


def _smooth(arr: np.ndarray, sigma: float) -> np.ndarray:
    """Cheap separable Gaussian smoothing without scipy.

    Convolves with a 1D kernel along each axis. ``sigma`` is in cells.
    """
    if sigma <= 0:
        return arr
    radius = max(1, int(np.ceil(3 * sigma)))
    x = np.arange(-radius, radius + 1)
    kernel = np.exp(-(x**2) / (2 * sigma * sigma))
    kernel /= kernel.sum()
    out = arr
    for axis in (0, 1):
        out = np.apply_along_axis(
            lambda v: np.convolve(v, kernel, mode="same"), axis, out
        )
    return out


def synth_mesa(grid_size: int = 25, seed: int = 0) -> Heatmap:
    """Mesa: a single large plateau, sharp drop at the boundary."""
    rng = np.random.default_rng(seed)
    ii, jj = np.indices((grid_size, grid_size))
    cx, cy = grid_size * 0.55, grid_size * 0.55
    radius = grid_size * 0.30
    dist = np.hypot(ii - cx, jj - cy)
    # Sharp sigmoidal mesa.
    plateau = 1.0 / (1.0 + np.exp((dist - radius) * 1.6))
    arr = 0.05 + 0.90 * plateau
    arr += rng.normal(0, 0.015, arr.shape)
    arr = _smooth(arr, sigma=0.6)
    arr = np.clip(arr, 0.0, 1.0)
    return Heatmap(values=arr, grid_size=grid_size, cell_width=1.0 / grid_size)


def synth_mosaic(grid_size: int = 25, seed: int = 0) -> Heatmap:
    """Mosaic: many small basins on a low-AD background."""
    rng = np.random.default_rng(seed)
    arr = np.full((grid_size, grid_size), 0.20)
    n_basins = 15
    for _ in range(n_basins):
        ci = rng.integers(2, grid_size - 2)
        cj = rng.integers(2, grid_size - 2)
        amplitude = rng.uniform(0.45, 0.85)
        sigma = rng.uniform(1.5, 2.5)
        ii, jj = np.indices((grid_size, grid_size))
        bump = amplitude * np.exp(-((ii - ci) ** 2 + (jj - cj) ** 2) / (2 * sigma * sigma))
        arr = np.maximum(arr, 0.20 + bump)
    arr += rng.normal(0, 0.02, arr.shape)
    arr = _smooth(arr, sigma=0.4)
    arr = np.clip(arr, 0.0, 1.0)
    return Heatmap(values=arr, grid_size=grid_size, cell_width=1.0 / grid_size)


def synth_flat(grid_size: int = 25, seed: int = 0) -> Heatmap:
    """Flat: peak AD just at τ = 0.5, no cells strictly above."""
    rng = np.random.default_rng(seed)
    ii, jj = np.indices((grid_size, grid_size))
    cx, cy = grid_size * 0.5, grid_size * 0.5
    dist = np.hypot(ii - cx, jj - cy) / (grid_size * 0.5)
    arr = 0.15 + 0.30 * np.exp(-2.5 * dist**2)
    arr += rng.normal(0, 0.01, arr.shape)
    arr = _smooth(arr, sigma=0.5)
    # Hard-cap at the threshold to mimic the GPT-5-Mini case where U_τ = ∅.
    arr = np.clip(arr, 0.0, 0.499)
    return Heatmap(values=arr, grid_size=grid_size, cell_width=1.0 / grid_size)


def make(shape: str, *, grid_size: int = 25, seed: int = 0) -> Heatmap:
    """Factory: ``shape`` ∈ {mesa, mosaic, flat}."""
    if shape == "mesa":
        return synth_mesa(grid_size=grid_size, seed=seed)
    if shape == "mosaic":
        return synth_mosaic(grid_size=grid_size, seed=seed)
    if shape == "flat":
        return synth_flat(grid_size=grid_size, seed=seed)
    raise ValueError(f"Unknown shape: {shape!r}. Choices: mesa, mosaic, flat.")
