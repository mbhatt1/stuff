# trilemma-validator

Empirical validator for the [Defense Trilemma](https://github.com/mbhatt1/defensetrilemma) theorems. Loads an alignment-deviation heatmap (produced by [`rethinking-evals`](https://github.com/kingroryg/rethinking-evals) or any compatible source), applies a discrete defense, and checks Theorems 4.1, 5.1, and 6.2 against the actual surface.

## Install

From this directory:

```bash
pip install -e .             # or: uv pip install -e .
```

This installs a single command, `trilemma`.

## Quick start: synthetic surface (no API calls)

The fastest way to verify the validator works is to run it on a synthetic mesa-shaped surface that mimics Llama-3-8B from the paper:

```bash
trilemma synth --shape mesa --output ./out_mesa
```

This produces:

```
out_mesa/
├── heatmap.npy        # raw 25×25 array
├── result.json        # full validation result, machine-readable
├── report.md          # human-readable report with PASS/FAIL per theorem
└── validation.png     # 6-panel diagnostic figure
```

Three synthetic shapes are available (`--shape mesa | mosaic | flat`). The `flat` shape mimics GPT-5-Mini and should report the trilemma as **not applicable** — a precision check that the validator correctly stays silent when the unsafe region is empty.

## Quick start: real model via OpenAI

Once you have `rethinking-evals` cloned and `OPENAI_API_KEY` set, run the full pipeline:

```bash
trilemma pipeline \
    --rethinking-path /path/to/rethinking-evals \
    --model gpt5_mini \
    --iterations 100 \
    --seed-prompts 50 \
    --output ./out_gpt5
```

This invokes `rethinking-evals` (via `uv run` if available, otherwise the current Python) to produce a `final_archive.json`, then validates the resulting heatmap against all three theorems.

For just the experiment (no validation):

```bash
trilemma experiment --rethinking-path /path/to/rethinking-evals --model gpt5_mini
```

For just validation of a heatmap that already exists:

```bash
trilemma validate --archive /path/to/final_archive.json
trilemma validate --heatmap /path/to/heatmap.npy
```

## What the validator computes

For each input heatmap (with safety threshold `τ`, default 0.5) and a chosen defense `D`, it computes:

| Symbol | Meaning |
|---|---|
| `L` | Global Lipschitz constant of `f`, from grid finite differences. |
| `K` | Lipschitz constant of `D`, from grid finite differences over the defense's outputs. |
| `ℓ` | Defense-path Lipschitz constant `sup |f(D(x)) − f(x)| / dist(D(x), x)`. |
| `G` | Maximum directional rate at which `f` rises across the safe-unsafe boundary. |
| `K*` | Critical defense rate `G/ℓ − 1`. |

Then it runs three theorem checks:

* **Theorem 4.1 (Boundary Fixation):** every boundary cell `z ∈ closure(S_τ) ∖ S_τ` must satisfy `D(z) = z`. Reports the count of boundary cells and the number that the defense fixes.
* **Theorem 5.1 (ε-Robust Constraint):** for the densest boundary anchor `z`, checks that `|f(D(x)) − τ| ≤ L·K·dist(x, z)` for every filled cell. Reports the worst violation.
* **Theorem 6.2 (Persistent Unsafe Region):** checks the transversality condition `G > ℓ(K + 1)` and enumerates the empirical persistent set `{x : f(D(x)) > τ}`. Reports whether the empirical result is consistent with the theorem's prediction.

## Defenses

| Name | Behavior | When to use |
|---|---|---|
| `identity` | `D(x) = x` everywhere | Sanity check; gives the maximum persistent set (all of `U_τ`). |
| `nearest_safe` | Each unsafe cell jumps to the closest safe cell. | Trivially complete on the discrete grid, but discontinuous — has no useful Lipschitz constant. Comparison point. |
| `bounded_step` *(default)* | Each unsafe cell moves up to `--max-step` cells toward the nearest safe cell. | The most informative for the trilemma: parameterized by displacement, naturally produces a non-trivial `K`, and exposes the `K`-tradeoff from the dilemma. |

The default `bounded_step` defense with `--max-step 2` is a reasonable starting point. Increase `--max-step` to make the defense more aggressive (lower persistent set, larger ε-band).

## Outputs

Every command writes the same bundle to `--output`:

* `heatmap.npy` — raw heatmap (always written, even when loading from `.json`)
* `result.json` — full validation result; the canonical machine-readable output
* `report.md` — human-readable markdown report
* `validation.png` — 6-panel diagnostic figure: original surface, regions, defense displacements, post-defense surface, persistent set, parameter bar chart

## Limitations

* **Discrete grid only.** All Lipschitz/gradient estimates are finite differences on the grid the heatmap was sampled at. Coarser grids give cruder estimates of `L` and `G`. Run `rethinking-evals` with a larger grid (`grid_size` in `experiments.yaml`) for tighter bounds.
* **Empty cells are unknown, not safe.** MAP-Elites typically leaves many cells unfilled. The validator uses only filled cells for every metric.
* **The defenses are toys.** `nearest_safe` and `bounded_step` are stand-ins that let us measure `K` and `ℓ` empirically. They are not the production-grade wrappers the paper rules out — but the *measurements* they give of `L`, `G`, `ℓ` are surface properties of `f`, independent of the defense, and these are what matter for the trilemma's preconditions.
