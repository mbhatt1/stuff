# Live empirical validation results

These directories contain the outputs of running the full pipeline live
against the OpenAI API on two real targets, using
[`rethinking-evals`](https://github.com/kingroryg/rethinking-evals) to
produce the raw alignment-deviation grids and `trilemma validate` to
check Theorems 4.1 / 5.1 / 6.2 against them.

Each directory contains:

- `source_archive.json` — the raw `final_archive.json` from
  `rethinking-evals`, the input to the validator
- `heatmap.npy` — the 25×25 heatmap derived from the archive
- `result.json` — full validation result, including per-cell
  observations (`f`, `D(x)`, `f(D(x))`, distance to anchor, ε-robust
  LHS/RHS, steep/persistent membership)
- `report.md` — human-readable per-theorem report with the
  predicted-vs-empirical confusion matrix
- `validation.png` — 6-panel diagnostic figure

## Headline result

Both runs use the canonical continuous defense (`identity`,
$K = 1$, $\ell = 0$). The predicted steep set
$\mathcal{S}_{\text{pred}} = \{x : f(x) > \tau + \ell(K{+}1)\,\text{dist}(x, z^*)\}$
exactly equals the actual persistent set
$\mathcal{S}_{\text{act}} = \{x : f(D(x)) > \tau\}$, with **0 interior
false positives** on either run — i.e. zero empirical counterexamples
to Theorem 6.2.

| Run | Target | τ | Filled cells | L | G | \|S_pred\| | \|S_act\| | TP | FP_int | FN |
|---|---|---|---|---|---|---|---|---|---|---|
| `gpt5_mini_t03` | gpt-5-mini-2025-08-07 | 0.30 | 14 | 6.13 | 6.13 | 7 | 7 | 7 | **0** | 0 |
| `gpt35_turbo_t05` | gpt-3.5-turbo-0125 | 0.50 | 9 | 11.44 | 11.44 | 7 | 7 | 7 | **0** | 0 |

## Reproducing

```bash
cd trilemma_validator
pip install -e .

# Validate either archive directly:
trilemma validate \
    --archive live_runs/gpt5_mini_t03/source_archive.json \
    --tau 0.3 --defense identity \
    --output /tmp/repro_gpt5_mini

trilemma validate \
    --archive live_runs/gpt35_turbo_t05/source_archive.json \
    --tau 0.5 --defense identity \
    --output /tmp/repro_gpt35_turbo
```

Both should reproduce the headline numbers above byte-for-byte.

## Re-running the live experiment

If you want to re-collect the underlying alignment-deviation grids
yourself:

```bash
git clone https://github.com/kingroryg/rethinking-evals
cd rethinking-evals && uv sync
export OPENAI_API_KEY=sk-...
cd ../trilemma_validator
trilemma pipeline \
    --rethinking-path ../rethinking-evals \
    --model gpt5_mini --iterations 5 --seed-prompts 10 \
    --output /tmp/your_run
```

The actual grids you collect will differ from the ones here (MAP-Elites
is stochastic and the OpenAI APIs are non-deterministic at temperature
> 0), but the predicted-vs-empirical containment should hold on any
sample where the trilemma's preconditions are met.
