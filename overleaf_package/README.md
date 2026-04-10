# Defense Trilemma — Overleaf Upload Package

This bundle contains both versions of the Defense Trilemma paper plus
the figure asset they reference, ready to upload to Overleaf as a
single project.

## Contents

```
overleaf_package/
├── paper2_v2.tex            ← arXiv-style version (article class)
├── paper2_neurips.tex       ← NeurIPS preprint version (uses neurips_2025.sty)
├── neurips_2025.sty         ← NeurIPS 2025 LaTeX style file
├── figures/
│   └── eps_robust_saturated.pdf  ← Per-cell ε-robust validation figure
└── README.md                ← this file
```

## How to use on Overleaf

1. Create a new **Blank Project** on Overleaf.
2. Click *Upload Project* and upload this entire directory (or the zip
   you downloaded).
3. In the Overleaf project settings, set the **Main document** to the
   version you want to compile:
   - `paper2_v2.tex`         → 19-page arXiv-style PDF, ~376 KB
   - `paper2_neurips.tex`    → 16-page NeurIPS preprint PDF, ~371 KB
4. Set the **TeX Live version** to **2023** or later (any modern
   default works).
5. Click *Recompile*.

Both `.tex` files are self-contained (no external bibliography file —
references are inline `\bibitem` entries). The only asset they pull
in is `figures/eps_robust_saturated.pdf`, which is included.

## Differences between the two versions

| | `paper2_v2.tex` | `paper2_neurips.tex` |
|---|---|---|
| Document class | `article` (11pt) | `article` + `neurips_2025` package |
| Page width | full letter | NeurIPS column |
| Bibliography | `\bibitem` (numbered) | `\bibitem` (numbered) via `natbib` |
| Page count | 19 | 16 |
| Title block | Multi-line | NeurIPS `\And`-separated |

The mathematical content is identical. The NeurIPS version is the
publication-ready preprint; the arXiv version is the more verbose
read-along version.

## What changed in this revision

This version of the paper adds the live empirical validation of
Theorem 6.2 (Persistent Unsafe Region) against two real OpenAI
targets, including a saturated run on `gpt-3.5-turbo-0125` with
$82$ filled grid cells. See §11.4 ("Live Empirical Validation of
Theorem~\ref{thm:persistent}"), Tables 3 and 4, and the figure
`eps_robust_saturated.pdf`.

The figure was generated from the live archive committed in
the project repository at
`trilemma_validator/live_runs/gpt35_turbo_t05_saturated/source_archive.json`.
The script that produced it is at
`trilemma_validator/scripts/make_paper_figure.py` and can be re-run
without API calls to reproduce the figure byte-for-byte.

## Repository

Full source, validator, and live archives:
<https://github.com/mbhatt1/defensetrilemma>
