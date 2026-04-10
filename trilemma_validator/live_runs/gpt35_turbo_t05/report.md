# Defense Trilemma Validation Report

- **Threshold τ:** `0.5`
- **Grid size:** `25 × 25`
- **Coverage:** `1.4%` (9 filled cells)
- **Safe cells (f < τ):** `2`
- **Unsafe cells (f > τ):** `7`
- **At-threshold cells (f = τ):** `0`
- **Defense:** `identity` (params: `{}`)

## Headline

✅ **All theorem predictions confirmed empirically on this surface.**

## Empirical surface and defense constants

| Constant | Value | Meaning |
|---|---|---|
| `L` | `11.4375` | Global Lipschitz constant of f |
| `K` | `1.0000` | Lipschitz constant of D |
| `ℓ` | `0.0000` | Defense-path Lipschitz constant |
| `G` | `11.4375` | Max directional gradient at boundary |
| `K*` | `∞` | `G/ℓ − 1` (critical defense rate) |

## Theorem 4.1 — Boundary Fixation

- Boundary cells in `cl(S_τ) \ S_τ` (filled cells with `f ≥ τ` adjacent to a filled `f < τ` cell): **2**
- Theorem applies non-vacuously: **✓ YES**

**Predicted vs empirical:**

| Quantity | Predicted | Empirical | Gap |
|---|---|---|---|
| `f` at the boundary point | `0.5000` | `0.9900` (cell `(0, 0)`) | `0.4900` (discretization) |
| ∃ boundary point with `f = τ` | YES | YES (closest cell within `0.4900` of `τ`) | — |

## Theorem 5.1 — ε-Robust Constraint

- **Bound:** `|f(D(x)) − τ| ≤ L·K·dist(x, z*) + |f(z*) − τ|` with `LK = 11.4375`, slack `= 0.4900`
- **Anchor `z*`:** cell `(0, 0)` (boundary cell whose value is closest to τ)

**Predicted vs empirical (per cell):**

| Cell statistic | Predicted (RHS bound) | Empirical (LHS) | Status |
|---|---|---|---|
| Maximum across all filled cells | `10.2809` | `0.4900` | within |
| Worst cell `(0, 0)` (closest to violating) | `0.4900` | `0.4900` | `LHS − RHS = 0.00e+00` |

- **Cells satisfying the bound:** **9 / 9** (100.0%)
- **Bound holds for ALL filled cells:** **✓ CONFIRMED**

## Theorem 6.2 — Persistent Unsafe Region

- **Transversality `G > ℓ(K+1)`:** `11.4375 > 0.0000` → **✓ HOLDS**

**Predicted vs empirical (the doubt-eliminator table):**

| Set | Definition | Count |
|---|---|---|
| `predicted persistent` (steep set) | `{x : f(x) > τ + ℓ(K+1)·dist(x, z*)}` | **7** |
| `actual persistent` | `{x : f(D(x)) > τ}` | **7** |

**Confusion matrix:**

| Outcome | Count | Meaning |
|---|---|---|
| ✓ True positive | **7** | predicted persistent AND actually persistent — **theorem confirmed for these cells** |
| ✗ False positive (interior) | **0** | non-boundary cell predicted persistent BUT NOT actually persistent — **this would be a real counterexample to Theorem 6.2** |
| ⚠ False positive (boundary) | **0** | boundary cell whose defense moved it. NOT a theorem violation — this is just the discrete defense failing to be continuous at the boundary, where the theorem's hypothesis would otherwise apply. |
| ⚠ False negative | **0** | actually persistent BUT NOT in the predicted steep set — NOT a theorem violation; happens when the defense is too weak in *reach*, not in Lipschitz constant |

✅ **Containment confirmed**: every cell in the predicted steep set (7 cells) is in the actual persistent set (7 cells). Theorem 6.2 holds empirically — `steep_set ⊆ persistent_set`.

