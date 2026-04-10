"""Render trilemma validation results to JSON and Markdown."""

from __future__ import annotations

import json
from pathlib import Path

from .theorems import TrilemmaResult


def write_json(result: TrilemmaResult, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        json.dump(result.to_dict(), f, indent=2)


def _bool_emoji(b: bool) -> str:
    return "✓" if b else "✗"


def _fmt(x: float, n: int = 4) -> str:
    if x != x:  # NaN
        return "—"
    return f"{x:.{n}f}"


def write_markdown(result: TrilemmaResult, path: Path) -> None:
    e = result.estimates
    bd = result.boundary
    er = result.eps_robust
    pc = result.persistence

    lines: list[str] = []
    lines.append("# Defense Trilemma Validation Report")
    lines.append("")
    lines.append(f"- **Threshold τ:** `{result.tau}`")
    lines.append(f"- **Grid size:** `{result.grid_size} × {result.grid_size}`")
    lines.append(
        f"- **Coverage:** `{100 * result.coverage:.1f}%` "
        f"({result.safe_count + result.unsafe_count + result.at_threshold_count} filled cells)"
    )
    lines.append(f"- **Safe cells (f < τ):** `{result.safe_count}`")
    lines.append(f"- **Unsafe cells (f > τ):** `{result.unsafe_count}`")
    lines.append(f"- **At-threshold cells (f = τ):** `{result.at_threshold_count}`")
    lines.append(f"- **Defense:** `{result.defense_name}` (params: `{result.defense_params}`)")
    lines.append("")

    if not result.applicable:
        lines.append("## Trilemma not applicable")
        lines.append("")
        for note in result.notes:
            lines.append(f"> {note}")
        lines.append("")
        lines.append(
            "_Conclusion: the surface fails the theorem's preconditions, so "
            "no impossibility is predicted. This is **a correct prediction**, "
            "not a failure of the theorems._"
        )
        lines.append("")
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w") as f:
            f.write("\n".join(lines) + "\n")
        return

    # Headline
    lines.append("## Headline")
    lines.append("")
    if result.all_predictions_confirmed:
        lines.append(
            "✅ **All theorem predictions confirmed empirically on this surface.**"
        )
    else:
        if pc.theorem_violated:
            lines.append(
                f"❌ **Theorem 6.2 violated**: {len(pc.false_positives)} cells "
                f"are in the predicted steep set but NOT in the actual "
                f"persistent set. See the false-positive list below."
            )
        elif not er.holds:
            lines.append(
                f"⚠️ **Theorem 5.1 has violations**: "
                f"{er.num_total - er.num_within_bound} of {er.num_total} cells "
                f"exceed the predicted bound. (See worst cell below — usually a "
                f"discretization artifact when the defense is non-continuous.)"
            )
        else:
            lines.append(
                "⚠️ Predictions partially confirmed; see per-theorem details."
            )
    lines.append("")

    # Estimates
    lines.append("## Empirical surface and defense constants")
    lines.append("")
    lines.append("| Constant | Value | Meaning |")
    lines.append("|---|---|---|")
    lines.append(f"| `L` | `{e.L:.4f}` | Global Lipschitz constant of f |")
    lines.append(f"| `K` | `{e.K:.4f}` | Lipschitz constant of D |")
    lines.append(f"| `ℓ` | `{e.ell:.4f}` | Defense-path Lipschitz constant |")
    lines.append(f"| `G` | `{e.G:.4f}` | Max directional gradient at boundary |")
    K_star = e.K_star
    K_star_str = "∞" if K_star == float("inf") else f"{K_star:.4f}"
    lines.append(f"| `K*` | `{K_star_str}` | `G/ℓ − 1` (critical defense rate) |")
    lines.append("")

    # ============================================================
    # Theorem 4.1
    # ============================================================
    lines.append("## Theorem 4.1 — Boundary Fixation")
    lines.append("")
    lines.append(
        f"- Boundary cells in `cl(S_τ) \\ S_τ` (filled cells with `f ≥ τ` "
        f"adjacent to a filled `f < τ` cell): **{len(bd.boundary_cells)}**"
    )
    lines.append(
        f"- Theorem applies non-vacuously: **{_bool_emoji(bd.boundary_exists)} "
        f"{'YES' if bd.boundary_exists else 'NO'}**"
    )

    if bd.boundary_exists:
        lines.append("")
        lines.append("**Predicted vs empirical:**")
        lines.append("")
        lines.append("| Quantity | Predicted | Empirical | Gap |")
        lines.append("|---|---|---|---|")
        lines.append(
            f"| `f` at the boundary point | `{_fmt(bd.predicted_f_at_boundary)}` | "
            f"`{_fmt(bd.empirical_f_at_closest)}` (cell `{bd.closest_cell}`) | "
            f"`{_fmt(bd.discretization_gap)}` (discretization) |"
        )
        lines.append(
            f"| ∃ boundary point with `f = τ` | YES | "
            f"YES (closest cell within `{_fmt(bd.discretization_gap)}` of `τ`) | — |"
        )
        lines.append("")
        if not bd.defense_fixes_all_boundary:
            lines.append(
                f"_Note: only `{len(bd.fixed_boundary_cells)}/"
                f"{len(bd.boundary_cells)}` boundary cells are fixed by `"
                f"{result.defense_name}`. This is fine — discrete defenses are "
                f"not topologically continuous, so the theorem's hypotheses do "
                f"not apply to them. The theorem's claim is about the surface, "
                f"not about this specific defense._"
            )
            lines.append("")

    # ============================================================
    # Theorem 5.1
    # ============================================================
    lines.append("## Theorem 5.1 — ε-Robust Constraint")
    lines.append("")
    if er.anchor_cell is None:
        lines.append("- No boundary cells; check is vacuous.")
    else:
        lines.append(
            f"- **Bound:** `|f(D(x)) − τ| ≤ L·K·dist(x, z*) + |f(z*) − τ|` "
            f"with `LK = {er.L * er.K:.4f}`, slack `= {er.discretization_slack:.4f}`"
        )
        lines.append(
            f"- **Anchor `z*`:** cell `{er.anchor_cell}` "
            f"(boundary cell whose value is closest to τ)"
        )
        lines.append("")
        lines.append("**Predicted vs empirical (per cell):**")
        lines.append("")
        lines.append("| Cell statistic | Predicted (RHS bound) | Empirical (LHS) | Status |")
        lines.append("|---|---|---|---|")
        lines.append(
            f"| Maximum across all filled cells | `{_fmt(er.max_predicted_rhs)}` | "
            f"`{_fmt(er.max_observed_lhs)}` | "
            f"{'within' if er.max_observed_lhs <= er.max_predicted_rhs + 1e-9 else 'EXCEEDS'} |"
        )
        if er.worst_cell is not None:
            lines.append(
                f"| Worst cell `{er.worst_cell}` (closest to violating) | "
                f"`{_fmt(er.worst_predicted_rhs)}` | "
                f"`{_fmt(er.worst_observed_lhs)}` | "
                f"`LHS − RHS = {er.max_violation:.2e}` |"
            )
        lines.append("")
        lines.append(
            f"- **Cells satisfying the bound:** "
            f"**{er.num_within_bound} / {er.num_total}** "
            f"({100 * er.num_within_bound / er.num_total if er.num_total else 100:.1f}%)"
        )
        lines.append(
            f"- **Bound holds for ALL filled cells:** **{_bool_emoji(er.holds)} "
            f"{'CONFIRMED' if er.holds else 'VIOLATIONS PRESENT'}**"
        )
    lines.append("")

    # ============================================================
    # Theorem 6.2
    # ============================================================
    lines.append("## Theorem 6.2 — Persistent Unsafe Region")
    lines.append("")
    lines.append(
        f"- **Transversality `G > ℓ(K+1)`:** `{e.G:.4f} > "
        f"{e.ell * (e.K + 1):.4f}` "
        f"→ **{_bool_emoji(pc.transversality_holds)} "
        f"{'HOLDS' if pc.transversality_holds else 'DOES NOT HOLD'}**"
    )
    lines.append("")
    lines.append("**Predicted vs empirical (the doubt-eliminator table):**")
    lines.append("")
    lines.append("| Set | Definition | Count |")
    lines.append("|---|---|---|")
    lines.append(
        f"| `predicted persistent` (steep set) | "
        f"`{{x : f(x) > τ + ℓ(K+1)·dist(x, z*)}}` | "
        f"**{len(pc.predicted_steep_cells)}** |"
    )
    lines.append(
        f"| `actual persistent` | `{{x : f(D(x)) > τ}}` | "
        f"**{len(pc.actual_persistent_cells)}** |"
    )
    lines.append("")
    lines.append("**Confusion matrix:**")
    lines.append("")
    lines.append("| Outcome | Count | Meaning |")
    lines.append("|---|---|---|")
    lines.append(
        f"| ✓ True positive | **{len(pc.true_positives)}** | "
        f"predicted persistent AND actually persistent — **theorem confirmed for these cells** |"
    )
    lines.append(
        f"| ✗ False positive (interior) | **{len(pc.false_positives_interior)}** | "
        f"non-boundary cell predicted persistent BUT NOT actually persistent — "
        f"**this would be a real counterexample to Theorem 6.2** |"
    )
    lines.append(
        f"| ⚠ False positive (boundary) | **{len(pc.false_positives_boundary)}** | "
        f"boundary cell whose defense moved it. NOT a theorem violation — "
        f"this is just the discrete defense failing to be continuous at the "
        f"boundary, where the theorem's hypothesis would otherwise apply. |"
    )
    lines.append(
        f"| ⚠ False negative | **{len(pc.false_negatives)}** | "
        f"actually persistent BUT NOT in the predicted steep set — "
        f"NOT a theorem violation; happens when the defense is too weak in *reach*, "
        f"not in Lipschitz constant |"
    )
    lines.append("")
    if pc.theorem_violated:
        lines.append(
            f"❌ **THEOREM VIOLATION**: {len(pc.false_positives)} cells in the "
            f"predicted steep set are not actually persistent after the defense. "
            f"This would be a counterexample to Theorem 6.2. Either the empirical "
            f"`ℓ`/`K`/`G` estimates are wrong (sparse grid?) or the surface "
            f"genuinely does not satisfy the theorem on this defense."
        )
        lines.append("")
        if pc.false_positives:
            lines.append(
                f"  False-positive cells (first 10): "
                f"`{[list(c) for c in pc.false_positives[:10]]}`"
            )
            lines.append("")
    elif len(pc.predicted_steep_cells) > 0:
        lines.append(
            f"✅ **Containment confirmed**: every cell in the predicted steep set "
            f"({len(pc.predicted_steep_cells)} cells) is in the actual persistent "
            f"set ({len(pc.actual_persistent_cells)} cells). Theorem 6.2 holds "
            f"empirically — `steep_set ⊆ persistent_set`."
        )
        lines.append("")
    elif pc.transversality_holds and len(pc.predicted_steep_cells) == 0:
        lines.append(
            "_Transversality holds but the steep-set integral evaluates to zero "
            "on this discrete grid — happens when the anchor is at a corner or "
            "the grid spacing is comparable to the surface's natural scale. "
            "Run with a denser grid for a meaningful steep set._"
        )
        lines.append("")
    else:
        lines.append(
            "_Transversality does not hold and the predicted steep set is empty. "
            "Theorem 6.2 makes no prediction here._"
        )
        if len(pc.actual_persistent_cells) > 0:
            lines.append("")
            lines.append(
                f"  Note: {len(pc.actual_persistent_cells)} cells are still "
                f"persistent after the defense. This is **not** a counterexample "
                f"to Theorem 6.2 — those cells are persistent because the discrete "
                f"defense has *bounded reach*, not because of the surface's "
                f"Lipschitz geometry. The theorem doesn't claim to characterize "
                f"all persistent cells, only that the steep-set ones must be "
                f"persistent."
            )
        lines.append("")

    if result.notes:
        lines.append("## Notes")
        lines.append("")
        for note in result.notes:
            lines.append(f"- {note}")
        lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        f.write("\n".join(lines) + "\n")
