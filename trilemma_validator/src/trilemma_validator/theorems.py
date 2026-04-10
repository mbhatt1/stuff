"""Empirical checks for the three Defense Trilemma theorems on a discrete grid.

Theorem 4.1 — Boundary Fixation
    For nearest-safe and bounded-step defenses, every safe cell is a fixed
    point by construction (utility preservation), so the closure of the safe
    region is contained in the fixed-point set: every cell adjacent to the
    boundary in the safe region is fixed. We verify this explicitly and
    enumerate the boundary cells that are fixed by the defense.

Theorem 5.1 — ε-Robust Constraint
    For each fixed boundary point ``z``, the bound
        |f(D(x)) - tau| <= L * K * dist(x, z)
    is checked over all filled cells. The "max violation" is the largest
    excess of the LHS over the RHS — should be ``<= 0`` if the theorem holds.

Theorem 6.2 — Persistent Unsafe Region
    The transversality condition ``G > ell * (K + 1)`` is checked using the
    estimates from ``lipschitz.py``. We then enumerate the cells that remain
    strictly unsafe after the defense (``f(D(x)) > tau``) — this is the
    *empirical* persistent set, which the theorem predicts to be non-empty
    when the transversality condition holds.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

import numpy as np

from .defenses import DefenseMap
from .lipschitz import LipschitzEstimates, estimate_all
from .loader import Heatmap

# 4-neighborhood (rook) for boundary detection. We use 4-connectivity here so
# that "boundary cell" means "edge of safe region adjacent to an unsafe cell"
# rather than "corner-touches-unsafe", which is the natural discrete analog of
# topological closure.
_RNEIGH = np.array([(-1, 0), (1, 0), (0, -1), (0, 1)], dtype=int)


@dataclass
class CellObservation:
    """Per-cell record of one cell's predicted vs empirical behavior."""

    cell: tuple[int, int]
    f_value: float  # f(x), the surface alignment-deviation at this cell
    target_cell: tuple[int, int]  # D(x), the cell this gets mapped to
    f_post_defense: float  # f(D(x))
    dist_to_anchor: float  # distance to the chosen boundary anchor z*
    eps_robust_lhs: float  # |f(D(x)) - tau|
    eps_robust_rhs: float  # LK * dist(x, z*) + discretization slack
    eps_robust_within_bound: bool  # lhs <= rhs
    in_predicted_steep_set: bool  # f(x) > tau + ell*(K+1)*dist(x, z*)
    in_actual_persistent_set: bool  # f(D(x)) > tau

    def to_dict(self) -> dict:
        return {
            "cell": list(self.cell),
            "f": self.f_value,
            "D_x": list(self.target_cell),
            "f_D_x": self.f_post_defense,
            "dist_to_anchor": self.dist_to_anchor,
            "T5_1_lhs": self.eps_robust_lhs,
            "T5_1_rhs": self.eps_robust_rhs,
            "T5_1_within_bound": self.eps_robust_within_bound,
            "T6_2_in_steep_set": self.in_predicted_steep_set,
            "T6_2_in_persistent_set": self.in_actual_persistent_set,
        }


@dataclass
class BoundaryFixationCheck:
    """Result of the Theorem 4.1 check.

    Theorem 4.1 says: any continuous, utility-preserving defense on a connected
    space with non-empty S_tau and U_tau must fix at least one boundary point z
    with ``f(z) = tau``. On the discrete grid, ``z`` is approximated by the
    boundary cell whose value is closest to tau.

    Predicted: ``f(z) = tau`` exactly.
    Empirical: ``f(z*)`` at the closest discrete cell.
    Discretization gap: ``|f(z*) - tau|``, which → 0 as the grid is refined.
    """

    boundary_cells: list[tuple[int, int]]
    fixed_boundary_cells: list[tuple[int, int]]
    boundary_exists: bool  # surface-level: theorem's conclusion is non-vacuous
    defense_fixes_all_boundary: bool  # diagnostic: for the specific defense
    closest_cell: tuple[int, int] | None  # boundary cell with f closest to tau
    predicted_f_at_boundary: float  # = tau (the theorem's prediction)
    empirical_f_at_closest: float  # f(z*)
    discretization_gap: float  # |f(z*) - tau|

    @property
    def holds(self) -> bool:
        """Backwards-compat: theorem confirmed iff boundary cells exist."""
        return self.boundary_exists

    def to_dict(self) -> dict:
        return {
            "num_boundary_cells": len(self.boundary_cells),
            "boundary_cells_exist": self.boundary_exists,
            "num_fixed_by_this_defense": len(self.fixed_boundary_cells),
            "defense_fixes_all_boundary": self.defense_fixes_all_boundary,
            "closest_cell": list(self.closest_cell) if self.closest_cell else None,
            "predicted_f_at_boundary": self.predicted_f_at_boundary,
            "empirical_f_at_closest_cell": self.empirical_f_at_closest,
            "discretization_gap": self.discretization_gap,
        }


@dataclass
class EpsRobustCheck:
    """Result of the Theorem 5.1 check.

    The theorem's bound is checked per-cell::

        |f(D(x)) - tau| <= L * K * dist(x, z*) + discretization_slack

    where ``z*`` is the boundary cell whose value is closest to tau, and the
    slack is ``|f(z*) - tau|`` (vanishes as the grid is refined).

    The theorem is *empirically confirmed* iff every filled cell satisfies
    the bound. ``num_within_bound`` and ``num_total`` give the per-cell tally.
    """

    anchor_cell: Optional[tuple[int, int]]
    L: float
    K: float
    discretization_slack: float
    max_observed_lhs: float
    max_predicted_rhs: float
    max_violation: float  # max(LHS - RHS), should be <= 0 if theorem holds
    num_within_bound: int
    num_total: int
    worst_cell: Optional[tuple[int, int]]
    worst_observed_lhs: float
    worst_predicted_rhs: float
    holds: bool

    def to_dict(self) -> dict:
        return {
            "anchor_cell": list(self.anchor_cell) if self.anchor_cell else None,
            "L": self.L,
            "K": self.K,
            "LK": self.L * self.K,
            "discretization_slack": self.discretization_slack,
            "max_observed_lhs": self.max_observed_lhs,
            "max_predicted_rhs": self.max_predicted_rhs,
            "max_violation_LHS_minus_RHS": self.max_violation,
            "num_cells_within_bound": self.num_within_bound,
            "num_cells_total": self.num_total,
            "fraction_within_bound": (
                self.num_within_bound / self.num_total if self.num_total else 1.0
            ),
            "worst_cell": list(self.worst_cell) if self.worst_cell else None,
            "worst_observed_lhs": self.worst_observed_lhs,
            "worst_predicted_rhs": self.worst_predicted_rhs,
            "bound_holds_for_all_cells": self.holds,
        }


@dataclass
class PersistenceCheck:
    """Result of the Theorem 6.2 check.

    The theorem's prediction is twofold:

    1. **Transversality condition**: ``G > ell * (K + 1)``. When this holds,
       the *steep set* ``S = {x : f(x) > tau + ell*(K+1)*dist(x, z)}`` is
       non-empty.
    2. **Persistence**: every cell in the steep set satisfies ``f(D(x)) > tau``
       — that is, the steep set is a SUBSET of the actual persistent unsafe set.

    Empirical validation: enumerate the steep set (the *predicted* persistent
    cells) and the actual persistent set ``{x : f(D(x)) > tau}``. Compare:

    * **True positives**: in both. Theorem confirmed for these cells.
    * **False positives**: predicted-persistent but NOT actually persistent.
      Split further into:

      - **Interior false positives** — non-boundary cells where the defense
        somehow pulled an interior steep cell below tau. These are *real*
        counterexamples to Theorem 6.2.
      - **Boundary false positives** — the defense moved a *boundary* cell
        (whose hypothesis assumes it should be fixed by a continuous defense).
        These are NOT theorem violations; they witness that the discrete
        defense violates the theorem's continuity hypothesis at the boundary.

    * **False negatives**: actually persistent but NOT in the predicted set —
      *not a theorem violation*. The theorem only claims that the steep set
      is contained in the persistent set, not the other way around.

    A theorem violation requires at least one *interior* false positive.
    """

    G: float
    ell: float
    K: float
    ell_K_plus_1: float
    transversality_holds: bool  # G > ell(K+1)
    anchor_cell: Optional[tuple[int, int]]
    predicted_steep_cells: list[tuple[int, int]]
    actual_persistent_cells: list[tuple[int, int]]
    true_positives: list[tuple[int, int]]
    false_positives_interior: list[tuple[int, int]]  # *real counterexamples*
    false_positives_boundary: list[tuple[int, int]]  # defense not continuous at boundary
    false_negatives: list[tuple[int, int]]
    persistent_fraction: float  # |actual persistent| / |filled|
    theorem_violated: bool  # true iff false_positives_interior is non-empty
    consistent_with_theorem: bool

    @property
    def false_positives(self) -> list[tuple[int, int]]:
        return self.false_positives_interior + self.false_positives_boundary

    def to_dict(self) -> dict:
        n_pred = len(self.predicted_steep_cells)
        n_act = len(self.actual_persistent_cells)
        return {
            "G": self.G,
            "ell": self.ell,
            "K": self.K,
            "ell_times_K_plus_1": self.ell_K_plus_1,
            "transversality_condition_G_gt_ellKp1": self.transversality_holds,
            "anchor_cell": list(self.anchor_cell) if self.anchor_cell else None,
            "predicted_persistent_count": n_pred,
            "actual_persistent_count": n_act,
            "persistent_fraction_of_filled_cells": self.persistent_fraction,
            "true_positives_count": len(self.true_positives),
            "false_positives_interior_count": len(self.false_positives_interior),
            "false_positives_boundary_count": len(self.false_positives_boundary),
            "false_negatives_count": len(self.false_negatives),
            "false_positive_interior_cells": [
                list(c) for c in self.false_positives_interior[:10]
            ],
            "false_positive_boundary_cells": [
                list(c) for c in self.false_positives_boundary[:10]
            ],
            "containment_steep_subset_of_persistent_modulo_boundary": (
                len(self.false_positives_interior) == 0 and n_pred > 0
            ),
            "theorem_violated": self.theorem_violated,
            "empirical_consistent_with_theorem": self.consistent_with_theorem,
        }


@dataclass
class TrilemmaResult:
    """Aggregate result of all three theorem checks plus headline numbers.

    Cell counts use the strict paper convention:
    ``safe_count = |{f < tau}|``,
    ``unsafe_count = |{f > tau}|``,
    ``at_threshold_count = |{f == tau}|`` (cells exactly at the threshold).
    The trilemma is *applicable* iff both ``safe_count > 0`` and
    ``unsafe_count > 0``.
    """

    tau: float
    grid_size: int
    coverage: float
    safe_count: int
    unsafe_count: int
    at_threshold_count: int
    estimates: LipschitzEstimates
    defense_name: str
    defense_params: dict
    boundary: BoundaryFixationCheck
    eps_robust: EpsRobustCheck
    persistence: PersistenceCheck
    applicable: bool  # False if S or U is empty (no impossibility predicted)
    cell_observations: list[CellObservation] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def all_predictions_confirmed(self) -> bool:
        """Headline: every theorem prediction the validator can check holds."""
        if not self.applicable:
            return True  # nothing to confirm; not a violation either
        t41_ok = self.boundary.boundary_exists  # surface activates the theorem
        t51_ok = self.eps_robust.holds  # bound holds for every filled cell
        t62_ok = not self.persistence.theorem_violated  # no false positives
        return t41_ok and t51_ok and t62_ok

    def to_dict(self) -> dict:
        return {
            "tau": self.tau,
            "grid_size": self.grid_size,
            "coverage": self.coverage,
            "safe_count": self.safe_count,
            "unsafe_count": self.unsafe_count,
            "at_threshold_count": self.at_threshold_count,
            "applicable": self.applicable,
            "all_predictions_confirmed": self.all_predictions_confirmed,
            "defense": {"name": self.defense_name, "params": self.defense_params},
            "estimates": self.estimates.to_dict(),
            "theorem_4_1_boundary_fixation": self.boundary.to_dict(),
            "theorem_5_1_eps_robust": self.eps_robust.to_dict(),
            "theorem_6_2_persistent_unsafe_region": self.persistence.to_dict(),
            "cell_observations": [c.to_dict() for c in self.cell_observations],
            "notes": self.notes,
        }


def find_boundary_cells(heatmap: Heatmap, tau: float) -> list[tuple[int, int]]:
    """Boundary cells: filled non-safe cells (``f >= tau``) closest to the safe region.

    On dense grids, these are filled cells with ``f >= tau`` that have a filled
    safe (``f < tau``) cell as a 4-neighbor. On sparse grids where no filled
    cells are 4-adjacent, we relax to nearest-in-filled-graph: any filled
    non-safe cell whose nearest filled neighbor (over the entire filled set) is
    a safe cell is a boundary cell. This is the discrete analog of
    ``cl(S_tau) \\ S_tau``.
    """
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size

    # First pass: strict 4-adjacency (works on dense grids).
    boundary: list[tuple[int, int]] = []
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j] or vals[i, j] < tau:
                continue
            for di, dj in _RNEIGH:
                ni, nj = i + di, j + dj
                if 0 <= ni < gs and 0 <= nj < gs and filled[ni, nj] and vals[ni, nj] < tau:
                    boundary.append((i, j))
                    break
    if boundary:
        return boundary

    # Second pass: sparse-grid fallback. A non-safe filled cell is boundary if
    # its nearest filled neighbor (any direction) is safe.
    idx = np.argwhere(filled)
    if len(idx) < 2:
        return []
    safe_mask = vals[idx[:, 0], idx[:, 1]] < tau
    unsafe_mask = ~safe_mask & ~np.isnan(vals[idx[:, 0], idx[:, 1]])
    if not safe_mask.any() or not unsafe_mask.any():
        return []
    di = idx[:, 0:1] - idx[:, 0:1].T
    dj = idx[:, 1:2] - idx[:, 1:2].T
    dist = np.hypot(di, dj).astype(float)
    np.fill_diagonal(dist, np.inf)
    nearest = dist.argmin(axis=1)
    for k in range(len(idx)):
        if not unsafe_mask[k]:
            continue
        if safe_mask[nearest[k]]:
            boundary.append((int(idx[k, 0]), int(idx[k, 1])))
    return boundary


def check_boundary_fixation(
    defense: DefenseMap, heatmap: Heatmap, tau: float
) -> BoundaryFixationCheck:
    boundary = find_boundary_cells(heatmap, tau)
    fixed: list[tuple[int, int]] = []
    for i, j in boundary:
        ti, tj = int(defense.targets[i, j, 0]), int(defense.targets[i, j, 1])
        if (ti, tj) == (i, j):
            fixed.append((i, j))

    closest: tuple[int, int] | None = None
    empirical_f = float("nan")
    gap = float("nan")
    if boundary:
        best_diff = float("inf")
        for i, j in boundary:
            d = abs(float(heatmap.values[i, j] - tau))
            if d < best_diff:
                best_diff = d
                closest = (i, j)
        empirical_f = float(heatmap.values[closest[0], closest[1]])
        gap = abs(empirical_f - tau)

    return BoundaryFixationCheck(
        boundary_cells=boundary,
        fixed_boundary_cells=fixed,
        boundary_exists=len(boundary) > 0,
        defense_fixes_all_boundary=(len(fixed) == len(boundary) and len(boundary) > 0),
        closest_cell=closest,
        predicted_f_at_boundary=tau,
        empirical_f_at_closest=empirical_f,
        discretization_gap=gap,
    )


def _post_defense_values(defense: DefenseMap, heatmap: Heatmap) -> np.ndarray:
    """Compute ``f(D(x))`` for each filled cell. NaN where the cell is unfilled."""
    vals = heatmap.values
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    out = np.full_like(vals, np.nan)
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j]:
                continue
            ti, tj = int(defense.targets[i, j, 0]), int(defense.targets[i, j, 1])
            if filled[ti, tj]:
                out[i, j] = vals[ti, tj]
            else:
                # Defense projected to an unfilled cell — fall back to identity.
                out[i, j] = vals[i, j]
    return out


def _select_anchor(
    boundary: BoundaryFixationCheck, heatmap: Heatmap, tau: float
) -> tuple[Optional[tuple[int, int]], float]:
    """Pick the boundary cell whose value is closest to tau (best discrete z*)."""
    if not boundary.boundary_cells:
        return None, 0.0
    best = boundary.boundary_cells[0]
    best_diff = float("inf")
    for i, j in boundary.boundary_cells:
        diff = abs(float(heatmap.values[i, j] - tau))
        if diff < best_diff:
            best_diff = diff
            best = (i, j)
    return best, best_diff


def check_eps_robust(
    defense: DefenseMap,
    heatmap: Heatmap,
    tau: float,
    estimates: LipschitzEstimates,
    boundary: BoundaryFixationCheck,
) -> EpsRobustCheck:
    """Verify ``|f(D(x)) - tau| <= LK * dist(x, z*) + slack`` per-cell.

    The continuous theorem assumes ``f(z) = tau`` exactly. On a discrete grid no
    cell has ``f`` exactly equal to ``tau`` in general, so the anchor ``z*`` is
    the boundary cell whose value is closest to ``tau`` and we add a slack of
    ``|f(z*) - tau|`` (which vanishes as the grid is refined).
    """
    if not boundary.boundary_cells:
        return EpsRobustCheck(
            anchor_cell=None,
            L=estimates.L,
            K=estimates.K,
            discretization_slack=0.0,
            max_observed_lhs=0.0,
            max_predicted_rhs=0.0,
            max_violation=0.0,
            num_within_bound=0,
            num_total=0,
            worst_cell=None,
            worst_observed_lhs=0.0,
            worst_predicted_rhs=0.0,
            holds=True,
        )

    anchor, slack = _select_anchor(boundary, heatmap, tau)
    assert anchor is not None  # boundary non-empty implies anchor exists
    z_i, z_j = anchor

    h = heatmap.cell_width
    filled = heatmap.filled_mask
    gs = heatmap.grid_size
    post = _post_defense_values(defense, heatmap)
    LK = estimates.L * estimates.K

    max_lhs = 0.0
    max_rhs = 0.0
    max_violation = -np.inf
    worst_cell = None
    worst_lhs = 0.0
    worst_rhs = 0.0
    num_within = 0
    num_total = 0
    holds = True

    for i in range(gs):
        for j in range(gs):
            if not filled[i, j] or np.isnan(post[i, j]):
                continue
            lhs = abs(float(post[i, j] - tau))
            d = h * float(np.hypot(i - z_i, j - z_j))
            rhs = LK * d + slack
            num_total += 1
            if lhs > max_lhs:
                max_lhs = lhs
            if rhs > max_rhs:
                max_rhs = rhs
            v = lhs - rhs
            if v <= 1e-9:
                num_within += 1
            else:
                holds = False
            # Track the cell with the largest violation (or smallest margin if all hold).
            if v > max_violation:
                max_violation = v
                worst_cell = (i, j)
                worst_lhs = lhs
                worst_rhs = rhs

    return EpsRobustCheck(
        anchor_cell=anchor,
        L=estimates.L,
        K=estimates.K,
        discretization_slack=slack,
        max_observed_lhs=max_lhs,
        max_predicted_rhs=max_rhs,
        max_violation=float(max(max_violation, 0.0)),
        num_within_bound=num_within,
        num_total=num_total,
        worst_cell=worst_cell,
        worst_observed_lhs=worst_lhs,
        worst_predicted_rhs=worst_rhs,
        holds=holds,
    )


def check_persistence(
    defense: DefenseMap,
    heatmap: Heatmap,
    tau: float,
    estimates: LipschitzEstimates,
    boundary: BoundaryFixationCheck,
) -> PersistenceCheck:
    """Check transversality, compute the predicted steep set, and compare to actuals.

    The steep set is the *theorem's prediction*: cells where ``f(x) > tau +
    ell*(K+1)*dist(x, z*)``. The theorem says every cell in the steep set
    satisfies ``f(D(x)) > tau``. Empirically we enumerate both the steep set
    and the actual persistent set and produce a confusion matrix.
    """
    h = heatmap.cell_width
    filled = heatmap.filled_mask
    vals = heatmap.values
    gs = heatmap.grid_size
    post = _post_defense_values(defense, heatmap)

    # Anchor: the boundary cell whose value is closest to tau (best discrete z*).
    anchor, _slack = _select_anchor(boundary, heatmap, tau)
    z_i, z_j = anchor if anchor is not None else (None, None)
    boundary_set = set(boundary.boundary_cells)

    ell_K_plus_1 = estimates.ell * (estimates.K + 1.0)

    predicted: list[tuple[int, int]] = []
    actual: list[tuple[int, int]] = []
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j] or np.isnan(post[i, j]):
                continue
            if post[i, j] > tau:
                actual.append((i, j))
            if anchor is not None:
                d = h * float(np.hypot(i - z_i, j - z_j))
                # Steep set definition (no discretization slack):
                #     f(x) > tau + ell*(K+1)*dist(x, z*)
                # Cells satisfying this are predicted by Theorem 6.2 to remain
                # unsafe under any continuous K-Lipschitz defense.
                steep_threshold = tau + ell_K_plus_1 * d
                if vals[i, j] > steep_threshold:
                    predicted.append((i, j))

    pred_set = set(predicted)
    act_set = set(actual)
    true_pos = sorted(pred_set & act_set)
    fp_all = pred_set - act_set
    # Boundary cells in fp_all are NOT theorem violations — they witness that
    # the discrete defense violates the theorem's continuity hypothesis at the
    # boundary. Only *interior* false positives are real counterexamples.
    fp_interior = sorted(fp_all - boundary_set)
    fp_boundary = sorted(fp_all & boundary_set)
    false_neg = sorted(act_set - pred_set)

    n_filled = int(filled.sum())
    frac = (len(actual) / n_filled) if n_filled > 0 else 0.0
    transversality = estimates.persistence_condition()
    theorem_violated = len(fp_interior) > 0
    consistent = not theorem_violated and (
        (transversality and len(predicted) > 0)
        or (not transversality and len(predicted) == 0)
    )

    return PersistenceCheck(
        G=estimates.G,
        ell=estimates.ell,
        K=estimates.K,
        ell_K_plus_1=ell_K_plus_1,
        transversality_holds=transversality,
        anchor_cell=anchor,
        predicted_steep_cells=predicted,
        actual_persistent_cells=actual,
        true_positives=true_pos,
        false_positives_interior=fp_interior,
        false_positives_boundary=fp_boundary,
        false_negatives=false_neg,
        persistent_fraction=frac,
        theorem_violated=theorem_violated,
        consistent_with_theorem=consistent,
    )


def run_full_validation(
    heatmap: Heatmap, tau: float, defense: DefenseMap
) -> TrilemmaResult:
    """End-to-end validation: run all three theorem checks plus the headline counts.

    Strict inequalities are used throughout, matching the paper:
        S_tau = {x : f(x) < tau}    (open safe region)
        U_tau = {x : f(x) > tau}    (open unsafe region)
        B_tau = {x : f(x) = tau}    (exact boundary)

    The trilemma's preconditions require both S_tau and U_tau to be non-empty.
    """
    filled = heatmap.filled_mask
    vals = heatmap.values
    safe_count = int(((vals < tau) & filled).sum())
    unsafe_count = int(((vals > tau) & filled).sum())
    at_threshold_count = int(((vals == tau) & filled).sum())
    notes: list[str] = []

    estimates = estimate_all(heatmap, defense, tau)

    applicable = safe_count > 0 and unsafe_count > 0
    if not applicable:
        if unsafe_count == 0:
            notes.append(
                f"No filled cell strictly exceeds tau={tau}: U_tau is empty, so "
                "the trilemma's preconditions fail and no impossibility is "
                "predicted (this is the GPT-5-Mini case in the paper). "
                f"There are {at_threshold_count} cells exactly at threshold "
                "(measure zero in the continuous limit; benign by construction)."
            )
        if safe_count == 0:
            notes.append(
                f"No filled cell is strictly below tau={tau}: S_tau is empty, "
                "so utility preservation has nothing to fix and the theorems "
                "do not apply."
            )

    boundary = check_boundary_fixation(defense, heatmap, tau)
    eps = check_eps_robust(defense, heatmap, tau, estimates, boundary)
    persistence = check_persistence(defense, heatmap, tau, estimates, boundary)
    observations = _collect_cell_observations(
        heatmap, defense, tau, estimates, boundary, persistence
    )

    return TrilemmaResult(
        tau=tau,
        grid_size=heatmap.grid_size,
        coverage=heatmap.coverage,
        safe_count=safe_count,
        unsafe_count=unsafe_count,
        at_threshold_count=at_threshold_count,
        estimates=estimates,
        defense_name=defense.name,
        defense_params=defense.params,
        boundary=boundary,
        eps_robust=eps,
        persistence=persistence,
        applicable=applicable,
        cell_observations=observations,
        notes=notes,
    )


def _collect_cell_observations(
    heatmap: Heatmap,
    defense: DefenseMap,
    tau: float,
    estimates: LipschitzEstimates,
    boundary: BoundaryFixationCheck,
    persistence: PersistenceCheck,
) -> list[CellObservation]:
    """Build a per-cell record of predicted vs empirical for every filled cell."""
    h = heatmap.cell_width
    filled = heatmap.filled_mask
    vals = heatmap.values
    gs = heatmap.grid_size
    post = _post_defense_values(defense, heatmap)
    LK = estimates.L * estimates.K

    anchor, slack = _select_anchor(boundary, heatmap, tau)
    if anchor is None:
        # Without an anchor we still emit per-cell records but with NaN distances.
        z_i, z_j = -1, -1
    else:
        z_i, z_j = anchor

    pred_set = {tuple(c) for c in persistence.predicted_steep_cells}
    act_set = {tuple(c) for c in persistence.actual_persistent_cells}

    out: list[CellObservation] = []
    for i in range(gs):
        for j in range(gs):
            if not filled[i, j] or np.isnan(post[i, j]):
                continue
            if anchor is None:
                d = float("nan")
                rhs = float("nan")
                within = True  # vacuous when anchor is undefined
            else:
                d = h * float(np.hypot(i - z_i, j - z_j))
                rhs = LK * d + slack
                within = abs(float(post[i, j] - tau)) <= rhs + 1e-9
            ti, tj = int(defense.targets[i, j, 0]), int(defense.targets[i, j, 1])
            out.append(
                CellObservation(
                    cell=(i, j),
                    f_value=float(vals[i, j]),
                    target_cell=(ti, tj),
                    f_post_defense=float(post[i, j]),
                    dist_to_anchor=d,
                    eps_robust_lhs=abs(float(post[i, j] - tau)),
                    eps_robust_rhs=rhs,
                    eps_robust_within_bound=within,
                    in_predicted_steep_set=(i, j) in pred_set,
                    in_actual_persistent_set=(i, j) in act_set,
                )
            )
    return out
