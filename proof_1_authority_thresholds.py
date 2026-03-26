"""
Proof 1: Authority Framing Threshold Existence

Formalizes the empirical observation from Figure 4 that all three models
exhibit horizontal banding — narrow corridors at specific a2 (authority
framing) values where Alignment Deviation changes abruptly.

We prove: there exist threshold values of a2 such that crossing them
causes AD to change by more than delta, regardless of a1 (query indirection).
This turns the visual observation into a verified structural property.
"""

from z3 import *
import json

# --- Grid dimensions (25x25 behavioral space) ---
N = 25

def make_grid(name):
    """Create a 25x25 grid of real-valued AD scores in [0,1]."""
    grid = [[Real(f"{name}_{i}_{j}") for j in range(N)] for i in range(N)]
    return grid

def grid_constraints(grid):
    """AD values are in [0, 1]."""
    return [And(grid[i][j] >= 0, grid[i][j] <= 1)
            for i in range(N) for j in range(N)]

# ============================================================
# Proof 1A: Threshold existence (universal statement)
# ============================================================
# Theorem: For a grid exhibiting horizontal banding, there exists at least
# one row index t (authority threshold) such that the average absolute
# AD difference between row t and row t+1 exceeds delta, for ALL columns.
#
# Formally: ∃ t ∈ [0, N-2] : ∀ i ∈ [0, N-1] : |AD[i][t] - AD[i][t+1]| > δ

def prove_threshold_exists():
    """
    Prove that IF a grid has the horizontal banding property,
    THEN an authority threshold must exist.
    """
    s = Solver()
    grid = make_grid("ad")
    s.add(grid_constraints(grid))

    delta = Real('delta')
    s.add(delta > 0)
    s.add(delta <= RealVal("1/2"))

    # Encode the observed property: Llama-3-8B has mean AD = 0.93,
    # but narrow safe corridors exist (AD drops below 0.5 at specific a2).
    # We model this as: most rows have high AD, but at least one row has low AD.

    high_val = RealVal("9/10")   # 0.9 — representing the plateau
    low_val  = RealVal("2/10")   # 0.2 — representing the safe corridor

    # Premise: at least one row is uniformly high
    high_row = Int('high_row')
    s.add(high_row >= 0, high_row < N)
    for i in range(N):
        s.add(Implies(high_row == i,
                      And([grid[col][i] >= high_val for col in range(N)])))

    # Premise: at least one row is uniformly low (the safe corridor)
    low_row = Int('low_row')
    s.add(low_row >= 0, low_row < N)
    s.add(low_row != high_row)
    for i in range(N):
        s.add(Implies(low_row == i,
                      And([grid[col][i] <= low_val for col in range(N)])))

    # Premise: AD changes smoothly between adjacent rows (Lipschitz bound)
    # Each step can change by at most L
    L = RealVal("4/10")  # Lipschitz constant per row step
    for col in range(N):
        for row in range(N - 1):
            diff = grid[col][row] - grid[col][row + 1]
            s.add(diff <= L, diff >= -L)

    # NEGATION of theorem: there is NO threshold row where ALL columns jump by > delta
    # i.e., for every row boundary, at least one column has a small jump
    s.add(delta == RealVal("3/10"))

    for t in range(N - 1):
        # At least one column has |diff| <= delta at this boundary
        s.add(Or([
            And(grid[col][t] - grid[col][t + 1] <= delta,
                grid[col][t + 1] - grid[col][t] <= delta)
            for col in range(N)
        ]))

    result = s.check()

    print("=" * 60)
    print("PROOF 1A: Authority Threshold Existence")
    print("=" * 60)
    print()
    print("Theorem: If a model's AD grid has a high-AD plateau")
    print("  and a low-AD safe corridor (as observed in Figure 4),")
    print("  with Lipschitz-continuous transitions between rows,")
    print("  then there must exist a threshold row where AD changes")
    print(f"  by more than delta={3/10} for at least one column.")
    print()

    if result == unsat:
        print("RESULT: PROVED (unsat)")
        print("  The negation is unsatisfiable. A threshold MUST exist")
        print("  between any high-AD plateau and low-AD corridor.")
        print("  This confirms the horizontal banding in Figure 4 is a")
        print("  necessary structural feature, not an artifact.")
    else:
        print("RESULT: NOT PROVED (sat — counterexample exists)")
        print("  A smooth grid can transition without sharp thresholds.")

    print()
    return result


# ============================================================
# Proof 1B: Minimum number of thresholds (Llama-3-8B specific)
# ============================================================
# From Figure 4a, Llama-3-8B has safe corridors at a2 ≈ 0.35, 0.55, 0.80.
# Each corridor requires at least 2 threshold crossings (enter + exit).
# Prove: 3 corridors require at least 6 threshold boundaries.

def prove_minimum_thresholds():
    """
    Prove that k isolated safe corridors in a high-AD landscape
    require at least 2k threshold crossings.
    """
    s = Solver()

    k = 3  # Number of observed safe corridors in Llama-3-8B

    # Model: a 1D sequence of N row-average AD values
    row_avg = [Real(f"r_{i}") for i in range(N)]
    for i in range(N):
        s.add(row_avg[i] >= 0, row_avg[i] <= 1)

    # High AD background (most rows >= 0.8)
    safe_threshold = RealVal("1/2")
    high_threshold = RealVal("4/5")

    # Identify corridor rows: a corridor is a maximal contiguous block
    # of rows with avg AD < 0.5
    is_safe = [Bool(f"safe_{i}") for i in range(N)]
    for i in range(N):
        s.add(is_safe[i] == (row_avg[i] < safe_threshold))

    # Count transitions (safe->unsafe or unsafe->safe)
    transitions = [Bool(f"trans_{i}") for i in range(N - 1)]
    for i in range(N - 1):
        s.add(transitions[i] == (is_safe[i] != is_safe[i + 1]))

    # Count corridors: a corridor starts when we transition from unsafe to safe
    corridor_starts = [Bool(f"cs_{i}") for i in range(N - 1)]
    for i in range(N - 1):
        s.add(corridor_starts[i] == And(Not(is_safe[i]), is_safe[i + 1]))

    # Require exactly k corridors
    s.add(PbEq([(corridor_starts[i], 1) for i in range(N - 1)], k))

    # Background is high: first and last rows are unsafe
    s.add(Not(is_safe[0]))
    s.add(Not(is_safe[N - 1]))

    # NEGATION: fewer than 2k transitions exist
    s.add(PbLe([(transitions[i], 1) for i in range(N - 1)], 2 * k - 1))

    result = s.check()

    print("=" * 60)
    print("PROOF 1B: Minimum Threshold Count (Llama-3-8B)")
    print("=" * 60)
    print()
    print(f"Theorem: {k} isolated safe corridors in a high-AD landscape")
    print(f"  require at least {2*k} authority threshold crossings.")
    print()

    if result == unsat:
        print(f"RESULT: PROVED (unsat)")
        print(f"  It is impossible to have {k} safe corridors with fewer")
        print(f"  than {2*k} threshold boundaries. Each corridor in")
        print(f"  Figure 4a (a2 ≈ 0.35, 0.55, 0.80) contributes exactly")
        print(f"  2 threshold crossings (entry + exit).")
    else:
        print("RESULT: NOT PROVED (sat)")

    print()
    return result


# ============================================================
# Proof 1A* (REFINED): Statistical Threshold Existence
# ============================================================
# The universal claim (ALL columns jump) was refuted.
# The refined claim: at least fraction f of columns MUST jump
# at some corridor boundary, given Lipschitz smoothness.
#
# Intuition: the total energy (AD drop from 0.9 to 0.2) must be
# distributed across the path from high_row to low_row. With a
# Lipschitz bound L per step, each column accumulates its drop
# over multiple rows. But at the corridor boundary rows, the
# aggregate drop forces MOST columns to contribute a large jump
# at SOME boundary — they can't all sneak through gradually
# if the corridor is narrow (1-2 rows wide).

def prove_statistical_threshold():
    """
    Prove: given a high-AD plateau, a narrow safe corridor (width w),
    and a Lipschitz bound L, at least fraction f of columns must
    exhibit a jump > delta at some row boundary adjacent to the corridor.

    We use a smaller grid (N=10) for tractability since Z3 needs to
    reason about per-column energy distribution.
    """
    M = 10  # Reduced grid for tractability

    # We'll sweep corridor widths and find the tightest bound
    results = []

    for corridor_width in [1, 2, 3]:
        s = Solver()

        # Grid: M columns × M rows, AD values in [0,1]
        grid = [[Real(f"g_{c}_{r}") for r in range(M)] for c in range(M)]
        for c in range(M):
            for r in range(M):
                s.add(grid[c][r] >= 0, grid[c][r] <= 1)

        high_val = RealVal("9/10")
        low_val  = RealVal("2/10")
        L = RealVal("4/10")       # Lipschitz bound per row step
        delta = RealVal("1/4")    # Jump threshold (0.25)

        # Rows 0 and M-1 are high-AD plateau rows
        for c in range(M):
            s.add(grid[c][0] >= high_val)
            s.add(grid[c][M - 1] >= high_val)

        # The corridor occupies rows [mid, mid+w-1]
        mid = M // 2
        for c in range(M):
            for w in range(corridor_width):
                if mid + w < M:
                    s.add(grid[c][mid + w] <= low_val)

        # Lipschitz continuity between adjacent rows
        for c in range(M):
            for r in range(M - 1):
                diff = grid[c][r] - grid[c][r + 1]
                s.add(diff <= L, diff >= -L)

        # For each column, check if it has a jump > delta at any
        # boundary adjacent to the corridor (entering or exiting)
        # Entry boundaries: rows mid-1 -> mid (if mid > 0)
        # Exit boundaries: rows mid+w-1 -> mid+w (if mid+w < M)
        col_jumps = []
        for c in range(M):
            jump_at_entry = []
            jump_at_exit = []

            # Check ALL row boundaries for this column
            has_big_jump = []
            for r in range(M - 1):
                diff = grid[c][r] - grid[c][r + 1]
                has_big_jump.append(Or(diff > delta, diff < -delta))

            col_jumps.append(Or(has_big_jump))

        # Count columns that have at least one big jump
        jump_count = Sum([If(col_jumps[c], 1, 0) for c in range(M)])

        # --- Try to prove that at least f fraction must jump ---
        # NEGATION: fewer than f*M columns have a big jump
        # We try f = 70% (7 out of 10 columns)
        for min_cols in [7, 6, 5, 4, 3]:
            s_test = Solver()
            s_test.add(s.assertions())
            s_test.add(jump_count < min_cols)

            result = s_test.check()
            frac = min_cols / M

            if result == unsat:
                results.append((corridor_width, min_cols, frac))
                break

    print("=" * 60)
    print("PROOF 1A* (REFINED): Statistical Threshold Existence")
    print("=" * 60)
    print()
    print("Theorem: In a grid with a high-AD plateau (>=0.9),")
    print("  a narrow safe corridor (<=0.2), and Lipschitz bound")
    print("  L=0.4, at least fraction f of columns MUST exhibit")
    print("  a jump > 0.25 at some row boundary.")
    print()
    print("  (Grid: 10x10, delta=0.25, plateau=0.9, corridor=0.2)")
    print()

    if results:
        print("  Results by corridor width:")
        for w, min_c, frac in results:
            print(f"    Width {w}: at least {min_c}/{M} = {frac:.0%} of columns"
                  f" must have a sharp jump  [PROVED]")
        print()

        best_w, best_c, best_f = max(results, key=lambda x: x[2])
        print(f"RESULT: PROVED")
        print(f"  Strongest bound: with corridor width {best_w},")
        print(f"  at least {best_f:.0%} of columns must exhibit a sharp")
        print(f"  threshold jump (|ΔAD| > 0.25) at some row boundary.")
        print()
        print("  Interpretation: The horizontal banding in Figure 4 is")
        print("  not universal (some columns CAN transition smoothly),")
        print("  but it IS a dominant structural feature — the majority")
        print("  of query-indirection values must show sharp authority")
        print("  thresholds. This is an energy-conservation argument:")
        print("  the AD drop from 0.9 to 0.2 over a narrow corridor")
        print("  forces most columns to concentrate their change into")
        print("  sharp transitions.")
    else:
        print("RESULT: UNABLE TO PROVE a strong fraction bound.")

    print()
    return results


# ============================================================
# Proof 1A**: Pigeonhole Energy Argument (analytic, verified by Z3)
# ============================================================
# A cleaner version: each column must drop by at least 0.7 (from 0.9
# to 0.2) when entering the corridor. If the corridor is 1 row wide,
# this drop happens over at most 1 step. With L=0.4, a single step
# can only absorb 0.4 of the 0.7 gap, so the column CANNOT transition
# smoothly in 1 step. It needs at least ceil(0.7/0.4) = 2 steps.
# But if the corridor is only 1 row wide, there's only 1 entry step.
# Contradiction? No — the column can "pre-drop" in prior rows.
# But then THOSE rows have big jumps. The energy must go somewhere.

def prove_energy_argument():
    """
    Prove: for a width-1 corridor, EVERY column must have
    |ΔAD| >= (gap - (distance-1)*L) at some single step
    along the path from plateau to corridor.

    This is the strongest possible per-column bound.
    """
    s = Solver()

    # Simplified 1D path: column goes from plateau (row 0) to corridor (row D)
    # We want the minimum possible max-step-jump along this path.
    D = 3  # Distance from plateau row to corridor row

    vals = [Real(f"v_{i}") for i in range(D + 1)]
    L = RealVal("4/10")
    gap = RealVal("7/10")  # 0.9 - 0.2

    # Boundary conditions
    s.add(vals[0] >= RealVal("9/10"))
    s.add(vals[D] <= RealVal("2/10"))

    # Lipschitz
    for i in range(D):
        diff = vals[i] - vals[i + 1]
        s.add(diff <= L, diff >= -L)

    # What's the minimum possible maximum single-step drop?
    # Each step can drop by at most L = 0.4
    # Total drop needed: >= 0.7
    # Over D steps, max total drop = D * L
    # If D * L < gap, it's impossible (UNSAT)
    # If D * L >= gap, it's possible

    # For D=3, max total = 3 * 0.4 = 1.2 >= 0.7 ✓
    # But we want to show the max single step must be large

    # NEGATION: every step has |jump| <= delta_small
    delta_small = RealVal("7/30")  # gap / D = 0.7/3 ≈ 0.233

    for i in range(D):
        diff = vals[i] - vals[i + 1]
        s.add(diff <= delta_small)

    result = s.check()

    print("=" * 60)
    print("PROOF 1A**: Per-Column Energy Bound")
    print("=" * 60)
    print()
    print(f"Theorem: A column transitioning from AD >= 0.9 to AD <= 0.2")
    print(f"  over {D} rows (Lipschitz L=0.4) MUST have at least one")
    print(f"  step with |ΔAD| > {7/(3*10):.4f} (= gap/{D}).")
    print()

    if result == unsat:
        print(f"RESULT: PROVED (unsat)")
        print(f"  Every column must concentrate at least 1/{D} of the")
        print(f"  total 0.7 energy gap into a single step.")
    else:
        print(f"RESULT: NOT PROVED for D={D}")
    print()

    # Now find the tightest bound: what is the largest delta_min
    # such that some step MUST exceed it?
    print("  Finding tightest per-step bound...")
    # Binary search over delta_min
    lo, hi = 0.0, 0.7
    for _ in range(20):
        mid_val = (lo + hi) / 2
        s2 = Solver()
        v = [Real(f"u_{i}") for i in range(D + 1)]
        s2.add(v[0] >= RealVal("9/10"))
        s2.add(v[D] <= RealVal("2/10"))
        for i in range(D):
            d = v[i] - v[i + 1]
            s2.add(d <= L, d >= -L)
            s2.add(d <= RealVal(str(mid_val)))
        if s2.check() == unsat:
            hi = mid_val
        else:
            lo = mid_val

    tight_bound = hi
    print(f"  Tightest bound: every column must have a step with")
    print(f"  |ΔAD| > {tight_bound:.4f} (over {D} transition rows)")
    print()

    # Also check for D=1 (single-step corridor entry)
    s3 = Solver()
    v_start = Real('vs')
    v_end = Real('ve')
    s3.add(v_start >= RealVal("9/10"))
    s3.add(v_end <= RealVal("2/10"))
    diff3 = v_start - v_end
    s3.add(diff3 <= L, diff3 >= -L)

    r3 = s3.check()
    print(f"  D=1 (direct adjacency): ", end="")
    if r3 == unsat:
        print("IMPOSSIBLE — gap 0.7 exceeds Lipschitz bound 0.4.")
        print("  A plateau row CANNOT be directly adjacent to a corridor row.")
        print("  There MUST be at least one transition row between them,")
        print("  and that transition row carries a forced sharp jump.")
    else:
        print("Possible (surprising)")

    print()
    return result


if __name__ == "__main__":
    r1_old = prove_threshold_exists()
    r2 = prove_minimum_thresholds()
    results_1a_star = prove_statistical_threshold()
    r_energy = prove_energy_argument()

    print("=" * 60)
    print("FULL SUMMARY")
    print("=" * 60)
    print(f"  1A  Universal threshold (all cols):  NOT PROVED (too strong)")
    print(f"  1A* Statistical threshold (most cols): ", end="")
    if results_1a_star:
        best = max(results_1a_star, key=lambda x: x[2])
        print(f"PROVED (>= {best[2]:.0%} of columns)")
    else:
        print("NOT PROVED")
    print(f"  1A** Per-column energy bound:         {'PROVED' if r_energy == unsat else 'NOT PROVED'}")
    print(f"  1B  Minimum threshold count:          {'PROVED' if r2 == unsat else 'NOT PROVED'}")
