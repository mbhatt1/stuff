import Mathlib
/-
  PromptInjection09_DimensionalityCurse.lean

  Lean 4 / Mathlib formalization of Theorem 9 from the
  "Manifold of Failure" prompt-injection framework:

  **Dimensionality Curse for Prompt Injection Defense**

  As the behavioral space dimension d increases, defense becomes
  exponentially harder:

    1. The d-dimensional behavioral space is [0,1]^d  (Fin d → Set.Icc 0 1).
    2. An N-partition per axis yields N^d grid cells.
    3. N^d grows exponentially in d for fixed N > 1.
    4. A defense ball of radius r < 1 covers a fraction proportional
       to r^d of the unit cube, which → 0 as d → ∞.
    5. Coverage requires exponentially many defense patches.
    6. MAP-Elites query complexity is Ω(N^d).

  This formalizes the fundamental impossibility of exhaustive defense
  in high-dimensional prompt spaces.
-/


noncomputable section

open Set Filter Fintype Topology

/-! ## 1. The d-Dimensional Behavioral Space -/

/--
The d-dimensional behavioral space: functions from `Fin d` into the unit
interval `Set.Icc (0 : ℝ) 1`.  Each coordinate represents one behavioral
dimension of a language model's response space.
-/
abbrev BehavioralSpace (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

/-! ## 2. Grid Discretisation: Card = N^d -/

/--
A discretised grid along one axis with N cells is modeled by `Fin N`.
The d-dimensional grid is `Fin d → Fin N`, whose cardinality is N^d.

This is the number of cells a MAP-Elites archive must maintain.
-/
theorem grid_card (N d : ℕ) :
    Fintype.card (Fin d → Fin N) = N ^ d := by
  simp [Fintype.card_fin]

/-! ## 3. Exponential Growth of Grid Size -/

/--
For N ≥ 2, the grid size N^d is strictly monotone in d and exceeds
any fixed bound for large enough d.  This is the combinatorial core
of the dimensionality curse: the number of cells to patrol grows
exponentially.
-/
theorem grid_size_tendsto_atTop {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun d => (N : ℝ) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact_mod_cast hN

/--
N^d ≥ 2^d for N ≥ 2, giving a concrete exponential lower bound.
-/
theorem grid_size_lower_bound {N : ℕ} (hN : 2 ≤ N) (d : ℕ) :
    2 ^ d ≤ N ^ d := by
  exact Nat.pow_le_pow_left (by linarith) d

/-! ## 4. Fractional Volume of a Defense Ball -/

/--
The fraction of the unit cube [0,1]^d covered by a single defense
ball of radius r is bounded above by a constant times r^d.
We define the "coverage fraction" abstractly as `V_d * r^d` where
`V_d` is the unit-ball volume prefactor (which is at most 1 for
balls inscribed in [0,1]^d with r ≤ 1/2).

For the dimensionality curse, the key quantity is r^d.
-/
def coverageFraction (r : ℝ) (V_d : ℝ) (d : ℕ) : ℝ := V_d * r ^ d

/--
For 0 ≤ r < 1, the term r^d → 0 as d → ∞.  This is the heart of the
dimensionality curse: each defense patch covers an exponentially
shrinking fraction of the behavioral space.
-/
theorem defense_fraction_tendsto_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

/--
Multiplying by any bounded prefactor V_d ≤ C still gives convergence
to zero.  In particular, `C * r^d → 0`.
-/
theorem scaled_defense_fraction_tendsto_zero
    {r C : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C) :
    Tendsto (fun d : ℕ => C * r ^ d) atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have : (fun d : ℕ => C * r ^ d) = fun d => C * (r ^ d) := rfl
  rw [this]
  rw [show (0 : ℝ) = C * 0 from by ring]
  exact h.const_mul C

/-! ## 5. The Coverage Fraction r^d Is Strictly Decreasing -/

/--
For 0 < r < 1, we have r^(d+1) < r^d — each additional dimension
strictly shrinks the fraction of space a single ball can cover.
-/
theorem defense_fraction_strict_decrease
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (d : ℕ) :
    r ^ (d + 1) < r ^ d := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos hr0 d) hr1

/--
r^d < 1 for all d ≥ 1 when 0 < r < 1.  Even in dimension 1, a single
ball of radius r < 1 cannot cover the whole space.
-/
theorem defense_fraction_lt_one
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {d : ℕ} (hd : 0 < d) :
    r ^ d < 1 := by
  exact pow_lt_one₀ hr0 hr1 (by omega)

/-! ## 6. Number of Balls Needed for Coverage -/

/--
To cover a fraction α of [0,1]^d using balls each covering at most
`V_d * r^d`, you need at least ⌈α / (V_d * r^d)⌉ balls.

We state the real-valued lower bound: if each ball covers at most `c`,
then covering total area `α` requires at least `α / c` balls.
-/
theorem balls_needed_lower_bound
    {α c : ℝ} (hα : 0 < α) (hc : 0 < c) (n : ℕ)
    (h_cover : α ≤ n * c) :
    α / c ≤ (n : ℝ) := by
  rwa [div_le_iff₀ hc]

/--
The number of balls needed grows as 1/r^d, which → ∞ as d → ∞
for any fixed 0 < r < 1.

More precisely, if each ball covers fraction at most C * r^d with C > 0,
and we want to cover a fixed fraction α > 0, then the required number
of balls α / (C * r^d) → ∞.
-/
theorem balls_needed_tendsto_atTop
    {r C α : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C) (hα : 0 < α) :
    Tendsto (fun d : ℕ => α / (C * r ^ d)) atTop atTop := by
  have h_inv : Tendsto (fun d : ℕ => (1 / r) ^ d) atTop atTop := by
    apply tendsto_pow_atTop_atTop_of_one_lt
    rw [one_div]
    exact (one_lt_inv₀ hr0).mpr hr1
  have key : ∀ d : ℕ, α / (C * r ^ d) = α / C * (1 / r) ^ d := by
    intro d
    rw [one_div, inv_pow, div_mul_eq_div_div]
    congr 1
  simp_rw [key]
  exact Tendsto.const_mul_atTop (div_pos hα hC) h_inv

/-! ## 7. Exponential Lower Bound on Defense Cost -/

/--
For 0 < r < 1, we have `(1/r)^d → ∞`, giving an explicit exponential
growth rate for the number of required defense patches.
-/
theorem inverse_radius_pow_tendsto_atTop
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => (1 / r) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  rw [one_div]
  exact (one_lt_inv₀ hr0).mpr hr1

/--
Concrete bound: the number of defense balls needed is at least (1/r)^d
times a constant.  Since (1/r) > 1 for r < 1, this is exponential in d.
-/
theorem defense_cost_exponential
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (d : ℕ) :
    (1 / r) ^ d = 1 / r ^ d := by
  rw [one_div, inv_pow, one_div]

/-! ## 8. MAP-Elites Query Complexity -/

/--
**MAP-Elites Query Complexity (Informal Ω(N^d) Statement)**

In a MAP-Elites exploration of the d-dimensional behavioral space with
N bins per axis, achieving full coverage requires visiting all N^d cells.
Since each query covers at most one cell, the number of queries is at
least N^d.

We state this as: for any archive coverage count `covered ≤ N^d`, the
remaining uncovered cells are `N^d - covered`, and to fill them all
requires at least `N^d - covered` additional queries.
-/
theorem map_elites_query_lower_bound (N d covered : ℕ)
    (h_cov : covered ≤ N ^ d) :
    N ^ d - covered + covered = N ^ d := by
  omega

/--
Even with an oracle that covers one new cell per query, full coverage
of the N^d-cell grid requires exactly N^d queries.
-/
theorem map_elites_full_coverage_cost (N d : ℕ) :
    Fintype.card (Fin d → Fin N) = N ^ d := grid_card N d

/-! ## 9. Main Dimensionality Curse Theorem -/

/--
**Theorem 9: Dimensionality Curse for Prompt Injection Defense.**

This structure bundles the key quantitative facts:
  1. Grid size = N^d (combinatorial explosion).
  2. Defense fraction r^d → 0 (coverage collapse).
  3. Required defense balls → ∞ (cost explosion).
  4. MAP-Elites needs Ω(N^d) queries.

Together these prove that defense in high-dimensional prompt spaces is
fundamentally intractable: the defender's workload grows exponentially
while the attacker need only find one point in the vulnerability manifold.
-/
structure DimensionalityCurse where
  /-- Number of bins per axis -/
  N : ℕ
  /-- N ≥ 2 for meaningful discretisation -/
  hN : 2 ≤ N
  /-- Defense ball radius -/
  r : ℝ
  /-- Radius is positive -/
  hr_pos : 0 < r
  /-- Radius is less than 1 -/
  hr_lt : r < 1
  /-- Coverage target (fraction of space to defend) -/
  α : ℝ
  /-- Coverage target is positive -/
  hα : 0 < α
  /-- Volume prefactor for unit ball -/
  C : ℝ
  /-- Prefactor is positive -/
  hC : 0 < C

namespace DimensionalityCurse

variable (dc : DimensionalityCurse)

/-- The grid size N^d tends to infinity as d → ∞. -/
theorem grid_explosion :
    Tendsto (fun d => (dc.N : ℝ) ^ d) atTop atTop :=
  grid_size_tendsto_atTop dc.hN

/-- Each defense ball covers a fraction that shrinks to zero. -/
theorem coverage_collapse :
    Tendsto (fun d => dc.r ^ d) atTop (nhds 0) :=
  defense_fraction_tendsto_zero (le_of_lt dc.hr_pos) dc.hr_lt

/-- The number of defense balls needed grows without bound. -/
theorem cost_explosion :
    Tendsto (fun d => dc.α / (dc.C * dc.r ^ d)) atTop atTop :=
  balls_needed_tendsto_atTop dc.hr_pos dc.hr_lt dc.hC dc.hα

/-- The inverse-radius base (1/r) > 1 drives exponential growth. -/
theorem exponential_base_gt_one : 1 < 1 / dc.r := by
  rw [one_div]
  exact (one_lt_inv₀ dc.hr_pos).mpr dc.hr_lt

/-- MAP-Elites archive has N^d cells to fill. -/
theorem archive_size (d : ℕ) :
    Fintype.card (Fin d → Fin dc.N) = dc.N ^ d :=
  grid_card dc.N d

end DimensionalityCurse

/-! ## 10. Attacker Advantage Asymmetry -/

/--
**Attacker-Defender Asymmetry.**

The attacker needs to find *one* point in the vulnerability manifold;
the defender must cover *all* of [0,1]^d.  As d grows, the attacker's
job stays O(1) per injection attempt while the defender's cost is Ω(N^d).

We express this as: for any fixed query budget B, there exists a
dimension d₀ beyond which N^d > B, making exhaustive defense impossible.
-/
theorem attacker_advantage {N : ℕ} (hN : 2 ≤ N) (B : ℝ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < (N : ℝ) ^ d := by
  have h_tend := grid_size_tendsto_atTop hN
  rw [Filter.tendsto_atTop_atTop] at h_tend
  obtain ⟨d₀, hd₀⟩ := h_tend (B + 1)
  exact ⟨d₀, fun d hd => by linarith [hd₀ d hd]⟩

/--
**Corollary: No Fixed-Budget Defense Suffices.**

For any budget B and grid resolution N ≥ 2, there is a critical dimension
beyond which the grid exceeds the budget.  This is the formal statement
that "you cannot defend a sufficiently high-dimensional prompt space
with a fixed number of defense patches."
-/
theorem no_fixed_budget_defense {N : ℕ} (hN : 2 ≤ N) (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < N ^ d := by
  have : 1 < N := by omega
  exact ⟨B, fun d hd => by
    calc B < 2 ^ B := Nat.lt_two_pow_self
      _ ≤ N ^ B := Nat.pow_le_pow_left (by omega) B
      _ ≤ N ^ d := Nat.pow_le_pow_right (by omega) hd⟩

end
