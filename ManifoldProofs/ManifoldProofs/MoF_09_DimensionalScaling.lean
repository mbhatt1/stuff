import Mathlib

/-!
# Manifold of Failure — Part 9: Curse of Dimensionality for Defense

We prove that the cost of defending a behavioral space grows exponentially
in its dimension, making exhaustive defense fundamentally intractable.

## Main results

- `grid_card` — the number of cells in a d-dimensional N-partition is N^d
- `grid_exponential_growth` — N^d → ∞ as d → ∞ for N ≥ 2
- `coverage_fraction_vanishes` — for 0 ≤ r < 1, r^d → 0
- `defense_patch_shrinks` — defense coverage fraction r^d → 0
- `queries_lower_bound` — filling an N^d grid requires ≥ N^d queries
- `exponential_base` — (1/r)^d → ∞ for 0 < r < 1
- `no_fixed_budget_defense` — any fixed budget is eventually exceeded
-/

noncomputable section

open Set Filter Fintype Topology

namespace MoF

/-! ## 1. Grid Discretization -/

/--
For an N-partition in d dimensions, the number of cells is N^d.
The d-dimensional grid `Fin d → Fin N` has cardinality `N ^ d`.
-/
theorem grid_card (N d : ℕ) :
    Fintype.card (Fin d → Fin N) = N ^ d := by
  simp [Fintype.card_fin]

/-! ## 2. Exponential Growth of Grid Size -/

/--
For N ≥ 2, the grid size N^d grows without bound as d → ∞.
This is the combinatorial core of the dimensionality curse.
-/
theorem grid_exponential_growth {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (fun d => (N : ℝ) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact_mod_cast hN

/--
N^d ≥ 2^d for N ≥ 2, giving a concrete exponential lower bound.
-/
theorem grid_lower_bound {N : ℕ} (hN : 2 ≤ N) (d : ℕ) :
    2 ^ d ≤ N ^ d :=
  Nat.pow_le_pow_left (by linarith) d

/-! ## 3. Coverage Fraction Vanishes -/

/--
For 0 ≤ r < 1, r^d → 0 as d → ∞. Each defense patch covers an
exponentially shrinking fraction of the behavioral space.
-/
theorem coverage_fraction_vanishes {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

/-! ## 4. Defense Patch Shrinks -/

/--
If a defense patches a ball of relative radius r < 1 in each dimension,
the fraction of space covered is r^d, which tends to 0 as d → ∞.
The coverage fraction is bounded by C * r^d for some constant C > 0,
and this product also tends to 0.
-/
theorem defense_patch_shrinks
    {r C : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => C * r ^ d) atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  rw [show (0 : ℝ) = C * 0 from by ring]
  exact h.const_mul C

/--
For 0 < r < 1, r^(d+1) < r^d — each additional dimension strictly
shrinks the fraction of space a single defense patch can cover.
-/
theorem defense_patch_strict_decrease
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (d : ℕ) :
    r ^ (d + 1) < r ^ d := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos hr0 d) hr1

/-! ## 5. Query Lower Bound (Pigeonhole) -/

/--
If `f : Fin k → (Fin d → Fin N)` is injective (each query fills a
distinct grid cell), then `k ≤ N ^ d`.  This is the pigeonhole
principle applied to the grid: you cannot inject more elements into
a set than its cardinality.
-/
theorem queries_lower_bound_injective (N d k : ℕ)
    (f : Fin k → (Fin d → Fin N)) (hf : Function.Injective f) :
    k ≤ N ^ d := by
  rw [← grid_card N d, show k = Fintype.card (Fin k) from by simp]
  exact Fintype.card_le_of_injective f hf

/--
If `f : Fin k → (Fin d → Fin N)` is surjective (every grid cell is
hit by some query), then `N ^ d ≤ k`.  To cover all cells of the
grid you need at least `N ^ d` queries.
-/
theorem queries_lower_bound_surjective (N d k : ℕ)
    (f : Fin k → (Fin d → Fin N)) (hf : Function.Surjective f) :
    N ^ d ≤ k := by
  rw [← grid_card N d, show k = Fintype.card (Fin k) from by simp]
  exact Fintype.card_le_of_surjective f hf

/--
The grid has exactly N^d cells, so full coverage requires exactly N^d queries
under the one-query-per-cell model.
-/
theorem queries_exact_cost (N d : ℕ) :
    Fintype.card (Fin d → Fin N) = N ^ d := grid_card N d

/--
Any partial coverage leaves cells uncovered: if `covered < N^d`,
there remain `N^d - covered` uncovered cells.
-/
theorem queries_remaining (N d covered : ℕ)
    (h_cov : covered ≤ N ^ d) :
    N ^ d - covered + covered = N ^ d := by omega

/-! ## 6. Exponential Base -/

/--
For 0 < r < 1, we have 1/r > 1.
-/
theorem exponential_base_gt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    1 < 1 / r := by
  rw [one_div]
  exact (one_lt_inv₀ hr0).mpr hr1

/--
For 0 < r < 1, (1/r)^d → ∞ as d → ∞. The number of defense patches
needed grows exponentially with dimension.
-/
theorem exponential_base {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => (1 / r) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact exponential_base_gt_one hr0 hr1

/--
Concrete identity: (1/r)^d = 1/r^d.
-/
theorem exponential_base_eq {r : ℝ} (_hr0 : 0 < r) (d : ℕ) :
    (1 / r) ^ d = 1 / r ^ d := by
  rw [one_div, inv_pow, one_div]

/--
The number of defense balls needed to cover fraction α of space,
when each ball covers at most C * r^d, tends to infinity.
-/
theorem defense_balls_tendsto_atTop
    {r C α : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C) (hα : 0 < α) :
    Tendsto (fun d : ℕ => α / (C * r ^ d)) atTop atTop := by
  have h_inv : Tendsto (fun d : ℕ => (1 / r) ^ d) atTop atTop :=
    exponential_base hr0 hr1
  have key : ∀ d : ℕ, α / (C * r ^ d) = α / C * (1 / r) ^ d := by
    intro d
    rw [one_div, inv_pow, div_mul_eq_div_div]
    congr 1
  simp_rw [key]
  exact Tendsto.const_mul_atTop (div_pos hα hC) h_inv

/-! ## 7. No Fixed Budget Defense -/

/--
For any fixed budget B : ℕ, there exists d₀ such that for all d ≥ d₀,
the grid size N^d > B. No finite budget can defend a sufficiently
high-dimensional space.
-/
theorem no_fixed_budget_defense {N : ℕ} (hN : 2 ≤ N) (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < N ^ d := by
  have : 1 < N := by omega
  exact ⟨B, fun d hd => by
    calc B < 2 ^ B := Nat.lt_two_pow_self
      _ ≤ N ^ B := Nat.pow_le_pow_left (by omega) B
      _ ≤ N ^ d := Nat.pow_le_pow_right (by omega) hd⟩

/--
Real-valued version: for any real budget B, the grid eventually exceeds it.
-/
theorem no_fixed_budget_defense_real {N : ℕ} (hN : 2 ≤ N) (B : ℝ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < (N : ℝ) ^ d := by
  have h_tend := grid_exponential_growth hN
  rw [Filter.tendsto_atTop_atTop] at h_tend
  obtain ⟨d₀, hd₀⟩ := h_tend (B + 1)
  exact ⟨d₀, fun d hd => by linarith [hd₀ d hd]⟩

/-! ## 8. Summary Structure -/

/--
Bundles the key parameters and facts of the dimensionality curse.
-/
structure DimensionalCurse where
  /-- Number of bins per axis -/
  N : ℕ
  /-- N ≥ 2 for meaningful discretization -/
  hN : 2 ≤ N
  /-- Defense patch radius -/
  r : ℝ
  /-- Radius is positive -/
  hr_pos : 0 < r
  /-- Radius is less than 1 -/
  hr_lt : r < 1

namespace DimensionalCurse

variable (dc : DimensionalCurse)

/-- The grid size N^d tends to infinity. -/
theorem grid_explosion :
    Tendsto (fun d => (dc.N : ℝ) ^ d) atTop atTop :=
  grid_exponential_growth dc.hN

/-- Each defense patch covers a fraction tending to zero. -/
theorem coverage_collapse :
    Tendsto (fun d => dc.r ^ d) atTop (nhds 0) :=
  coverage_fraction_vanishes (le_of_lt dc.hr_pos) dc.hr_lt

/-- The defense cost (1/r)^d grows without bound. -/
theorem cost_explosion :
    Tendsto (fun d => (1 / dc.r) ^ d) atTop atTop :=
  exponential_base dc.hr_pos dc.hr_lt

/-- For any budget, there exists a dimension beyond which defense fails. -/
theorem budget_exceeded (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < dc.N ^ d :=
  no_fixed_budget_defense dc.hN B

/-- Archive size is N^d. -/
theorem archive_size (d : ℕ) :
    Fintype.card (Fin d → Fin dc.N) = dc.N ^ d :=
  grid_card dc.N d

end DimensionalCurse

end MoF

end
