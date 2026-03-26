/-
  MoF Cost Analysis Part 3: Hitting Time Foundations
  ===================================================
  Deterministic foundations for random search hitting time analysis.

  When uniformly sampling a space, the expected number of trials to hit
  a set of probability p is 1/p (geometric distribution). Here we prove
  the underlying analytic facts:
    1. Partial geometric series formula
    2. Partial geometric sums bounded by 1/p
    3. Miss probability (1-p)^n is monotone decreasing in n
    4. Miss probability tends to 0
    5. Bernoulli's inequality: (1-p)^n ≤ 1 for 0 ≤ p ≤ 1
-/

import Mathlib

open Finset Filter Topology BigOperators

namespace MoF

/-! ## 1. Partial Geometric Series Formula -/

/-- The partial geometric series: ∑_{k=0}^{n-1} r^k = (r^n - 1) / (r - 1) for r ≠ 1.
    Specialised to r = 1 - p: ∑_{k=0}^{n-1} (1-p)^k = (1 - (1-p)^n) / p for p ≠ 0. -/
theorem geometric_sum_bound (p : ℝ) (hp : p ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 - p) ^ k = (1 - (1 - p) ^ n) / p := by
  have h1mp : (1 : ℝ) - p ≠ 1 := by intro h; apply hp; linarith
  rw [geom_sum_eq h1mp]
  ring

/-! ## 2. Partial Geometric Sums Bounded by 1/p -/

/-- For 0 < p ≤ 1, the partial geometric sum ∑_{k=0}^{n-1} (1-p)^k ≤ 1/p.
    This follows because partial sums of a positive convergent series are
    bounded by the infinite sum, which equals (1-(1-p))⁻¹ = 1/p. -/
theorem geometric_sum_le_inverse (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 - p) ^ k ≤ 1 / p := by
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  have hsummable : Summable (fun k : ℕ => (1 - p) ^ k) :=
    summable_geometric_of_lt_one h0 h1
  have htsum : ∑' k : ℕ, (1 - p) ^ k = (1 - (1 - p))⁻¹ :=
    tsum_geometric_of_lt_one h0 h1
  calc ∑ k ∈ Finset.range n, (1 - p) ^ k
      ≤ ∑' k : ℕ, (1 - p) ^ k := hsummable.sum_le_tsum (Finset.range n) (fun k _ => pow_nonneg h0 k)
    _ = (1 - (1 - p))⁻¹ := htsum
    _ = p⁻¹ := by ring_nf
    _ = 1 / p := by rw [one_div]

/-! ## 3. Miss Probability is Monotone Decreasing -/

/-- The miss probability (1-p)^n is nonincreasing in n for 0 < p ≤ 1. -/
theorem miss_probability_antitone (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    Antitone (fun n : ℕ => (1 - p) ^ n) := by
  intro m n hmn
  apply pow_le_pow_of_le_one
  · linarith
  · linarith
  · exact hmn

/-- Strict version: if p > 0, then (1-p)^(n+1) < (1-p)^n when p < 1. -/
theorem miss_probability_decreasing (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) (n : ℕ) :
    (1 - p) ^ (n + 1) < (1 - p) ^ n := by
  have h0 : 0 < 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  calc (1 - p) ^ (n + 1)
      = (1 - p) ^ n * (1 - p) := pow_succ (1 - p) n
    _ < (1 - p) ^ n * 1 := by {
        apply mul_lt_mul_of_pos_left h1
        exact pow_pos h0 n
      }
    _ = (1 - p) ^ n := mul_one _

/-! ## 4. Miss Probability Vanishes -/

/-- The miss probability (1-p)^n → 0 as n → ∞, for 0 < p ≤ 1. -/
theorem miss_probability_vanishes (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    Tendsto (fun n : ℕ => (1 - p) ^ n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · linarith
  · linarith

/-! ## 5. Bernoulli-type Bound: Miss Probability Bounded by 1 -/

/-- For 0 ≤ p ≤ 1, the miss probability satisfies 0 ≤ (1-p)^n ≤ 1. -/
theorem miss_probability_bounds (p : ℝ) (hp_nn : 0 ≤ p) (hp_le : p ≤ 1) (n : ℕ) :
    0 ≤ (1 - p) ^ n ∧ (1 - p) ^ n ≤ 1 := by
  constructor
  · exact pow_nonneg (by linarith) n
  · exact pow_le_one₀ (by linarith) (by linarith)

/-! ## 6. Expected Hits in n Trials -/

/-- If each trial independently hits with probability p, the expected fraction
    of hits in n trials is p. Combinatorially: n · p / n = p.
    We state this as: for M > 0 and S ≤ M, the ratio S/M satisfies
    n * (S / M) / n = S / M. -/
theorem expected_hit_fraction (S M : ℝ) (hM : 0 < M) (_hS_nn : 0 ≤ S) (_hS_le : S ≤ M)
    (n : ℕ) (hn : 0 < (n : ℝ)) :
    ↑n * (S / M) / ↑n = S / M := by
  field_simp

/-! ## 7. Infinite Geometric Series = 1/p -/

/-- The infinite geometric series ∑_{k=0}^∞ (1-p)^k = 1/p for 0 < p ≤ 1.
    This is the expected number of trials in a geometric distribution. -/
theorem tsum_geometric_eq_inv (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    ∑' k : ℕ, (1 - p) ^ k = 1 / p := by
  rw [tsum_geometric_of_lt_one (by linarith) (by linarith)]
  simp [one_div]

/-! ## 8. Sufficient Trials for Target Confidence -/

/-- After n trials each with success probability p (0 < p ≤ 1),
    the probability of at least one success is 1 - (1-p)^n,
    and this quantity is nonneg and at most 1. -/
theorem hit_probability_bounds (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (n : ℕ) :
    0 ≤ 1 - (1 - p) ^ n ∧ 1 - (1 - p) ^ n ≤ 1 := by
  obtain ⟨h0, h1⟩ := miss_probability_bounds p (le_of_lt hp_pos) hp_le n
  exact ⟨by linarith, by linarith⟩

/-- More trials means higher (or equal) probability of at least one hit. -/
theorem hit_probability_monotone (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    Monotone (fun n : ℕ => 1 - (1 - p) ^ n) := by
  intro m n hmn
  have := miss_probability_antitone p hp_pos hp_le hmn
  linarith

/-- The hit probability 1 - (1-p)^n → 1 as n → ∞. -/
theorem hit_probability_tends_to_one (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    Tendsto (fun n : ℕ => 1 - (1 - p) ^ n) atTop (𝓝 1) := by
  have h := miss_probability_vanishes p hp_pos hp_le
  have : (fun n : ℕ => 1 - (1 - p) ^ n) = (fun n => 1 - (1 - p) ^ n) := rfl
  convert Tendsto.const_sub (1 : ℝ) h using 1
  simp

end MoF
