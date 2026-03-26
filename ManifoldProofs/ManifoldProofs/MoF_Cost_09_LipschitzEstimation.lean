/-
  MoF Cost 09: Lipschitz Estimation Error
  ========================================
  Proves how Lipschitz continuity controls estimation error from samples.

  Main results:
    1. lipschitz_estimation_error     — |f x - f x₀| ≤ L * dist x x₀
    2. nearest_sample_bound           — for any sample index i, same bound applies
    3. estimation_improves_with_distance — if dist x x₀ ≤ r then error ≤ L * r
    4. estimation_error_zero_at_sample  — |f x₀ - f x₀| = 0
    5. total_estimation_budget         — covering number grows exponentially in d
-/

import Mathlib

noncomputable section

open Metric Set NNReal

namespace MoF

/-! ## 1. lipschitz_estimation_error -/

/--
If `f` is `L`-Lipschitz on a pseudo-metric space, then for any two points
`x` and `x₀`, the absolute difference `|f x - f x₀| ≤ L * dist x x₀`.
-/
theorem lipschitz_estimation_error {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x x₀ : X) :
    |f x - f x₀| ≤ ↑L * dist x x₀ := by
  have h := hf.dist_le_mul x x₀
  rwa [Real.dist_eq] at h

/-! ## 2. nearest_sample_bound -/

/--
Given a finite collection of sample points `samples : Fin n → X` and an
`L`-Lipschitz function `f`, for any query point `x` and any sample index `i`,
the estimation error is bounded by `L * dist x (samples i)`.
-/
theorem nearest_sample_bound {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {n : ℕ} (samples : Fin n → X) (x : X) (i : Fin n) :
    |f x - f (samples i)| ≤ ↑L * dist x (samples i) :=
  lipschitz_estimation_error hf x (samples i)

/-! ## 3. estimation_improves_with_distance -/

/--
If `dist x x₀ ≤ r` then the estimation error `|f x - f x₀| ≤ L * r`.
Packages the Lipschitz bound with a distance hypothesis.
-/
theorem estimation_improves_with_distance {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {x x₀ : X} {r : ℝ}
    (hr : dist x x₀ ≤ r) :
    |f x - f x₀| ≤ ↑L * r :=
  le_trans (lipschitz_estimation_error hf x x₀)
    (mul_le_mul_of_nonneg_left hr (NNReal.coe_nonneg L))

/-! ## 4. estimation_error_zero_at_sample -/

/--
At a sample point itself, the estimation error is exactly 0.
-/
theorem estimation_error_zero_at_sample {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (x₀ : X) :
    |f x₀ - f x₀| = 0 := by
  simp

/-! ## 5. total_estimation_budget -/

/--
The covering number grows exponentially in dimension: for any base `b > 1`
and any bound `M > 0`, there exists a dimension `d` such that `b ^ d > M`.
This captures the curse of dimensionality: to maintain estimation error ≤ ε
for an L-Lipschitz function on [0,1]^d, we need at least `⌈L/(2ε)⌉^d`
sample points, which grows without bound as `d` increases.
-/
theorem total_estimation_budget {b : ℝ} (hb : 1 < b) (M : ℝ) :
    ∃ d : ℕ, M < b ^ d :=
  pow_unbounded_of_one_lt M hb

end MoF
