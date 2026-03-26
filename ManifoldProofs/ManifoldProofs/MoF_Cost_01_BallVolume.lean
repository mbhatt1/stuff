/-
  MoF Cost 01: Ball Volume Lower Bounds
  ======================================
  Proves lower bounds and basic properties of the Lebesgue measure
  of open balls in Euclidean space.
-/

import Mathlib

open MeasureTheory Metric Set ENNReal

namespace MoF

/-! ## 1. Positive measure of open balls -/

/-- An open ball of positive radius in `EuclideanSpace ℝ (Fin n)` has positive Lebesgue measure. -/
theorem ball_measure_pos {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball x r) :=
  Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩

/-- An open ball of positive radius in `Fin n → ℝ` has positive Lebesgue measure. -/
theorem ball_measure_pos_fin {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball x r) :=
  Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩

/-! ## 2. Ball subset monotonicity -/

/-- If `r₁ ≤ r₂` then `ball x r₁ ⊆ ball x r₂`. -/
theorem ball_subset_ball_of_le {α : Type*} [PseudoMetricSpace α] (x : α) {r₁ r₂ : ℝ}
    (h : r₁ ≤ r₂) : Metric.ball x r₁ ⊆ Metric.ball x r₂ :=
  Metric.ball_subset_ball h

/-! ## 3. Measure monotonicity for balls -/

/-- If `r₁ ≤ r₂` then the measure of `ball x r₁` is at most that of `ball x r₂`. -/
theorem ball_measure_mono {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) (x : α) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    μ (Metric.ball x r₁) ≤ μ (Metric.ball x r₂) :=
  measure_mono (Metric.ball_subset_ball h)

/-! ## 4. Exact volume of balls in ℝ -/

/-- The volume of an open ball in `ℝ` of radius `r` is `ofReal (2 * r)`. -/
theorem ball_measure_scale (r : ℝ) :
    volume (Metric.ball (0 : ℝ) r) = ENNReal.ofReal (2 * r) :=
  Real.volume_ball 0 r

end MoF
