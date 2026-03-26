import Mathlib
/-
  MoF_Cost_02_BasinVolume.lean
  ============================
  Basin volume lower bound via Lipschitz robustness balls.

  If the Alignment Deviation function f is L-Lipschitz and f(p) > τ,
  the basin {x | f x > τ} contains the ball of radius (f p - τ)/L
  around p.  Consequently, its Lebesgue measure is at least that of
  the ball, and in particular is strictly positive.

  We prove:
    1. robustness_ball_subset_basin  — the robustness ball sits inside the basin
    2. basin_measure_ge_ball         — measure monotonicity gives the lower bound
    3. basin_measure_ge_ball_pos     — the basin has strictly positive measure
    4. basin_measurableSet           — the basin is Lebesgue-measurable
-/

noncomputable section

open Metric Set MeasureTheory Topology

open scoped NNReal

namespace MoF

/-! ## 1. robustness_ball_subset_basin -/

/--
If `f` is `L`-Lipschitz, `f p > τ`, and `L > 0`, then the open ball of
radius `(f p - τ) / L` around `p` is contained in the superlevel set
`{x | f x > τ}`.
-/
theorem robustness_ball_subset_basin
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (_h_above : f p > τ) :
    Metric.ball p ((f p - τ) / ↑L) ⊆ {x | f x > τ} := by
  intro q hq
  rw [Metric.mem_ball] at hq
  simp only [mem_setOf_eq]
  have h_lip : |f q - f p| ≤ (L : ℝ) * dist q p := by
    have := hf.dist_le_mul q p; rwa [Real.dist_eq] at this
  have h_bound : (L : ℝ) * dist q p < f p - τ := by
    have hq' : dist q p < (f p - τ) / ↑L := hq
    rwa [lt_div_iff₀ hL, mul_comm] at hq'
  linarith [neg_abs_le (f q - f p)]

/-! ## 2. basin_measure_ge_ball -/

/--
The measure of the basin `{x | f x > τ}` is at least the measure
of the robustness ball around `p`.
-/
theorem basin_measure_ge_ball
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ) :
    μ (Metric.ball p ((f p - τ) / ↑L)) ≤ μ {x | f x > τ} :=
  measure_mono (robustness_ball_subset_basin hf hL h_above)

/-! ## 3. basin_measure_ge_ball_pos -/

/--
If `f` is continuous and `f p > τ`, then the basin `{x | f x > τ}` has
strictly positive measure with respect to any measure for which open
nonempty sets have positive measure.

This works for `X = EuclideanSpace ℝ (Fin n)` with Lebesgue measure,
for `ℝ × ℝ`, and for any space satisfying `IsOpenPosMeasure μ`.
-/
theorem basin_measure_ge_ball_pos
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf_cont : Continuous f)
    {p : X} {τ : ℝ}
    (h_above : f p > τ) :
    0 < μ {x : X | f x > τ} := by
  apply IsOpen.measure_pos μ
  · exact isOpen_lt continuous_const hf_cont
  · exact ⟨p, h_above⟩

/-! ## 4. basin_measurableSet -/

/--
For continuous `f`, the basin `{x | f x > τ}` is a measurable set.
It is open (preimage of the open ray `(τ, ∞)` under a continuous map),
and open sets are measurable in any `OpensMeasurableSpace`.
-/
theorem basin_measurableSet
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → ℝ} (hf_cont : Continuous f) {τ : ℝ} :
    MeasurableSet {x | f x > τ} :=
  (isOpen_lt continuous_const hf_cont).measurableSet

end MoF

end
