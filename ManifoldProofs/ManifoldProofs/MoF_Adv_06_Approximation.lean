/-
  MoF Advanced Part 6: Statistical Approximation of the AD Surface
  =================================================================
  Under what conditions is a function well-approximated by smooth functions?

  Key question: When is the AD surface well-approximated by a GP?

  Full GP theory requires probability/stochastic processes. We prove the
  DETERMINISTIC approximation foundations:

  Results:
    1. continuous_approximation_on_compact — continuous on compact → uniformly continuous
    2. uniform_continuous_bounded_variation — uniformly continuous on [a,b] → bounded
    3. lipschitz_is_uniformly_continuous — Lipschitz → uniformly continuous
    4. lipschitz_approx_error — Lipschitz error bound from distance
    5. approximation_preserves_basin_interior — ‖f-g‖∞ ≤ ε, f(x) > τ+ε ⟹ g(x) > τ
    6. approximation_preserves_safe_interior — ‖f-g‖∞ ≤ ε, f(x) < τ-ε ⟹ g(x) < τ
    7. approximation_uncertain_band — |f(x)-τ| ≤ ε ⟹ classification uncertain
-/

import Mathlib

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace MoF

/-! ## 1. Continuous on compact ⟹ uniformly continuous -/

/-- Every continuous function on a compact metric space is uniformly continuous. -/
theorem continuous_approximation_on_compact
    {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] {f : X → Y} (hf : Continuous f) :
    UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf

/-! ## 2. Uniformly continuous on [a,b] ⟹ bounded -/

/-- A continuous real-valued function on a compact set attains its maximum,
    hence is bounded. We state: continuous f on a nonempty compact K implies
    f is bounded above on K. -/
theorem uniform_continuous_bounded_variation
    {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (f : ℝ → ℝ) (hf : ContinuousOn f K) :
    ∃ M : ℝ, ∀ x ∈ K, f x ≤ M := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hf
  exact ⟨f x, fun y hy => hmax hy⟩

/-! ## 3. Lipschitz ⟹ uniformly continuous -/

/-- Every Lipschitz function is uniformly continuous. -/
theorem lipschitz_is_uniformly_continuous
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    UniformContinuous f :=
  hf.uniformContinuous

/-! ## 4. Lipschitz approximation error from distance bound -/

/-- If f is L-Lipschitz and dist(x, x₀) ≤ r, then |f(x) - f(x₀)| ≤ L * r. -/
theorem lipschitz_approx_error
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {x x₀ : X} {r : ℝ} (hr : dist x x₀ ≤ r) :
    |f x - f x₀| ≤ L * r := by
  have h1 : dist (f x) (f x₀) ≤ L * dist x x₀ := hf.dist_le_mul x x₀
  rw [Real.dist_eq] at h1
  calc |f x - f x₀| ≤ ↑L * dist x x₀ := h1
    _ ≤ ↑L * r := by
        apply mul_le_mul_of_nonneg_left hr
        exact NNReal.coe_nonneg L

/-! ## 5. Approximation preserves basin interior -/

/-- If the sup-norm error ‖f - g‖∞ ≤ ε and f(x) > τ + ε, then g(x) > τ.
    Points strictly inside the "above-threshold" basin remain classified correctly. -/
theorem approximation_preserves_basin_interior
    {X : Type*} {f g : X → ℝ} {τ ε : ℝ}
    (happrox : ∀ x, |f x - g x| ≤ ε)
    {x : X} (hfx : f x > τ + ε) :
    g x > τ := by
  have hab := happrox x
  rw [abs_le] at hab
  linarith [hab.1]

/-! ## 6. Approximation preserves safe interior -/

/-- If ‖f - g‖∞ ≤ ε and f(x) < τ - ε, then g(x) < τ.
    Points strictly inside the "below-threshold" (safe) region stay safe. -/
theorem approximation_preserves_safe_interior
    {X : Type*} {f g : X → ℝ} {τ ε : ℝ}
    (happrox : ∀ x, |f x - g x| ≤ ε)
    {x : X} (hfx : f x < τ - ε) :
    g x < τ := by
  have hab := happrox x
  rw [abs_le] at hab
  linarith [hab.2]

/-! ## 7. Approximation uncertain band -/

/-- If |f(x) - τ| ≤ ε and ‖f - g‖∞ ≤ ε, then we cannot determine the sign
    of g(x) - τ: it could be anywhere in [-2ε, 2ε].
    We state: g(x) lies in [τ - 2ε, τ + 2ε]. -/
theorem approximation_uncertain_band
    {X : Type*} {f g : X → ℝ} {τ ε : ℝ}
    (happrox : ∀ x, |f x - g x| ≤ ε)
    {x : X} (hfx : |f x - τ| ≤ ε) :
    |g x - τ| ≤ 2 * ε := by
  have hab := happrox x
  rw [abs_le] at hab hfx ⊢
  constructor <;> linarith [hab.1, hab.2, hfx.1, hfx.2]

end MoF
