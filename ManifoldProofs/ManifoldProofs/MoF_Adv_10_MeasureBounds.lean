import Mathlib

/-!
# Manifold of Failure — Quantitative Measure Bounds on Failure Regions

We prove quantitative bounds on the measure of superlevel sets `{x | f x > τ}`,
connecting alignment deviation (AD) surface properties to the volume of
vulnerable regions.

## Main results

1. `basin_measure_monotone_threshold` — higher threshold ⇒ smaller basin measure
2. `basin_empty_above_sup` — basin is empty above the pointwise supremum
3. `basin_full_below_inf` — basin is the whole space below the pointwise infimum
4. `basin_containment_strict` — strict threshold ordering gives strict containment
5. `basin_nonconstant_distinct` — nonconstant f yields distinct basins
6. `markov_ennreal_basin` — Markov inequality for superlevel sets (ENNReal version)
7. `markov_real_basin` — Markov inequality for superlevel sets (real version)
-/

noncomputable section

open Set MeasureTheory Topology ENNReal

namespace MoF

variable {X : Type*}

/-! ## 1. basin_measure_monotone_threshold -/

/--
If τ₁ ≤ τ₂, then {f > τ₂} ⊆ {f > τ₁}, so μ({f > τ₂}) ≤ μ({f > τ₁}).
Higher threshold yields a smaller (or equal) basin.
-/
theorem basin_measure_monotone_threshold
    [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) :
    μ {x | f x > τ₂} ≤ μ {x | f x > τ₁} := by
  apply measure_mono
  intro x hx
  simp only [mem_setOf_eq] at *
  linarith

/-! ## 2. basin_empty_above_sup -/

/--
If f is bounded above by M (f(x) ≤ M for all x) and τ ≥ M, then {f > τ} = ∅.
No point can exceed the threshold when the threshold is at or above the
pointwise supremum.
-/
theorem basin_empty_above_sup
    (f : X → ℝ) {M τ : ℝ} (hbound : ∀ x, f x ≤ M) (hτ : τ ≥ M) :
    {x | f x > τ} = ∅ := by
  ext x
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
  linarith [hbound x]

/-! ## 3. basin_full_below_inf -/

/--
If f(x) ≥ m for all x and τ < m, then {f > τ} = Set.univ.
Every point exceeds the threshold when the threshold is strictly below
the pointwise infimum.
-/
theorem basin_full_below_inf
    (f : X → ℝ) {m τ : ℝ} (hbound : ∀ x, f x ≥ m) (hτ : τ < m) :
    {x | f x > τ} = Set.univ := by
  ext x
  simp only [mem_setOf_eq, mem_univ, iff_true]
  linarith [hbound x]

/-! ## 4. basin_containment_strict -/

/--
For τ₁ < τ₂, we have {f > τ₂} ⊆ {f > τ₁} (strict monotonicity of containment).
-/
theorem basin_containment_strict
    (f : X → ℝ) {τ₁ τ₂ : ℝ} (hτ : τ₁ < τ₂) :
    {x | f x > τ₂} ⊆ {x | f x > τ₁} := by
  intro x hx
  simp only [mem_setOf_eq] at *
  linarith

/-! ## 5. basin_nonconstant_distinct -/

/--
If f takes distinct values at two points, there exist thresholds τ₁ < τ₂
with {f > τ₁} ≠ {f > τ₂}. Specifically, choose τ₁, τ₂ to separate
the two function values so one point is in one basin but not the other.
-/
theorem basin_nonconstant_distinct
    {a b : X} (f : X → ℝ) (hab : f a < f b) :
    ∃ τ₁ τ₂ : ℝ, τ₁ < τ₂ ∧ {x | f x > τ₁} ≠ {x | f x > τ₂} := by
  -- Choose τ₁ = f a and τ₂ = (f a + f b) / 2
  -- Then b ∈ {f > τ₁} and b ∈ {f > τ₂}, but we need a point that separates.
  -- Actually: choose τ₁ between f a and f b, and τ₂ = f b.
  -- Then b ∈ {f > τ₁} \ {f > τ₂} doesn't work since f b > τ₂ = f b is false.
  -- Better: τ₁ = f a, τ₂ = (f a + f b) / 2.
  -- Then b ∈ {f > τ₂} since f b > (f a + f b)/2 iff f b > f a (true).
  -- And a ∈ {f > τ₁} iff f a > f a, which is false. So a ∉ {f > τ₁}.
  -- Hmm, we need a ∈ one set but not the other.
  -- Let τ₁ = (f a + f b) / 2 - 1 and τ₂ = (f a + f b) / 2? Too arbitrary.
  -- Simplest: τ₁ = f a, τ₂ = f a + (f b - f a) / 2 = (f a + f b) / 2.
  -- b ∈ {f > τ₁}: f b > f a ✓
  -- b ∈ {f > τ₂}: f b > (f a + f b)/2 iff f b > f a ✓
  -- a ∉ {f > τ₁}: f a > f a is false ✓
  -- a ∉ {f > τ₂}: f a > (f a + f b)/2 iff f a > f b, false ✓
  -- So both sets exclude a and include b... they could be equal.
  -- We need to choose so that one set contains a point the other doesn't.
  -- Pick τ₁ strictly between f a and f b, and pick τ₂ = f b.
  -- a ∉ {f > τ₁} since f a < τ₁. b ∈ {f > τ₁} since f b > τ₁. ✓
  -- b ∉ {f > τ₂} since ¬(f b > f b). So b ∈ {f > τ₁} \ {f > τ₂}. ✓
  -- Thus {f > τ₁} ≠ {f > τ₂}.
  refine ⟨(f a + f b) / 2, f b, by linarith, ?_⟩
  intro heq
  -- b ∈ {f > (f a + f b)/2} since f b > (f a + f b)/2
  have hb_in : b ∈ {x | f x > (f a + f b) / 2} := by
    simp only [mem_setOf_eq]; linarith
  -- b ∉ {f > f b}
  have hb_not : b ∉ {x | f x > f b} := by
    simp only [mem_setOf_eq]; linarith
  rw [heq] at hb_in
  exact hb_not hb_in

/-! ## 6. markov_ennreal_basin — Markov's inequality (ENNReal) -/

/--
**Markov's inequality for superlevel sets (ENNReal version).**
For a measurable function `g : X → ℝ≥0∞` and threshold `ε`,
we have `ε * μ({g ≥ ε}) ≤ ∫⁻ x, g x ∂μ`.

This wraps Mathlib's `mul_meas_ge_le_lintegral`.
-/
theorem markov_ennreal_basin
    [MeasurableSpace X]
    (μ : Measure X) {g : X → ℝ≥0∞} (hg : Measurable g) (ε : ℝ≥0∞) :
    ε * μ {x | ε ≤ g x} ≤ ∫⁻ x, g x ∂μ :=
  mul_meas_ge_le_lintegral hg ε

/-! ## 7. markov_real_basin — Markov's inequality (real-valued) -/

/--
**Markov's inequality for superlevel sets (real version).**
For a nonneg a.e. integrable function `f : X → ℝ` and threshold `ε`,
we have `ε * μ.real({f ≥ ε}) ≤ ∫ x, f x ∂μ`.

This wraps Mathlib's `mul_meas_ge_le_integral_of_nonneg`.
-/
theorem markov_real_basin
    [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : Integrable f μ) (ε : ℝ) :
    ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ :=
  mul_meas_ge_le_integral_of_nonneg hf_nonneg hf_int ε

end MoF
