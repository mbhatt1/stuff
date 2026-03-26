import Mathlib

/-!
# Manifold of Failure — Advanced Part 9: Optimization Landscape

**Theorems about the optimization landscape of the failure manifold.**

These properties characterize how efficiently an attacker can navigate the
failure manifold — compactness guarantees maxima exist, Lipschitz bounds
constrain how far values can drop, derivative conditions detect critical
points, and gradient ascent provides a constructive attack direction.

## Main results

1. `continuous_attains_max_on_compact` — a continuous function on a compact
   set attains its maximum.
2. `lipschitz_max_nearby` — Lipschitz bound: f(x) ≥ f(p) - L·dist(x,p).
3. `local_max_is_critical_1d` — a local max of a differentiable function
   on ℝ has zero derivative.
4. `basin_max_on_closure` — f attains its max on any compact region.
5. `gradient_ascent_increases_1d` — positive derivative implies nearby
   increase.
6. `no_local_max_in_interior_of_basin` — a non-critical interior point of
   a superlevel set is not a local max.
-/

noncomputable section

open Set Topology Metric Filter
open scoped NNReal

namespace MoF

/-! ## 1. continuous_attains_max_on_compact -/

/--
A continuous real-valued function on a nonempty compact set attains its
maximum.
-/
theorem continuous_attains_max_on_compact
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K) :
    ∃ p ∈ K, ∀ x ∈ K, f x ≤ f p := by
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne hf
  exact ⟨p, hp, fun x hx => hmax hx⟩

/-! ## 2. lipschitz_max_nearby -/

/--
If `f` is `L`-Lipschitz, then for any `p` and `x`,
`f(x) ≥ f(p) - L · dist(x, p)`.

This bounds how quickly the attack-deviation value can drop as we move
away from an optimum.
-/
theorem lipschitz_max_nearby
    {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (p x : X) :
    f x ≥ f p - ↑L * dist x p := by
  have h := hf.dist_le_mul x p
  rw [Real.dist_eq] at h
  have := neg_abs_le (f x - f p)
  linarith

/-! ## 3. local_max_is_critical_1d -/

/--
If `f : ℝ → ℝ` is differentiable at `x` (with derivative `d`) and `x` is
a local maximum of `f`, then `d = 0`.

Uses Mathlib's `IsLocalMax.hasDerivAt_eq_zero`.
-/
theorem local_max_is_critical_1d
    {f : ℝ → ℝ} {d : ℝ} {x : ℝ}
    (hd : HasDerivAt f d x) (hmax : IsLocalMax f x) :
    d = 0 :=
  hmax.hasDerivAt_eq_zero hd

/-! ## 4. basin_max_on_closure -/

/--
If `f` is continuous on a compact set `K`, then `f` attains its maximum
on `K`. The maximum of AD on any compact region is achieved.

This is a restatement of theorem 1 emphasizing the basin interpretation:
the worst-case attack deviation within any compact basin is always realized.
-/
theorem basin_max_on_closure
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K) :
    ∃ p ∈ K, IsMaxOn f K p :=
  hK.exists_isMaxOn hne hf

/-! ## 5. gradient_ascent_increases_1d -/

/--
If `f : ℝ → ℝ` has derivative `d > 0` at `x`, then there exists `ε > 0`
such that `f(x + ε) > f(x)`.

This formalizes that an attacker with access to a positive gradient can
always find a nearby point with strictly higher attack deviation.

Proof: by contradiction. If `f(x + ε) ≤ f(x)` for all `ε > 0`, then
for all `y > x`, `f(y) ≤ f(x)`, making `x` a right-local max. But the
slope `(f(x+t) - f(x))/t → d > 0`, so for small positive `t` the slope
is positive and `f(x+t) > f(x)`, contradiction.
-/
theorem gradient_ascent_increases_1d
    {f : ℝ → ℝ} {d : ℝ} {x : ℝ}
    (hd : HasDerivAt f d x) (hpos : d > 0) :
    ∃ ε : ℝ, ε > 0 ∧ f (x + ε) > f x := by
  by_contra h
  push_neg at h
  -- h : ∀ ε > 0, f (x + ε) ≤ f x
  -- The slope (f(x+t) - f(x))/t → d as t → 0⁺
  have htend := hd.tendsto_slope_zero_right
  -- For t > 0 small, t⁻¹ • (f(x+t) - f(x)) is near d > 0, hence > 0.
  -- But h says f(x+t) - f(x) ≤ 0 for t > 0, so the slope ≤ 0.
  -- This contradicts the limit being d > 0.
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (x + t) - f x) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hfle := h t ht
    rw [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht)) (by linarith)
  -- But htend says the filter limit is d > 0, so eventually > d/2 > 0.
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (x + t) - f x) > 0 :=
    htend.eventually (Ioi_mem_nhds hpos)
  -- These two eventually-statements contradict each other (the filter is nonempty).
  have := hle.and hev
  simp only [gt_iff_lt] at this
  exact this.exists.elim (fun t ⟨h1, h2⟩ => not_lt.mpr h1 h2)

/-! ## 6. no_local_max_in_interior_of_basin -/

/--
If `f : ℝ → ℝ` is differentiable at `x` and `f'(x) ≠ 0`, then `x` is not
a local maximum of `f`.

Equivalently, at a non-critical interior point of the superlevel set
`{f > τ}`, the attacker can always move to increase the attack deviation.
-/
theorem no_local_max_in_interior_of_basin
    {f : ℝ → ℝ} {d : ℝ} {x : ℝ}
    (hd : HasDerivAt f d x) (hne : d ≠ 0) :
    ¬IsLocalMax f x := by
  intro hmax
  exact hne (hmax.hasDerivAt_eq_zero hd)

end MoF

end
