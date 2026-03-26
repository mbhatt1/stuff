import Mathlib
/-
  MoF_04_LipschitzBasin.lean
  ==========================
  Part 4 of 10 — "Manifold of Failure" Lean 4 formalization.

  **Core theorem: Successful attacks are robust — basins have quantitative radius.**

  If the Alignment Deviation function AD is L-Lipschitz and AD(p) > τ,
  then the ball of radius (AD(p) - τ)/L around p is entirely unsafe.

  We prove:
    1. lipschitz_basin_ball        — the core quantitative bound
    2. robustnessRadius_pos        — the radius is positive when f(p) > τ, L > 0
    3. basin_ball_subset           — the ball is contained in the superlevel set
    4. perturbation_stability      — corollary: any point in the ball is unsafe
    5. robustnessRadius_monotone   — more deviant ⟹ larger basin radius
-/

noncomputable section

open Metric Set

open scoped NNReal

namespace MoF

/-! ### Definition: Robustness Radius -/

/--
The guaranteed basin radius around a point with function value `fp` above
threshold `τ`, given Lipschitz constant `L`.
-/
def robustnessRadius (fp τ : ℝ) (L : ℝ) : ℝ := (fp - τ) / L

/-! ### Auxiliary arithmetic -/

private theorem mul_lt_of_lt_div {a b c : ℝ} (hc : 0 < c) (h : a < b / c) :
    c * a < b := by
  have : a * c < b := by rwa [lt_div_iff₀ hc] at h
  linarith

/-! ## 1. lipschitz_basin_ball -/

/--
**Core basin ball theorem.**
If `f` is `L`-Lipschitz, `f(p) > τ`, and `dist p' p < (f(p) - τ) / L`,
then `f(p') > τ`.

Proof idea: `|f(p) - f(p')| ≤ L · dist(p, p') < f(p) - τ`,
so `f(p') > f(p) - (f(p) - τ) = τ`.
-/
theorem lipschitz_basin_ball
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p p' : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ)
    (h_close : dist p' p < (f p - τ) / L) :
    f p' > τ := by
  have h_abs : |f p' - f p| ≤ (L : ℝ) * dist p' p := by
    have := hf.dist_le_mul p' p; rwa [Real.dist_eq] at this
  have h_Ldist : ↑L * dist p' p < f p - τ := mul_lt_of_lt_div hL h_close
  have h_gap : 0 < f p - τ := by linarith
  linarith [neg_abs_le (f p' - f p)]

/-! ## 2. robustnessRadius_pos -/

/--
If `f(p) > τ` and `L > 0`, then the robustness radius is positive.
-/
theorem robustnessRadius_pos
    {fp τ : ℝ} {L : ℝ}
    (hL : 0 < L)
    (h_above : fp > τ) :
    robustnessRadius fp τ L > 0 := by
  unfold robustnessRadius
  exact div_pos (by linarith) hL

/-! ## 3. basin_ball_subset -/

/--
The open ball of robustness radius around `p` is contained in the
superlevel set `{x | f x > τ}`.
-/
theorem basin_ball_subset
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ) :
    Metric.ball p (robustnessRadius (f p) τ L) ⊆ {x | f x > τ} := by
  intro p' hp'
  rw [Metric.mem_ball] at hp'
  simp only [mem_setOf_eq]
  exact lipschitz_basin_ball hf hL h_above hp'

/-! ## 4. perturbation_stability -/

/--
**Perturbation stability (corollary).**
For any `p'` in the robustness ball around `p`, we have `f(p') > τ`.
-/
theorem perturbation_stability
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p p' : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ)
    (h_in_ball : p' ∈ Metric.ball p (robustnessRadius (f p) τ L)) :
    f p' > τ := by
  exact basin_ball_subset hf hL h_above h_in_ball

/-! ## 5. robustnessRadius_monotone -/

/--
If `f(p₁) ≤ f(p₂)`, then `robustnessRadius` for `p₁` is at most that for `p₂`.
More deviant points have larger safe perturbation balls.
-/
theorem robustnessRadius_monotone
    {fp₁ fp₂ τ : ℝ} {L : ℝ}
    (hL : 0 < L)
    (h_le : fp₁ ≤ fp₂) :
    robustnessRadius fp₁ τ L ≤ robustnessRadius fp₂ τ L := by
  unfold robustnessRadius
  apply div_le_div_of_nonneg_right _ (le_of_lt hL)
  linarith

end MoF

end
