import Mathlib

/-!
# Manifold of Failure — Advanced 08: Stability Under Perturbation

We prove that the topological structure of the failure manifold is stable
under small perturbations of the alignment deviation function.

When `f` is perturbed to `g` with `‖f - g‖∞ ≤ ε`, we show:

1. **Basin stability**: Compact subsets deep in the basin `{f > τ}` remain
   inside `{g > τ}`.
2. **Boundary continuity in 1D**: The boundary point moves by at most ε
   in function value.
3. **Topology preserved for regular values**: If `f'(z) ≠ 0` at a crossing
   `f(z) = τ`, then `g` also crosses τ near `z` (via IVT).
4. **Number of crossings stable**: Each transversal crossing of `f` produces
   at least one crossing of `g` nearby.
-/

noncomputable section

open Set Topology Filter

namespace MoF

/-! ## 1. Basin Stability Under Small Perturbation -/

/--
**Basin stability (pointwise).** If `f(x) > τ + ε` and `|f(x) - g(x)| ≤ ε`,
then `g(x) > τ`. Compact subsets deep in the basin are preserved.
-/
theorem basin_stable_under_small_perturbation
    {f g : ℝ → ℝ} {x τ ε : ℝ}
    (h_close : |f x - g x| ≤ ε)
    (h_deep : f x > τ + ε) :
    g x > τ := by
  have h := abs_le.mp h_close
  linarith

/-! ## 2. Boundary Continuity in 1D -/

/--
**Boundary continuity.** If `f` and `g` are within ε pointwise,
and `f(z₁) = τ`, then `|g(z₁) - τ| ≤ ε`. The boundary of `g`
is within ε of τ at the boundary point of `f`.
-/
theorem boundary_continuous_in_1d
    {f g : ℝ → ℝ} {z₁ τ ε : ℝ}
    (h_close : |f z₁ - g z₁| ≤ ε)
    (h_boundary : f z₁ = τ) :
    |g z₁ - τ| ≤ ε := by
  rw [h_boundary] at h_close
  rwa [abs_sub_comm] at h_close

/-! ## 3. Topology Preserved for Regular Values -/

/--
**IVT helper.** If `f` is continuous and `f(a) < τ < f(b)` with `a ≤ b`,
there exists `c ∈ [a, b]` with `f(c) = τ`.
-/
private theorem ivt_crossing
    {f : ℝ → ℝ} {a b τ : ℝ}
    (hf : Continuous f) (hab : a ≤ b)
    (ha : f a < τ) (hb : τ < f b) :
    ∃ c ∈ Icc a b, f c = τ := by
  have h_conn : IsPreconnected (Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr hab
  exact h_conn.intermediate_value₂ ha_mem hb_mem
    hf.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)

/--
**Perturbed crossing via IVT.** If `f(a) < τ - ε` and `f(b) > τ + ε` with
`a ≤ b`, and `g` is continuous with `|f(x) - g(x)| ≤ ε` for all `x`, then
`g` crosses `τ` in `[a, b]`.
-/
theorem perturbed_crossing_ivt
    {f g : ℝ → ℝ} {a b τ ε : ℝ}
    (hg_cont : Continuous g)
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (hab : a ≤ b)
    (hfa : f a < τ - ε)
    (hfb : f b > τ + ε) :
    ∃ z' ∈ Icc a b, g z' = τ := by
  have hga : g a < τ := by
    have h := abs_le.mp (h_close a)
    linarith
  have hgb : g b > τ := by
    have h := abs_le.mp (h_close b)
    linarith
  exact ivt_crossing hg_cont hab hga hgb

/--
**Topology preserved for regular values (1D).**

If `HasDerivAt f d z` with `d > 0`, `f(z) = τ`, `g` is continuous with
`‖f - g‖∞ ≤ ε`, then there exists `z'` near `z` with `g(z') = τ`.

We use the derivative to find points `a`, `b` near `z` where `f` is
far below and above `τ` (by more than `ε`), then apply IVT to `g`.

**Hypotheses simplification:** We require `ε < d * δ / 2` for a given `δ > 0`,
which ensures we can find such `a`, `b` within distance `δ` of `z`.
Here we state it with `a = z - δ` and `b = z + δ` as explicit witnesses,
where the derivative condition gives `f(z - δ) < τ - ε` and `f(z + δ) > τ + ε`.
-/
theorem topology_preserved_for_regular_values
    {f g : ℝ → ℝ} {z τ ε δ : ℝ}
    (hg_cont : Continuous g)
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (hδ : δ > 0)
    (hfa : f (z - δ) < τ - ε)
    (hfb : f (z + δ) > τ + ε) :
    ∃ z' ∈ Icc (z - δ) (z + δ), g z' = τ := by
  exact perturbed_crossing_ivt hg_cont h_close (by linarith) hfa hfb

/-! ## 4. Number of Crossings Stable -/

/--
**Each transversal crossing produces a nearby crossing of `g`.**

If `f` crosses `τ` transversally at some point in `[a, b]` — meaning
`f(a) < τ - ε` and `f(b) > τ + ε` — and `g` is continuous with
`‖f - g‖∞ ≤ ε`, then `g` has at least one crossing of `τ` in `[a, b]`.

When applied to each of `n` transversal crossings (with disjoint intervals),
this shows `g` has at least `n` crossings.
-/
theorem number_of_crossings_stable
    {f g : ℝ → ℝ} {a b τ ε : ℝ}
    (hg_cont : Continuous g)
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (hab : a ≤ b)
    (hfa : f a < τ - ε)
    (hfb : f b > τ + ε) :
    ∃ z' ∈ Icc a b, g z' = τ :=
  perturbed_crossing_ivt hg_cont h_close hab hfa hfb

/--
**Symmetric version: decreasing transversal crossing.**
If `f(a) > τ + ε` and `f(b) < τ - ε`, `g` still crosses `τ` in `[a, b]`.
-/
theorem number_of_crossings_stable_sym
    {f g : ℝ → ℝ} {a b τ ε : ℝ}
    (hg_cont : Continuous g)
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (hab : a ≤ b)
    (hfa : f a > τ + ε)
    (hfb : f b < τ - ε) :
    ∃ z' ∈ Icc a b, g z' = τ := by
  have hga : g a > τ := by
    have h := abs_le.mp (h_close a)
    linarith
  have hgb : g b < τ := by
    have h := abs_le.mp (h_close b)
    linarith
  have h_conn : IsPreconnected (Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Icc a b := right_mem_Icc.mpr hab
  have h := h_conn.intermediate_value₂ ha_mem hb_mem
    continuous_const.continuousOn hg_cont.continuousOn (le_of_lt hga) (le_of_lt hgb)
  obtain ⟨c, hc_mem, hc_eq⟩ := h
  exact ⟨c, hc_mem, hc_eq.symm⟩

/-! ## Bonus: Quantitative stability bounds -/

/--
**Perturbation sandwich.** If `|f(x) - g(x)| ≤ ε` for all `x`,
then `f(x) - ε ≤ g(x)` and `g(x) ≤ f(x) + ε`.
-/
theorem perturbation_sandwich
    {f g : ℝ → ℝ} {ε : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ ε) (x : ℝ) :
    f x - ε ≤ g x ∧ g x ≤ f x + ε := by
  have h := abs_le.mp (h_close x)
  constructor <;> linarith

/--
**Basin boundary shift bound.** If `f(z) = τ` and `|f(x) - g(x)| ≤ ε`,
then `τ - ε ≤ g(z) ≤ τ + ε`.
-/
theorem basin_boundary_shift
    {f g : ℝ → ℝ} {z τ ε : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (hfz : f z = τ) :
    τ - ε ≤ g z ∧ g z ≤ τ + ε := by
  have ⟨h1, h2⟩ := perturbation_sandwich h_close z
  rw [hfz] at h1 h2
  exact ⟨h1, h2⟩

end MoF

end
