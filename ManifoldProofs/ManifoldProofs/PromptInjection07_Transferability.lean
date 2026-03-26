import Mathlib
/-
  PromptInjection07_Transferability.lean

  Lean 4 / Mathlib formalization of Theorem 7 from the
  "Manifold of Failure" prompt-injection framework:

  **Cross-Model Injection Transferability Bound**

  Given two models M1 and M2 with Alignment Deviation functions
  AD1 = f and AD2 = g, if ‖f − g‖_∞ ≤ δ (i.e., ∀ x, |f(x) − g(x)| ≤ δ),
  then:

    1. Any injection achieving f(p) > τ + δ also achieves g(p) > τ.
    2. The superlevel set {x | f(x) > τ + δ} ⊆ {x | g(x) > τ}.
    3. Symmetrically, {x | g(x) > τ + δ} ⊆ {x | f(x) > τ}.
    4. The "transferability rate" (fraction of M1's injections that
       also work on M2) converges to 1 as δ → 0.
    5. If δ = 0 (identical AD surfaces), vulnerability basins coincide.

  This explains why prompt injections transfer across models:
  models with similar AD surfaces have overlapping vulnerability basins.
-/


noncomputable section

open Set

/-! ## 1. Core Transferability Lemma -/

/--
**Core transferability bound (pointwise).**
If `f` and `g` are within `δ` in sup-norm (pointwise) and `f(p) > τ + δ`,
then `g(p) > τ`.

Proof sketch: g(p) ≥ f(p) − |f(p) − g(p)| ≥ f(p) − δ > (τ + δ) − δ = τ.
-/
theorem transferability_pointwise
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : f p > τ + δ) :
    g p > τ := by
  have h1 : |f p - g p| ≤ δ := h_close p
  have h2 := abs_le.mp h1
  linarith

/--
**Symmetric transferability bound.**
If `g(p) > τ + δ`, then `f(p) > τ` (same hypothesis on closeness).
-/
theorem transferability_pointwise_symm
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : g p > τ + δ) :
    f p > τ := by
  have h1 : |f p - g p| ≤ δ := h_close p
  have h2 := abs_le.mp h1
  linarith

/-! ## 2. Superlevel Set Containment -/

/--
**Superlevel set containment (f → g).**
The vulnerability basin of M1 at threshold `τ + δ` is contained in the
vulnerability basin of M2 at threshold `τ`.
-/
theorem superlevel_subset_of_close
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    {x | f x > τ + δ} ⊆ {x | g x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at *
  exact transferability_pointwise h_close hx

/--
**Superlevel set containment (g → f), symmetric direction.**
The vulnerability basin of M2 at threshold `τ + δ` is contained in the
vulnerability basin of M1 at threshold `τ`.
-/
theorem superlevel_subset_of_close_symm
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    {x | g x > τ + δ} ⊆ {x | f x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at *
  exact transferability_pointwise_symm h_close hx

/-! ## 3. Bidirectional Sandwich -/

/--
**Bidirectional sandwich on vulnerability basins.**
The superlevel sets of `f` and `g` are sandwiched:
  {f > τ + δ} ⊆ {g > τ}  and  {g > τ + δ} ⊆ {f > τ}.

This means the vulnerability basins of two δ-close models differ by at most
a "δ-thick boundary layer."
-/
theorem superlevel_sandwich
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    ({x | f x > τ + δ} ⊆ {x | g x > τ}) ∧
    ({x | g x > τ + δ} ⊆ {x | f x > τ}) :=
  ⟨superlevel_subset_of_close h_close τ,
   superlevel_subset_of_close_symm h_close τ⟩

/-! ## 4. Quantitative Pointwise Bounds -/

/--
**Lower bound on g from f.**
If `|f(x) − g(x)| ≤ δ` everywhere, then `g(x) ≥ f(x) − δ` for all `x`.
-/
theorem pointwise_lower_bound
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (x : X) :
    g x ≥ f x - δ := by
  have h1 : |f x - g x| ≤ δ := h_close x
  have h2 := abs_le.mp h1
  linarith

/--
**Upper bound on g from f.**
If `|f(x) − g(x)| ≤ δ` everywhere, then `g(x) ≤ f(x) + δ` for all `x`.
-/
theorem pointwise_upper_bound
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (x : X) :
    g x ≤ f x + δ := by
  have h1 : |f x - g x| ≤ δ := h_close x
  have h2 := abs_le.mp h1
  linarith

/-! ## 5. Identical Models (δ = 0) ⟹ Identical Vulnerability Basins -/

/--
**Zero-distance models have identical superlevel sets.**
If `δ = 0`, i.e., `f = g` pointwise, then `{x | f(x) > τ} = {x | g(x) > τ}`
for every threshold `τ`.  This is the base case: identical models have
identical vulnerability basins.
-/
theorem superlevel_eq_of_zero_dist
    {X : Type*} {f g : X → ℝ}
    (h_close : ∀ x, |f x - g x| ≤ 0)
    (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} := by
  ext x
  simp only [mem_setOf_eq]
  have h_eq : f x = g x := by
    have hab := h_close x
    have h0 : |f x - g x| = 0 := le_antisymm hab (abs_nonneg _)
    have h1 : f x - g x = 0 := abs_eq_zero.mp h0
    linarith
  rw [h_eq]

/--
**Identical functions yield identical superlevel sets (direct statement).**
-/
theorem superlevel_eq_of_eq
    {X : Type*} {f g : X → ℝ}
    (h_eq : ∀ x, f x = g x)
    (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} := by
  ext x
  simp only [mem_setOf_eq, h_eq]

/-! ## 6. Transferability Rate -/

/-!
The **transferability rate** from model M1 (with AD function `f`) to
model M2 (with AD function `g`) at threshold `τ` is the proportion of
M1's successful injections that also succeed on M2.

We model this as a conditional measure:
  T(f, g, τ) = μ({x | f(x) > τ} ∩ {x | g(x) > τ}) / μ({x | f(x) > τ})

Rather than introducing full measure theory, we express the key structural
result: the numerator contains the stronger superlevel set {f > τ + δ},
so the transferability rate is at least μ({f > τ + δ}) / μ({f > τ}).
-/

/--
**Transferability numerator containment.**
The set of prompts that succeed on *both* models contains the
high-margin set `{f > τ + δ}`.
-/
theorem transferability_numerator_contains
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    {x | f x > τ + δ} ⊆ {x | f x > τ} ∩ {x | g x > τ} := by
  intro x hx
  simp only [mem_inter_iff, mem_setOf_eq] at *
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (h_close x)
  exact ⟨by linarith, transferability_pointwise h_close hx⟩

/--
**Full-strength transferability.**
At the elevated threshold `τ + δ`, *every* injection from M1 transfers to M2.
The transferability rate at threshold `τ + δ` is exactly 1.
-/
theorem transferability_rate_one_at_elevated_threshold
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    {x | f x > τ + δ} ⊆ {x | g x > τ} :=
  superlevel_subset_of_close h_close τ

/-! ## 7. Convergence: Transferability → 1 as δ → 0 -/

/--
**Superlevel sets converge as δ → 0.**
For any `ε > 0`, if `δ < ε` then the `(τ+ε)`-superlevel set of `f`
is contained in the `τ`-superlevel set of `g`.  As `δ → 0` we can
take `ε → 0`, so the gap between {f > τ+ε} and {f > τ} vanishes,
meaning nearly all injections transfer.
-/
theorem superlevel_gap_shrinks
    {X : Type*} {f g : X → ℝ} {δ ε : ℝ}
    (hδε : δ ≤ ε)
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    {x | f x > τ + ε} ⊆ {x | g x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at *
  have hfg : g x ≥ f x - δ := pointwise_lower_bound h_close x
  linarith

/--
**In the limit δ = 0, the full superlevel set transfers.**
When `δ = 0`, {f > τ} ⊆ {g > τ} (and vice versa, giving equality).
-/
theorem full_transfer_at_zero_distance
    {X : Type*} {f g : X → ℝ}
    (h_close : ∀ x, |f x - g x| ≤ 0)
    (τ : ℝ) :
    {x | f x > τ} ⊆ {x | g x > τ} := by
  have h_eq := superlevel_eq_of_zero_dist h_close τ
  rw [h_eq]

/--
**Bidirectional full transfer at zero distance.**
-/
theorem full_transfer_at_zero_distance_iff
    {X : Type*} {f g : X → ℝ}
    (h_close : ∀ x, |f x - g x| ≤ 0)
    (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} :=
  superlevel_eq_of_zero_dist h_close τ

/-! ## 8. Coverage Difference Bound -/

/--
**Coverage inclusion bound.**
If `|f(x) − g(x)| ≤ δ` everywhere, then:
  {g > τ + δ}  ⊆  {f > τ}  ⊆  {g > τ − δ}

This means the "coverage" (measure of the superlevel set) of f at threshold τ
is sandwiched between the coverage of g at thresholds τ − δ and τ + δ.
In particular, if coverage is monotone and Lipschitz in the threshold
parameter, then |Coverage_f(τ) − Coverage_g(τ)| is controlled by δ.
-/
theorem coverage_sandwich
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    ({x | g x > τ + δ} ⊆ {x | f x > τ}) ∧
    ({x | f x > τ} ⊆ {x | g x > τ - δ}) := by
  constructor
  · -- {g > τ + δ} ⊆ {f > τ}: symmetric transferability
    exact superlevel_subset_of_close_symm h_close τ
  · -- {f > τ} ⊆ {g > τ − δ}: if f(x) > τ then g(x) ≥ f(x) − δ > τ − δ
    intro x hx
    simp only [mem_setOf_eq] at *
    have hfg : g x ≥ f x - δ := pointwise_lower_bound h_close x
    linarith

/-! ## 9. Lipschitz Coverage Difference Bound -/

/--
**Coverage difference controlled by δ and Lipschitz constant.**

If the "coverage function" C(τ) = μ({x | h(x) > τ}) is `L_C`-Lipschitz
in τ (a reasonable assumption for smooth AD functions on compact domains),
and `|f − g|_∞ ≤ δ`, then:

  |Coverage_f(τ) − Coverage_g(τ)| ≤ 2 · L_C · δ

We prove this abstractly: if a real-valued function C is L_C-Lipschitz and
we know that Coverage_f(τ) is between C(τ − δ) and C(τ + δ) (from the
sandwich), then the difference is at most L_C · 2δ.
-/
theorem coverage_difference_bound
    {C_f C_g : ℝ → ℝ} {L_C δ τ : ℝ}
    (hδ : 0 ≤ δ)
    (hL : 0 ≤ L_C)
    -- C_f(τ) is between C_g(τ − δ) and C_g(τ + δ) (from sandwich)
    (h_lower : C_g (τ + δ) ≤ C_f τ)
    (h_upper : C_f τ ≤ C_g (τ - δ))
    -- C_g is L_C-Lipschitz in the threshold parameter
    (h_lip : ∀ a b : ℝ, |C_g a - C_g b| ≤ L_C * |a - b|) :
    |C_f τ - C_g τ| ≤ 2 * L_C * δ := by
  -- We bound |C_f(τ) − C_g(τ)| by max of the two one-sided gaps
  -- Case analysis: C_f(τ) ≥ C_g(τ) or C_f(τ) < C_g(τ)
  rw [abs_le]
  constructor
  · -- -(2 * L_C * δ) ≤ C_f(τ) − C_g(τ)
    -- C_f(τ) ≥ C_g(τ + δ), so C_f(τ) − C_g(τ) ≥ C_g(τ+δ) − C_g(τ) ≥ −L_C·δ ≥ −2·L_C·δ
    have h1 : C_g (τ + δ) - C_g τ ≥ -(L_C * δ) := by
      have hlip := h_lip (τ + δ) τ
      have hdiff : (τ + δ) - τ = δ := by ring
      rw [hdiff, abs_of_nonneg hδ] at hlip
      rw [abs_le] at hlip
      linarith [hlip.1]
    linarith [mul_nonneg hL hδ]
  · -- C_f(τ) − C_g(τ) ≤ 2 * L_C * δ
    -- C_f(τ) ≤ C_g(τ − δ), so C_f(τ) − C_g(τ) ≤ C_g(τ−δ) − C_g(τ) ≤ L_C·δ ≤ 2·L_C·δ
    have h1 : C_g (τ - δ) - C_g τ ≤ L_C * δ := by
      have hlip := h_lip (τ - δ) τ
      have hdiff : (τ - δ) - τ = -δ := by ring
      rw [hdiff, abs_neg, abs_of_nonneg hδ] at hlip
      rw [abs_le] at hlip
      linarith [hlip.2]
    linarith [mul_nonneg hL hδ]

/-! ## 10. Combined Cross-Model Transferability Theorem -/

/--
**Theorem 7: Cross-Model Injection Transferability (Combined Statement).**

Given two alignment-deviation functions `f` and `g` with `‖f − g‖_∞ ≤ δ`:

  (a) Any injection achieving `f(p) > τ + δ` also achieves `g(p) > τ`.
  (b) `{f > τ + δ} ⊆ {g > τ}` (superlevel containment).
  (c) `{g > τ + δ} ⊆ {f > τ}` (symmetric containment).
  (d) The vulnerability basins are sandwiched:
        `{g > τ + δ} ⊆ {f > τ} ⊆ {g > τ − δ}`.

This explains why prompt injections transfer between models with similar
alignment-deviation surfaces.
-/
theorem cross_model_transferability
    {X : Type*} {f g : X → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (τ : ℝ) :
    -- (a) Pointwise transferability
    (∀ p, f p > τ + δ → g p > τ) ∧
    -- (b) Superlevel containment f → g
    ({x | f x > τ + δ} ⊆ {x | g x > τ}) ∧
    -- (c) Superlevel containment g → f (symmetric)
    ({x | g x > τ + δ} ⊆ {x | f x > τ}) ∧
    -- (d) Coverage sandwich
    ({x | g x > τ + δ} ⊆ {x | f x > τ}) ∧
    ({x | f x > τ} ⊆ {x | g x > τ - δ}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) pointwise
    intro p hp
    exact transferability_pointwise h_close hp
  · -- (b) superlevel containment
    exact superlevel_subset_of_close h_close τ
  · -- (c) symmetric containment
    exact superlevel_subset_of_close_symm h_close τ
  · -- (d) sandwich
    exact coverage_sandwich hδ h_close τ

/--
**Corollary: Identical models have identical vulnerability basins.**
-/
theorem identical_models_identical_basins
    {X : Type*} {f g : X → ℝ}
    (h_eq : ∀ x, f x = g x)
    (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} :=
  superlevel_eq_of_eq h_eq τ

end
