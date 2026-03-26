import Mathlib

/-!
# Manifold of Failure — Cost Layer 4: Concentration Inequality Foundations

We prove deterministic foundations for concentration inequalities relevant to
sup-norm estimation. These results underpin the statistical guarantees needed
when estimating alignment deviation (AD) functions from finite samples.

## Main results

- `sup_norm_triangle` — triangle inequality for pointwise sup-norm bounds
- `sup_norm_symm` — symmetry of pointwise sup-norm bounds
- `estimation_error_bound_unsafe` — truly unsafe points via estimation margin
- `estimation_error_bound_safe` — truly safe points via estimation margin
- `estimation_uncertain_band` — characterisation of the uncertain band
- `estimation_band_shrinks` — monotonicity: smaller ε ⇒ smaller uncertain band
- `n_samples_coverage` — Lipschitz interpolation bound from nearest sample
-/

open Set

noncomputable section

namespace MoF

variable {X : Type*}

/-! ## 1. Sup-norm triangle inequality -/

/--
Triangle inequality for pointwise sup-norm bounds.
If `|f x - g x| ≤ δ₁` and `|g x - h x| ≤ δ₂` for all x,
then `|f x - h x| ≤ δ₁ + δ₂` for all x.
-/
theorem sup_norm_triangle
    {f g h : X → ℝ} {δ₁ δ₂ : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ δ₁)
    (hgh : ∀ x, |g x - h x| ≤ δ₂) :
    ∀ x, |f x - h x| ≤ δ₁ + δ₂ := by
  intro x
  have key : f x - h x = (f x - g x) + (g x - h x) := by ring
  rw [key]
  exact le_trans (abs_add_le _ _) (add_le_add (hfg x) (hgh x))

/-! ## 2. Sup-norm symmetry -/

/--
If `|f x - g x| ≤ δ` for all x, then `|g x - f x| ≤ δ` for all x.
-/
theorem sup_norm_symm
    {f g : X → ℝ} {δ : ℝ}
    (h : ∀ x, |f x - g x| ≤ δ) :
    ∀ x, |g x - f x| ≤ δ := by
  intro x
  rw [abs_sub_comm]
  exact h x

/-! ## 3. Estimation error bounds for classification -/

/--
If f̂ estimates f with pointwise error ≤ ε, and f̂ x > τ + ε, then f x > τ.
Any point classified as unsafe with sufficient margin is truly unsafe.
-/
theorem estimation_error_bound_unsafe
    {f_hat f : X → ℝ} {ε : ℝ}
    (h_est : ∀ x, |f_hat x - f x| ≤ ε)
    {x : X} {τ : ℝ}
    (h_unsafe : f_hat x > τ + ε) :
    f x > τ := by
  have h1 := abs_le.mp (h_est x)
  linarith

/--
If f̂ estimates f with pointwise error ≤ ε, and f̂ x < τ - ε, then f x < τ.
Any point classified as safe with sufficient margin is truly safe.
-/
theorem estimation_error_bound_safe
    {f_hat f : X → ℝ} {ε : ℝ}
    (h_est : ∀ x, |f_hat x - f x| ≤ ε)
    {x : X} {τ : ℝ}
    (h_safe : f_hat x < τ - ε) :
    f x < τ := by
  have h1 := abs_le.mp (h_est x)
  linarith

/--
Combined estimation error bound: both safe and unsafe directions.
-/
theorem estimation_error_bound
    {f_hat f : X → ℝ} {ε : ℝ}
    (h_est : ∀ x, |f_hat x - f x| ≤ ε)
    {x : X} {τ : ℝ} :
    (f_hat x > τ + ε → f x > τ) ∧ (f_hat x < τ - ε → f x < τ) :=
  ⟨fun h => estimation_error_bound_unsafe h_est h,
   fun h => estimation_error_bound_safe h_est h⟩

/-! ## 4. Uncertain band characterisation -/

/--
Points in the uncertain band: if `|f̂ x - τ| ≤ ε`, then we cannot reliably
determine whether `f x > τ` or `f x < τ`. The uncertain band is equivalently
described as `{x | τ - ε ≤ f̂ x ∧ f̂ x ≤ τ + ε}`.
-/
theorem estimation_uncertain_band
    {f_hat : X → ℝ} {τ ε : ℝ} :
    {x | |f_hat x - τ| ≤ ε} = {x | τ - ε ≤ f_hat x ∧ f_hat x ≤ τ + ε} := by
  ext x
  simp only [mem_setOf_eq, abs_le]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · intro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-! ## 5. Band monotonicity -/

/--
As ε shrinks, the uncertain band shrinks: if ε₁ ≤ ε₂ then
`{x | |f̂ x - τ| ≤ ε₁} ⊆ {x | |f̂ x - τ| ≤ ε₂}`.
-/
theorem estimation_band_shrinks
    {f_hat : X → ℝ} {τ ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) :
    {x | |f_hat x - τ| ≤ ε₁} ⊆ {x | |f_hat x - τ| ≤ ε₂} := by
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact le_trans hx hε

/-! ## 6. Lipschitz interpolation from nearest sample -/

/--
For a Lipschitz function f with constant L, if we know f at a sample point xᵢ
and the distance from x to xᵢ is d, then `|f x - f xᵢ| ≤ L * d`.
This is the fundamental bound on how well finitely many samples approximate f.
-/
theorem n_samples_coverage
    [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h_lip : ∀ a b : X, |f a - f b| ≤ L * dist a b)
    {x xᵢ : X} {d : ℝ}
    (h_dist : dist x xᵢ ≤ d) :
    |f x - f xᵢ| ≤ L * d := by
  calc |f x - f xᵢ| ≤ L * dist x xᵢ := h_lip x xᵢ
    _ ≤ L * d := by exact mul_le_mul_of_nonneg_left h_dist hL

/--
Corollary: for a list of sample points, the estimation error is bounded by
L times the minimum distance to any sample. We state this for two sample
points; the generalisation follows by induction.
-/
theorem n_samples_coverage_min
    [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h_lip : ∀ a b : X, |f a - f b| ≤ L * dist a b)
    {x x₁ x₂ : X} {d₁ d₂ : ℝ}
    (hd₁ : dist x x₁ ≤ d₁)
    (hd₂ : dist x x₂ ≤ d₂) :
    (|f x - f x₁| ≤ L * d₁) ∧ (|f x - f x₂| ≤ L * d₂) :=
  ⟨n_samples_coverage hL h_lip hd₁, n_samples_coverage hL h_lip hd₂⟩

end MoF
