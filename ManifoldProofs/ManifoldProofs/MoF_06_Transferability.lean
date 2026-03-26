import Mathlib

/-!
# Manifold of Failure — Part 6: Cross-Model Attack Transferability

We prove that models with close Alignment Deviation (AD) surfaces have
overlapping vulnerability basins, establishing rigorous bounds on
cross-model attack transferability.

Given two AD functions `f g : X → ℝ` satisfying `∀ x, |f x - g x| ≤ δ`
(i.e., sup-norm distance at most δ), we show:

## Main results

- `transfer_attack` — if `f p > τ + δ` then `g p > τ`
- `transfer_attack_symm` — symmetric: if `g p > τ + δ` then `f p > τ`
- `basin_containment` — `{x | f x > τ + δ} ⊆ {x | g x > τ}`
- `basin_containment_symm` — `{x | g x > τ + δ} ⊆ {x | f x > τ}`
- `identical_models_identical_basins` — if δ = 0, basins are equal
- `pointwise_sandwich` — `f x - δ ≤ g x ∧ g x ≤ f x + δ`
-/

open Set

noncomputable section

namespace MoF

variable {X : Type*} {f g : X → ℝ} {δ : ℝ}

/-! ## 1. Core Transferability -/

/--
If two AD functions are within δ in sup-norm and `f p > τ + δ`, then `g p > τ`.
From `|f p - g p| ≤ δ` we extract `f p - g p ≤ δ`, giving `g p ≥ f p - δ > τ`.
-/
theorem transfer_attack
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : f p > τ + δ) :
    g p > τ := by
  have h1 : |f p - g p| ≤ δ := h_close p
  have h2 := abs_le.mp h1
  linarith

/--
Symmetric transferability: if `g p > τ + δ`, then `f p > τ`.
-/
theorem transfer_attack_symm
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : g p > τ + δ) :
    f p > τ := by
  have h1 : |f p - g p| ≤ δ := h_close p
  have h2 := abs_le.mp h1
  linarith

/-! ## 2. Basin Containment -/

/--
The superlevel set of `f` at level `τ + δ` is contained in
the superlevel set of `g` at level `τ`.
-/
theorem basin_containment
    (h_close : ∀ x, |f x - g x| ≤ δ) (τ : ℝ) :
    {x | f x > τ + δ} ⊆ {x | g x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact transfer_attack h_close hx

/--
Symmetric basin containment.
-/
theorem basin_containment_symm
    (h_close : ∀ x, |f x - g x| ≤ δ) (τ : ℝ) :
    {x | g x > τ + δ} ⊆ {x | f x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact transfer_attack_symm h_close hx

/-! ## 3. Identical Models -/

/--
When δ = 0 the two AD functions agree pointwise, so their
vulnerability basins at any threshold τ are identical.
-/
theorem identical_models_identical_basins
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (hδ : δ = 0) (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} := by
  ext x
  simp only [mem_setOf_eq]
  have h1 : |f x - g x| ≤ 0 := by rw [← hδ]; exact h_close x
  have h2 : f x = g x := by
    have h3 : f x - g x = 0 := by
      have h4 := abs_nonneg (f x - g x)
      have h5 : |f x - g x| = 0 := le_antisymm h1 h4
      exact abs_eq_zero.mp h5
    linarith
  rw [h2]

/-! ## 4. Pointwise Sandwich -/

/--
The closeness hypothesis yields a two-sided sandwich:
`f x - δ ≤ g x` and `g x ≤ f x + δ`.
-/
theorem pointwise_sandwich
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (x : X) :
    f x - δ ≤ g x ∧ g x ≤ f x + δ := by
  have h1 : |f x - g x| ≤ δ := h_close x
  have h2 := abs_le.mp h1
  constructor <;> linarith

end MoF
