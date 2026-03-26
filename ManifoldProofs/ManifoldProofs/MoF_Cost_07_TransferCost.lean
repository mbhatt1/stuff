/-
  MoF Cost 07: Transfer Cost Model
  =================================
  Formalizes the cost of porting attacks between models.

  Given two AD functions `f g : X → ℝ` with `∀ x, |f x - g x| ≤ δ`,
  we prove:
  1. An attack needs margin > δ above threshold to transfer.
  2. Transfer itself is a pure logical deduction (zero additional queries).
  3. The empirical sup-norm from n samples lower-bounds the true sup-norm.
  4. More samples yield a tighter (larger) lower bound.
  5. If δ = 0, transfer is perfect and free.
-/

import Mathlib

open Set Finset

namespace MoF

variable {X : Type*}

/-! ## 1. Transfer margin needed -/

/--
If models differ by at most δ in sup-norm and `f p > τ + δ`, then `g p > τ`.
An attack needs margin > δ above threshold to transfer.
Self-contained version of MoF_06's `transfer_attack`.
-/
theorem transfer_margin_needed
    {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : f p > τ + δ) :
    g p > τ := by
  have h1 : |f p - g p| ≤ δ := h_close p
  have h2 := abs_le.mp h1
  linarith

/-! ## 2. Transfer is free (zero additional queries) -/

/--
The transfer function: given a proof that `f p > τ + δ` and that models are
δ-close, produce a proof that `g p > τ`. This is a pure logical deduction
that requires no additional evaluation of `g` — zero queries on the target.
-/
def transfer_attack_free
    {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : f p > τ + δ) :
    g p > τ :=
  transfer_margin_needed h_close h_above

/--
Transfer is free: the transfer function is definitionally equal to the margin
theorem — it requires zero additional evaluations of the target model g.
This theorem witnesses that `transfer_attack_free` is just a wrapper around
a pure logical deduction.
-/
theorem transfer_is_free
    {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    {p : X} {τ : ℝ}
    (h_above : f p > τ + δ) :
    transfer_attack_free h_close h_above = transfer_margin_needed h_close h_above :=
  rfl

/-! ## 3. Estimation cost: empirical δ̂ ≤ true δ -/

/--
If the true sup-norm satisfies `|f(xᵢ) - g(xᵢ)| ≤ δ` for all sample points,
then the empirical maximum (over a finite nonempty sample set S) also satisfies
`δ̂ ≤ δ`. The sampled max can only underestimate the true sup-norm.
-/
theorem estimation_cost
    {ι : Type*} [DecidableEq ι]
    {f g : ι → ℝ} {δ : ℝ}
    (h_bound : ∀ i, |f i - g i| ≤ δ)
    (S : Finset ι) (hS : S.Nonempty) :
    S.sup' hS (fun i => |f i - g i|) ≤ δ := by
  apply Finset.sup'_le
  intro i _
  exact h_bound i

/-! ## 4. More samples give a tighter estimate -/

/--
If S₁ ⊆ S₂ (more samples), then the empirical max over S₁ is at most that
over S₂. More samples yield a tighter (larger) lower bound on the true δ.
-/
theorem more_samples_better_estimate
    {ι : Type*} [DecidableEq ι]
    {f g : ι → ℝ}
    {S₁ S₂ : Finset ι}
    (h_sub : S₁ ⊆ S₂)
    (hS₁ : S₁.Nonempty) :
    S₁.sup' hS₁ (fun i => |f i - g i|) ≤
      S₂.sup' (Finset.Nonempty.mono h_sub hS₁) (fun i => |f i - g i|) := by
  exact Finset.sup'_mono _ h_sub hS₁

/-! ## 5. Zero distance means free transfer -/

/--
If δ = 0, models agree pointwise, so their superlevel sets are identical.
Transfer is perfect with zero estimation cost.
-/
theorem zero_distance_free_transfer
    {f g : X → ℝ} {δ : ℝ}
    (h_close : ∀ x, |f x - g x| ≤ δ)
    (hδ : δ = 0) (τ : ℝ) :
    {x | f x > τ} = {x | g x > τ} := by
  ext x
  simp only [mem_setOf_eq]
  have h1 : |f x - g x| ≤ 0 := hδ ▸ h_close x
  have h2 : f x = g x := by
    have := abs_nonneg (f x - g x)
    have h3 : |f x - g x| = 0 := le_antisymm h1 this
    linarith [abs_eq_zero.mp h3]
  rw [h2]

end MoF
