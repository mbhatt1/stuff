import Mathlib

/-!
# Manifold of Failure — Advanced 3: Fine-Tuning & Patching Effects

We model fine-tuning/patching as perturbation: an AD function `f` changes to
`g = f + δh` for some perturbation `h`.  The key question is:
**how fast does patching one region affect others?**

Given two AD functions `f g : X → ℝ` satisfying `∀ x, |f x - g x| ≤ ε`
(sup-norm distance at most ε), we prove:

## Main results

- `basin_hausdorff_distance_bound` — symmetric difference of basins
  `{f > τ} △ {g > τ}` is contained in the ε-band `{x | |f x - τ| ≤ ε}`
- `small_perturbation_preserves_interior` — points deep inside the failure
  basin (f x > τ + ε) survive perturbation
- `small_perturbation_preserves_safe_interior` — points deep inside the safe
  region (f x < τ - ε) survive perturbation
- `boundary_shift_bound` — boundary of g lies within the ε-band of boundary of f
- `patching_nonlocal` — perturbation affects boundaries globally (existence witness)
-/

open Set

noncomputable section

namespace MoF

variable {X : Type*} {f g : X → ℝ} {ε : ℝ}

/-! ## 1. Basin Symmetric-Difference Bound -/

/--
If ‖f - g‖∞ ≤ ε, the symmetric difference of basins {f > τ} △ {g > τ} is
contained in the ε-band {x | |f x - τ| ≤ ε}.

Proof sketch: if x is in the symmetric difference, then one of f(x) > τ,
g(x) ≤ τ (or vice versa). Combined with |f(x) - g(x)| ≤ ε this forces
|f(x) - τ| ≤ ε.
-/
theorem basin_hausdorff_distance_bound
    (h_close : ∀ x, |f x - g x| ≤ ε)
    (_hε : 0 ≤ ε)
    (τ : ℝ) :
    ({x | f x > τ} \ {x | g x > τ}) ∪ ({x | g x > τ} \ {x | f x > τ}) ⊆
      {x | |f x - τ| ≤ ε} := by
  intro x hx
  simp only [mem_union, mem_diff, mem_setOf_eq] at hx
  simp only [mem_setOf_eq]
  have hfg : |f x - g x| ≤ ε := h_close x
  have hfg' := abs_le.mp hfg
  rw [abs_le]
  rcases hx with ⟨hfx, hgx⟩ | ⟨hgx, hfx⟩
  · -- f x > τ but g x ≤ τ
    push_neg at hgx
    constructor <;> linarith
  · -- g x > τ but f x ≤ τ
    push_neg at hfx
    constructor <;> linarith

/-! ## 2. Interior Preservation Under Perturbation -/

/--
Points deep inside the failure basin survive perturbation:
if `f x > τ + ε` and `‖f - g‖∞ ≤ ε`, then `g x > τ`.
-/
theorem small_perturbation_preserves_interior
    (h_close : ∀ x, |f x - g x| ≤ ε)
    {x : X} {τ : ℝ}
    (h_deep : f x > τ + ε) :
    g x > τ := by
  have h1 : |f x - g x| ≤ ε := h_close x
  have h2 := abs_le.mp h1
  linarith

/-! ## 3. Safe Interior Preservation -/

/--
Points deep inside the safe region survive perturbation:
if `f x < τ - ε` and `‖f - g‖∞ ≤ ε`, then `g x < τ`.
-/
theorem small_perturbation_preserves_safe_interior
    (h_close : ∀ x, |f x - g x| ≤ ε)
    {x : X} {τ : ℝ}
    (h_safe : f x < τ - ε) :
    g x < τ := by
  have h1 : |f x - g x| ≤ ε := h_close x
  have h2 := abs_le.mp h1
  linarith

/-! ## 4. Boundary Shift Bound -/

/--
If `g z = τ` and `‖f - g‖∞ ≤ ε`, then `|f z - τ| ≤ ε`.
In other words, boundaries of g lie within the ε-band of boundaries of f.
-/
theorem boundary_shift_bound
    (h_close : ∀ x, |f x - g x| ≤ ε)
    {z : X} {τ : ℝ}
    (h_bdy : g z = τ) :
    |f z - τ| ≤ ε := by
  have h1 : |f z - g z| ≤ ε := h_close z
  rw [h_bdy] at h1
  exact h1

/--
Corollary: boundary points of g are near-boundary points of f.
Specifically f(z) ∈ [τ - ε, τ + ε].
-/
theorem boundary_shift_interval
    (h_close : ∀ x, |f x - g x| ≤ ε)
    {z : X} {τ : ℝ}
    (h_bdy : g z = τ) :
    τ - ε ≤ f z ∧ f z ≤ τ + ε := by
  have h1 := boundary_shift_bound h_close h_bdy
  have h2 := abs_le.mp h1
  constructor <;> linarith

/-! ## 5. Patching Is Nonlocal -/

/--
Patching is inherently nonlocal: even a small perturbation (‖f-g‖∞ ≤ ε)
can shift the boundary everywhere. We witness this concretely on `ℝ`:
take `f = id`, `g = id + ε/2`. Then `f(τ) = τ` (boundary point for f) but
`g(τ) = τ + ε/2 > τ` (not a boundary point for g), showing boundaries
don't agree.

We prove the concrete witness: there exist f, g : ℝ → ℝ with
‖f - g‖∞ ≤ ε (for ε > 0) and a point where f is on the boundary
but g is strictly above it.
-/
theorem patching_nonlocal (hε : (0 : ℝ) < ε) :
    ∃ (f g : ℝ → ℝ),
      (∀ x, |f x - g x| ≤ ε) ∧
      ∃ (τ : ℝ) (z : ℝ), f z = τ ∧ g z > τ := by
  refine ⟨id, fun x => x + ε / 2, ?_, ?_⟩
  · intro x
    simp only [id]
    have : x - (x + ε / 2) = -(ε / 2) := by ring
    rw [this, abs_neg, abs_of_pos (half_pos hε)]
    linarith
  · refine ⟨0, 0, ?_, ?_⟩
    · simp [id]
    · simp
      linarith

/-! ## 6. Supplementary: Perturbation Monotonicity -/

/--
If perturbation is pointwise non-negative (g ≥ f everywhere), then
the failure basin can only grow: {f > τ} ⊆ {g > τ}.
-/
theorem monotone_perturbation_basin_grows
    (h_pos : ∀ x, f x ≤ g x) (τ : ℝ) :
    {x | f x > τ} ⊆ {x | g x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact lt_of_lt_of_le hx (h_pos x)

/--
Dually, if perturbation is pointwise non-positive (g ≤ f), the safe region
can only grow: {f < τ} ⊆ {g < τ} is NOT true; rather {g < τ} ⊇ ... we
actually get {f > τ} ⊇ {g > τ}, i.e. the failure basin shrinks.
-/
theorem monotone_negative_perturbation_basin_shrinks
    (h_neg : ∀ x, g x ≤ f x) (τ : ℝ) :
    {x | g x > τ} ⊆ {x | f x > τ} := by
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  exact lt_of_lt_of_le hx (h_neg x)

/--
The ε-band thickness bounds the "uncertainty zone" — points where we
cannot determine basin membership from f alone after perturbation.
If |f(x) - τ| > ε, then f and g agree on whether x is in the basin.
-/
theorem outside_band_basin_agreement
    (h_close : ∀ x, |f x - g x| ≤ ε)
    {x : X} {τ : ℝ}
    (h_outside : |f x - τ| > ε) :
    (f x > τ ↔ g x > τ) := by
  have hfg : |f x - g x| ≤ ε := h_close x
  have hfg' := abs_le.mp hfg
  cases lt_or_ge (f x) τ with
  | inl hlt =>
    -- f x < τ, and |f x - τ| > ε means τ - f x > ε, i.e. f x < τ - ε
    have : f x - τ < 0 := by linarith
    have : |f x - τ| = τ - f x := by
      rw [abs_of_neg this]
      ring
    rw [this] at h_outside
    constructor
    · intro hfx; linarith
    · intro hgx; linarith
  | inr hge =>
    -- f x ≥ τ, and |f x - τ| > ε means f x - τ > ε, i.e. f x > τ + ε
    have : |f x - τ| = f x - τ := abs_of_nonneg (by linarith)
    rw [this] at h_outside
    constructor
    · intro _; linarith
    · intro _; linarith

end MoF
