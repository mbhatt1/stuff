import Mathlib

/-!
# Manifold of Failure — Advanced 4: Model Scale and Manifold Complexity

We study how function-class complexity (a proxy for model scale / parameter count)
affects the structure of superlevel sets {f > τ} ("basins" in the MoF framework).

## Main results

1. `constant_model_no_basin_empty/univ` — A constant model's basin is either empty or everything.
2. `lipschitz_basin_component_width` — Each connected component of {f > τ} for an
   L-Lipschitz function contains an interval of width 2(f(x)-τ)/L around any peak x.
3. `smoother_functions_larger_basins` — Smaller Lipschitz constant ⟹ larger robustness
   radius per peak.
4. `low_complexity_few_crossings_1d` — Monotone functions cross any threshold at most once.
5. `higher_lipschitz_more_oscillation` — On [0,1], if f(0)=f(1)=0 and max f = M,
   then L ≥ 2M.
-/

open Set

noncomputable section

namespace MoF

/-! ## 1. Constant model: basin is trivial -/

/-- If f is constant at value c ≤ τ, the superlevel set {f > τ} is empty. -/
theorem constant_model_no_basin_empty {X : Type*} {f : X → ℝ} {c τ : ℝ}
    (hf : ∀ x, f x = c) (hle : c ≤ τ) :
    {x | f x > τ} = (∅ : Set X) := by
  ext x
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
  rw [hf x]
  exact hle

/-- If f is constant at value c > τ, the superlevel set {f > τ} is the whole space. -/
theorem constant_model_no_basin_univ {X : Type*} {f : X → ℝ} {c τ : ℝ}
    (hf : ∀ x, f x = c) (hgt : c > τ) :
    {x | f x > τ} = (univ : Set X) := by
  ext x
  simp only [mem_setOf_eq, mem_univ, iff_true]
  rw [hf x]
  exact hgt

/-! ## 2. Lipschitz basin component width -/

/-- If f : ℝ → ℝ is L-Lipschitz with L > 0 and f(x) > τ, then for any y with
    |y - x| < (f(x) - τ)/L, we have f(y) > τ. This means the connected component
    of x in {f > τ} contains the open interval (x - (f(x)-τ)/L, x + (f(x)-τ)/L). -/
theorem lipschitz_basin_component_width
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b|)
    {x : ℝ} {τ : ℝ}
    (_hx : f x > τ) :
    ∀ y, |y - x| < (f x - τ) / L → f y > τ := by
  intro y hy
  have hLip := hf x y
  have h1 : L * |x - y| < f x - τ := by
    rw [abs_sub_comm] at hy
    calc L * |x - y| ≤ L * |y - x| := by rw [abs_sub_comm]
    _ < L * ((f x - τ) / L) := by
        exact mul_lt_mul_of_pos_left (by rwa [abs_sub_comm]) hL
    _ = f x - τ := by field_simp
  have h2 : f x - f y ≤ |f x - f y| := le_abs_self _
  linarith

/-! ## 3. Smoother functions have larger basins -/

/-- The robustness radius: (f(p) - τ) / L. -/
def robustnessRadius' (fp τ : ℝ) (L : ℝ) : ℝ := (fp - τ) / L

/-- If L₁ ≤ L₂ (both positive) and f(p) = g(p) > τ, then the robustness radius
    for the L₁-Lipschitz function is ≥ that for the L₂-Lipschitz function.
    Smoother (smaller Lipschitz constant) ⟹ larger basin per peak. -/
theorem smoother_functions_larger_basins
    {fp τ L₁ L₂ : ℝ}
    (hL₁ : 0 < L₁)
    (hfp : fp > τ)
    (hL : L₁ ≤ L₂) :
    robustnessRadius' fp τ L₁ ≥ robustnessRadius' fp τ L₂ := by
  unfold robustnessRadius'
  apply div_le_div_of_nonneg_left (by linarith) hL₁ hL

/-! ## 4. Monotone functions cross a threshold at most once -/

/-- For a monotone function f : ℝ → ℝ, if f(a) = τ and f(b) = τ with a ≤ b,
    then f is constantly τ on [a, b]. This means a monotone function has at most
    one "crossing" of any threshold level. -/
theorem low_complexity_few_crossings_1d
    {f : ℝ → ℝ} (hf : Monotone f)
    {a b τ : ℝ}
    (hfa : f a = τ) (hfb : f b = τ) :
    ∀ x, a ≤ x → x ≤ b → f x = τ := by
  intro x hax hxb
  have h1 : f a ≤ f x := hf hax
  have h2 : f x ≤ f b := hf hxb
  rw [hfa] at h1
  rw [hfb] at h2
  linarith

/-! ## 5. Higher Lipschitz constant needed for more oscillation -/

/-- On [0,1], if f(0) = 0, f(1) = 0, and f achieves value M > 0 at some point t ∈ [0,1],
    then the Lipschitz constant L satisfies L ≥ 2M.

    Proof: M = |f(t) - f(0)| ≤ L·t and M = |f(t) - f(1)| ≤ L·(1-t).
    Adding: 2M ≤ L·t + L·(1-t) = L. -/
theorem higher_lipschitz_more_oscillation
    {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b|)
    {t : ℝ} {M : ℝ}
    (hM : 0 < M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hf0 : f 0 = 0) (hf1 : f 1 = 0)
    (hft : f t = M) :
    2 * M ≤ L := by
  have h1 := hf 0 t
  have h2 := hf t 1
  rw [hf0, hft] at h1
  rw [hft, hf1] at h2
  -- |0 - M| = M
  rw [zero_sub, abs_neg, abs_of_pos hM] at h1
  -- |0 - t| = t
  rw [zero_sub, abs_neg, abs_of_nonneg ht0] at h1
  -- |M - 0| = M
  rw [sub_zero, abs_of_pos hM] at h2
  -- |t - 1| = 1 - t
  rw [show t - 1 = -(1 - t) from by ring, abs_neg, abs_of_nonneg (by linarith)] at h2
  linarith

end MoF
