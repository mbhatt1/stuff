import Mathlib
import ManifoldProofs.MoF_01_Foundations

/-
  MoF_03_ThresholdCrossing.lean

  Part 3 of the "Manifold of Failure" formalization for LLM safety.

  **Core result: The defense boundary is unavoidable.**

  All theorems are fully N-dimensional, parameterized over an arbitrary
  topological space X with a continuous function f : X → ℝ.

  We prove:

    1. `path_crosses_threshold` — IVT on ℝ: continuous f with f(a) < τ < f(b)
       implies ∃ c ∈ [a,b], f(c) = τ.
    1b. `path_crosses_threshold_generic` — N-dimensional version: if
        γ : ℝ → X is continuous, f : X → ℝ is continuous, and
        f(γ(a)) < τ < f(γ(b)), then ∃ c ∈ [a,b], f(γ(c)) = τ.
    2. `threshold_level_set_nonempty` — on a connected space, if f takes values
       above and below τ then {f = τ} ≠ ∅.
    3. `threshold_level_set_closed` — {x | f x = τ} is closed for continuous f.
    4. `safe_unsafe_separated` — the closures of the safe and unsafe regions
       intersect only on the boundary level set.
    5. `no_gap_theorem` — for f : X → ℝ continuous on a connected space X,
       if both safe and unsafe points exist, {f = τ} is nonempty.

  Definitions of SafeRegion, UnsafeRegion, Boundary are imported from
  MoF_01_Foundations.
-/

noncomputable section

open Set Topology

namespace MoF

/-! ## 1. Path Crosses Threshold (IVT on ℝ) -/

/--
If `f : ℝ → ℝ` is continuous, `f a < τ`, `f b > τ`, and `a ≤ b`, then
there exists `c ∈ [a, b]` with `f c = τ`.
-/
theorem path_crosses_threshold
    (f : ℝ → ℝ) (hf : Continuous f) (a b τ : ℝ)
    (hab : a ≤ b) (ha : f a < τ) (hb : f b > τ) :
    ∃ c ∈ Set.Icc a b, f c = τ := by
  have h_conn : IsPreconnected (Set.Icc a b) := isPreconnected_Icc
  have ha_mem : a ∈ Set.Icc a b := left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := right_mem_Icc.mpr hab
  obtain ⟨c, hc_mem, hc_eq⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hf.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc_mem, hc_eq⟩

/-! ## 1b. Path Crosses Threshold — Generic (N-dimensional) -/

/--
**Generic IVT along a path.** Let `X` be any topological space,
`γ : ℝ → X` a continuous path, and `f : X → ℝ` a continuous function.
If `f(γ(a)) < τ < f(γ(b))` and `a ≤ b`, then there exists `c ∈ [a, b]`
with `f(γ(c)) = τ`.

This is the IVT applied to the composite `f ∘ γ : ℝ → ℝ`.
-/
theorem path_crosses_threshold_generic
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f)
    (γ : ℝ → X) (hγ : Continuous γ)
    (a b τ : ℝ) (hab : a ≤ b)
    (ha : f (γ a) < τ) (hb : f (γ b) > τ) :
    ∃ c ∈ Set.Icc a b, f (γ c) = τ :=
  path_crosses_threshold (f ∘ γ) (hf.comp hγ) a b τ hab ha hb

/-! ## 2. Threshold Level Set Nonempty -/

/--
On a connected topological space, if a continuous function takes values both
above and below τ, then the boundary level set {f = τ} is nonempty.
-/
theorem threshold_level_set_nonempty
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (a b : X) (ha : f a < τ) (hb : f b > τ) :
    (Boundary f τ).Nonempty := by
  have h_conn : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
  have ha_mem : a ∈ (Set.univ : Set X) := Set.mem_univ _
  have hb_mem : b ∈ (Set.univ : Set X) := Set.mem_univ _
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ ha_mem hb_mem
    hf.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc⟩

/-! ## 3. Threshold Level Set is Closed -/

/--
The level set {x | f x = τ} is closed for any continuous f.
-/
theorem threshold_level_set_closed
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsClosed (Boundary f τ) :=
  boundary_isClosed hf τ

/-! ## 4. Safe and Unsafe Regions Separated by Level Set -/

/-- The safe region is open for continuous f. -/
theorem safe_region_isOpen
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsOpen (SafeRegion f τ) :=
  safeRegion_isOpen hf τ

/-- The unsafe region is open for continuous f. -/
theorem unsafe_region_isOpen
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsOpen (UnsafeRegion f τ) :=
  unsafeRegion_isOpen hf τ

/--
The closures of the safe and unsafe regions intersect only within the
boundary level set. That is,
  closure(SafeRegion) ∩ closure(UnsafeRegion) ⊆ Boundary.
-/
theorem safe_unsafe_separated
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    closure (SafeRegion f τ) ∩ closure (UnsafeRegion f τ) ⊆ Boundary f τ := by
  intro x ⟨hx_safe, hx_unsafe⟩
  -- x is in the closure of {f < τ}, so f x ≤ τ
  have h_le : f x ≤ τ := by
    by_contra h
    push_neg at h
    have hopen : IsOpen (UnsafeRegion f τ) := unsafeRegion_isOpen hf τ
    have hx_in : x ∈ UnsafeRegion f τ := h
    rw [mem_closure_iff] at hx_safe
    obtain ⟨y, hy_unsafe, hy_safe⟩ := hx_safe _ hopen hx_in
    simp only [SafeRegion, UnsafeRegion, Set.mem_setOf_eq] at hy_safe hy_unsafe
    linarith
  -- x is in the closure of {f > τ}, so f x ≥ τ
  have h_ge : f x ≥ τ := by
    by_contra h
    push_neg at h
    have hopen : IsOpen (SafeRegion f τ) := safeRegion_isOpen hf τ
    have hx_in : x ∈ SafeRegion f τ := h
    rw [mem_closure_iff] at hx_unsafe
    obtain ⟨y, hy_safe, hy_unsafe⟩ := hx_unsafe _ hopen hx_in
    simp only [SafeRegion, UnsafeRegion, Set.mem_setOf_eq] at hy_safe hy_unsafe
    linarith
  -- f x ≤ τ and f x ≥ τ imply f x = τ
  exact le_antisymm h_le h_ge

/-! ## 5. No Gap Theorem — Generic Connected Space -/

/--
**No Gap Theorem (N-dimensional).** For any connected topological space `X`
and continuous `f : X → ℝ`, if there exist both safe points (f < τ) and
unsafe points (f > τ), then the boundary level set {f = τ} is nonempty.

This generalizes the original ℝ × ℝ version to arbitrary connected spaces.
-/
theorem no_gap_theorem
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (a b : X) (ha : f a < τ) (hb : f b > τ) :
    (Boundary f τ).Nonempty :=
  threshold_level_set_nonempty f hf τ a b ha hb

/-! ## Summary

| # | Statement | Status |
|---|-----------|--------|
| 1 | `path_crosses_threshold` (IVT on ℝ) | Proved |
| 1b| `path_crosses_threshold_generic` (IVT along path in X) | Proved |
| 2 | `threshold_level_set_nonempty` (connected space X) | Proved |
| 3 | `threshold_level_set_closed` (any topological space X) | Proved |
| 4 | `safe_unsafe_separated` (closures meet on boundary, any X) | Proved |
| 5 | `no_gap_theorem` (connected space X, no defense gap) | Proved |

All results are sorry-free and fully N-dimensional.
-/

end MoF
