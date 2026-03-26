import Mathlib

/-!
# Manifold of Failure — Master Theorem

This capstone file combines the key results of the Manifold of Failure theory
into a single structure and a single master theorem, all in full N-dimensional
generality over an arbitrary topological space `X`.

The `ManifoldOfFailure` structure bundles a behavioral space with its
topological, metric, and analytic data. The `master_theorem` then proves
three fundamental properties:

1. **Basin openness**: The vulnerability basin `{x | f x > τ}` is open.
2. **Boundary nonemptiness**: The level set `{x | f x = τ}` is nonempty
   (via connectedness and the intermediate value theorem).
3. **Defense impossibility**: Any continuous, utility-preserving defense
   `D : X → X` necessarily fixes some boundary point, and therefore cannot
   push all points into the safe region.

Each part is proved from first principles using Mathlib, inlining the
needed sub-lemmas from the MoF series (MoF_02, MoF_03, MoF_08).
-/

open Set Topology Filter

noncomputable section

namespace MoF

/-- The Manifold of Failure: a connected Hausdorff behavioral space equipped
with a continuous alignment deviation function that witnesses both safe and
unsafe behaviors. -/
structure ManifoldOfFailure where
  /-- The behavioral space -/
  X : Type*
  /-- Topological structure -/
  top : TopologicalSpace X
  /-- Hausdorff -/
  t2 : T2Space X
  /-- Connected -/
  conn : ConnectedSpace X
  /-- Metric structure -/
  metric : PseudoMetricSpace X
  /-- Alignment deviation function -/
  f : X → ℝ
  /-- Continuity -/
  hf : Continuous f
  /-- Safety threshold -/
  τ : ℝ
  /-- Safe point exists -/
  safe_exists : ∃ a, f a < τ
  /-- Unsafe point exists -/
  unsafe_exists : ∃ b, f b > τ

/-! ## Sub-lemmas (self-contained, no imports from other MoF files) -/

/-- The superlevel set `{x | f x > τ}` is open for continuous `f`. -/
private theorem basin_open {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsOpen {x | f x > τ} :=
  isOpen_lt continuous_const hf

/-- On a connected space, if `f` takes values both below and above `τ`,
then `{x | f x = τ}` is nonempty. This is the intermediate value theorem
applied via `isPreconnected_univ.intermediate_value₂`. -/
private theorem boundary_nonempty {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (h_safe : ∃ a, f a < τ) (h_unsafe : ∃ b, f b > τ) :
    ∃ z, f z = τ := by
  obtain ⟨a, ha⟩ := h_safe
  obtain ⟨b, hb⟩ := h_unsafe
  have h_conn : IsPreconnected (Set.univ : Set X) := isPreconnected_univ
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂
    (Set.mem_univ a) (Set.mem_univ b)
    hf.continuousOn continuous_const.continuousOn
    (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc⟩

/-- In a T2 space, the fixed-point set `{x | D x = x}` of a continuous map
is closed. -/
private theorem fixedPoints_closed {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : X → X) (hD : Continuous D) :
    IsClosed {x : X | D x = x} := by
  have hprod : Continuous (fun x => (D x, x)) := by fun_prop
  have : {x : X | D x = x} = (fun x => (D x, x)) ⁻¹' (Set.diagonal X) := by
    ext x; simp [Set.mem_diagonal_iff]
  rw [this]
  exact isClosed_diagonal.preimage hprod

/-- If `D = id` on `{f < τ}`, then `closure {f < τ} ⊆ {x | D x = x}`. -/
private theorem closure_safe_subset_fixed {X : Type*} [TopologicalSpace X] [T2Space X]
    (D : X → X) (hD : Continuous D) (f : X → ℝ) (τ : ℝ)
    (h_pres : ∀ x, f x < τ → D x = x) :
    closure {x : X | f x < τ} ⊆ {x : X | D x = x} :=
  (fixedPoints_closed D hD).closure_subset_iff.mpr (fun x hx => h_pres x hx)

/-- In a connected space, `{f < τ}` is not closed when both safe and unsafe
regions are nonempty. -/
private theorem safe_not_closed {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (h_safe : ∃ a, f a < τ) (h_unsafe : ∃ b, f b > τ) :
    ¬IsClosed {x : X | f x < τ} := by
  intro hcl
  have hop : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
  have hclopen : IsClopen {x : X | f x < τ} := ⟨hcl, hop⟩
  rcases isClopen_iff.mp hclopen with h_empty | h_univ
  · obtain ⟨a, ha⟩ := h_safe
    have : a ∈ ({x : X | f x < τ} : Set X) := ha
    rw [h_empty] at this; exact this
  · obtain ⟨b, hb⟩ := h_unsafe
    have : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
    simp only [Set.mem_setOf_eq] at this; linarith

/-- There exists a boundary point in the closure of the safe region. -/
private theorem boundary_point_in_closure {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (h_safe : ∃ a, f a < τ) (h_unsafe : ∃ b, f b > τ) :
    ∃ z, f z = τ ∧ z ∈ closure {x : X | f x < τ} := by
  have h_strict : {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨subset_closure, fun h_eq => by
      have : IsClosed {x : X | f x < τ} := h_eq ▸ isClosed_closure
      exact safe_not_closed f hf τ h_safe h_unsafe this⟩
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} :=
      closure_minimal (fun x (hx : f x < τ) => le_of_lt hx) (isClosed_le hf continuous_const)
    exact this hz_clos
  have hz_ge : f z ≥ τ := by
    simp only [Set.mem_setOf_eq] at hz_not_safe
    linarith [not_lt.mp hz_not_safe]
  exact ⟨z, le_antisymm hz_le hz_ge, hz_clos⟩

/-! ## The Master Theorem -/

/--
**Manifold of Failure: Master Theorem.**

For any connected Hausdorff behavioral space with a continuous alignment
deviation function that admits both safe and unsafe points:

1. The vulnerability basin `{x | f x > τ}` is open.
2. The defense boundary `{x | f x = τ}` is nonempty.
3. For any continuous utility-preserving defense `D`, there exists a boundary
   point that `D` fixes in place — and therefore `D` cannot make safe.

This is the fundamental impossibility result: continuous defenses that
preserve utility on safe inputs always leave attack surface at the boundary.
-/
theorem master_theorem (M : ManifoldOfFailure) :
    -- 1. Basin is open
    @IsOpen M.X M.top {x | M.f x > M.τ} ∧
    -- 2. Boundary is nonempty
    (∃ z, M.f z = M.τ) ∧
    -- 3. For any continuous utility-preserving defense D, ∃ boundary point D can't fix
    (∀ D : M.X → M.X, @Continuous M.X M.X M.top M.top D →
      (∀ x, M.f x < M.τ → D x = x) →
      ∃ z, M.f z = M.τ ∧ D z = z ∧ ¬(M.f (D z) < M.τ)) := by
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: Basin is open
  · exact @basin_open M.X M.top M.f M.hf M.τ
  -- Part 2: Boundary is nonempty
  · exact @boundary_nonempty M.X M.top M.conn M.f M.hf M.τ M.safe_exists M.unsafe_exists
  -- Part 3: Defense impossibility
  · intro D hD h_pres
    obtain ⟨z, hz_eq, hz_clos⟩ :=
      @boundary_point_in_closure M.X M.top M.conn M.f M.hf M.τ M.safe_exists M.unsafe_exists
    have h_sub := @closure_safe_subset_fixed M.X M.top M.t2 D hD M.f M.τ h_pres
    have hDz : D z = z := h_sub hz_clos
    refine ⟨z, hz_eq, hDz, ?_⟩
    rw [hDz, hz_eq]
    exact lt_irrefl M.τ

end MoF

end
