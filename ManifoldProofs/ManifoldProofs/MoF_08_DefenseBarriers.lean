import Mathlib

/-!
# Manifold of Failure — Part 8: Defense Barriers

We prove impossibility results for prompt injection defense.

**Core theorem: Continuous defenses that preserve utility cannot completely
block attacks.**

The key insight: if a defense `D : X → X` is continuous and acts as the
identity on safe inputs, then the set `{x | D x = x}` is closed (in a T2
space). Since the safe region `{f < τ}` is contained in that fixed-point
set, its closure is too. In particular, `D` fixes every boundary point
that lies in `closure {f < τ}`.

Moreover, in any connected space where both safe and unsafe regions exist,
`closure {f < τ}` strictly contains `{f < τ}`, so there are always
boundary-value fixed points of the defense that cannot be pushed safe.

## Main results

1. `defense_fixes_closure` — `{x | D x = x}` is closed when `D` is
   continuous and the codomain is T2.
2. `safe_subset_fixedPoints` — safe inputs are fixed by `D`.
3. `closure_safe_subset_fixedPoints` — the closure of the safe region is
   contained in the fixed-point set.
4. `defense_continuous_on_boundary` — `D` fixes every point in
   `closure {f < τ}`.
5. `boundary_in_closure_of_safe` — in a connected space with both safe
   and unsafe points, `closure {f < τ}` strictly contains `{f < τ}`,
   so there exist boundary-value points fixed by any utility-preserving
   defense.
6. `defense_preserves_boundary_value` — `f(D(z)) = τ` for boundary points
   in `closure {f < τ}`.
7. `defense_cannot_strictly_lower_boundary` — `D` cannot map such points
   to strictly safe points.
8. `defense_incompleteness` — summary theorem.
-/

open Set Topology Filter

noncomputable section

namespace MoF

/-! ## 1. Fixed-point set of a continuous map is closed -/

/--
In a T2 (Hausdorff) space, the set of fixed points of a continuous map
is closed. This follows because `{x | D x = x}` is the preimage of the
closed diagonal under the continuous map `x ↦ (D x, x)`.
-/
theorem defense_fixes_closure
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} (hD : Continuous D) :
    IsClosed {x : X | D x = x} := by
  have hprod : Continuous (fun x => (D x, x)) := by fun_prop
  have : {x : X | D x = x} = (fun x => (D x, x)) ⁻¹' (Set.diagonal X) := by
    ext x; simp [Set.mem_diagonal_iff]
  rw [this]
  exact isClosed_diagonal.preimage hprod

/-! ## 2. Safe inputs are fixed by the defense -/

/--
If `D = id` on `{f < τ}`, then `{f < τ} ⊆ {x | D x = x}`.
-/
theorem safe_subset_fixedPoints
    {X : Type*} {D : X → X} {f : X → ℝ} {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x) :
    {x : X | f x < τ} ⊆ {x : X | D x = x} :=
  fun x hx => h_safe x hx

/--
Since `{x | D x = x}` is closed and contains `{f < τ}`, it contains the
closure of `{f < τ}`.
-/
theorem closure_safe_subset_fixedPoints
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ} {τ : ℝ}
    (hD : Continuous D)
    (h_safe : ∀ x, f x < τ → D x = x) :
    closure {x : X | f x < τ} ⊆ {x : X | D x = x} :=
  (defense_fixes_closure hD).closure_subset_iff.mpr (safe_subset_fixedPoints h_safe)

/-! ## 3. D fixes every point in the closure of the safe region -/

/--
If `D : X → X` is continuous, `X` is T2, and `D = id` on `{f < τ}`, then
`D` fixes every point in `closure {x | f x < τ}`.
-/
theorem defense_continuous_on_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    {z : X} (hz_mem : z ∈ closure {x : X | f x < τ}) :
    D z = z :=
  closure_safe_subset_fixedPoints hD h_safe hz_mem

/-! ## 4. Boundary-value points exist in the closure of the safe region

In any connected space where `{f < τ}` and `{f > τ}` are both nonempty,
the set `{f < τ}` is a nonempty proper open subset, hence NOT closed
(since a nonempty proper clopen set would disconnect the space).
Therefore `closure {f < τ} ⊋ {f < τ}`, and every point in the
difference has function value exactly `τ`.

This means there always exist boundary-value points in `closure {f < τ}` —
points where any utility-preserving defense is forced to be the identity.
-/

/--
In a connected space, `{f < τ}` is not closed when both `{f < τ}` and
`{f > τ}` are nonempty. Therefore `closure {f < τ}` strictly contains
`{f < τ}`.
-/
theorem safe_region_not_closed
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ¬ IsClosed {x : X | f x < τ} := by
  intro h_closed
  -- If {f < τ} is both open and closed, it's clopen.
  have h_open : IsOpen {x : X | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
  have h_clopen : IsClopen {x : X | f x < τ} := ⟨h_closed, h_open⟩
  -- A clopen set in a connected space is ∅ or univ.
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · -- If {f < τ} = ∅, contradicting h_safe_ne.
    obtain ⟨a, ha⟩ := h_safe_ne
    have : a ∈ ({x : X | f x < τ} : Set X) := ha
    rw [h_empty] at this
    exact this
  · -- If {f < τ} = univ, then f b < τ for all b, contradicting h_unsafe_ne.
    obtain ⟨b, hb⟩ := h_unsafe_ne
    have hmem : b ∈ ({x : X | f x < τ} : Set X) := h_univ ▸ mem_univ b
    simp only [Set.mem_setOf_eq] at hmem
    linarith

/--
`closure {f < τ}` strictly contains `{f < τ}` when both safe and unsafe
regions are nonempty in a connected space.
-/
theorem closure_safe_strictly_larger
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    {x : X | f x < τ} ⊂ closure {x : X | f x < τ} := by
  rw [Set.ssubset_iff_subset_ne]
  exact ⟨subset_closure, fun h_eq => by
    have : IsClosed {x : X | f x < τ} := h_eq ▸ isClosed_closure
    exact safe_region_not_closed hf h_safe_ne h_unsafe_ne this⟩

/--
There exist boundary-value points (f(z) = τ) in `closure {f < τ}`.
Any such point is fixed by every continuous utility-preserving defense.
-/
theorem boundary_in_closure_of_safe
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ z ∈ closure {x : X | f x < τ} := by
  -- closure {f < τ} strictly contains {f < τ}, so there exists z in the
  -- difference. Such z has f(z) ≥ τ (since {f > τ} is disjoint from
  -- closure {f < τ}) and f(z) ≤ τ (since closure {f < τ} ⊆ {f ≤ τ}).
  have h_strict := closure_safe_strictly_larger hf h_safe_ne h_unsafe_ne
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hz_ge : f z ≥ τ := by
    simp only [Set.mem_setOf_eq] at hz_not_safe
    linarith [not_lt.mp hz_not_safe]
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} := by
      apply closure_minimal
      · intro x (hx : f x < τ); exact le_of_lt hx
      · exact isClosed_le hf continuous_const
    exact this hz_clos
  exact ⟨z, le_antisymm hz_le hz_ge, hz_clos⟩

/-! ## 5. Defense preserves boundary value -/

/--
If `D` is continuous, `D = id` on safe inputs, and `z` is a boundary point
in the closure of the safe region, then `f(D(z)) = τ`.
-/
theorem defense_preserves_boundary_value
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    {z : X} (hz : f z = τ)
    (hz_mem : z ∈ closure {x : X | f x < τ}) :
    f (D z) = τ := by
  have hDz : D z = z := defense_continuous_on_boundary hD h_safe hz_mem
  rw [hDz, hz]

/-! ## 6. Defense cannot strictly lower boundary points -/

/--
A continuous defense cannot map boundary points (that lie in the closure
of the safe region) to strictly safe points.
-/
theorem defense_cannot_strictly_lower_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    {z : X} (hz : f z = τ)
    (hz_mem : z ∈ closure {x : X | f x < τ}) :
    ¬ (f (D z) < τ) := by
  have := defense_preserves_boundary_value hD h_safe hz hz_mem
  linarith

/-! ## 7. Summary: Defense Incompleteness Theorem -/

/--
**Defense Incompleteness Theorem.**

On a connected T2 space, if `f` is continuous and has values both below and
above `τ`, then for any continuous defense `D` that fixes safe inputs:

1. There exist boundary-value points (`f(z) = τ`) that `D` fixes.
2. `D` cannot push any such point into the safe region.

This is the fundamental impossibility: continuous utility-preserving
defenses always leave "attack surface" at the boundary.
-/
theorem defense_incompleteness
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ D z = z ∧ f (D z) = τ ∧ ¬ (f (D z) < τ) := by
  obtain ⟨z, hz_eq, hz_mem⟩ := boundary_in_closure_of_safe hf h_safe_ne h_unsafe_ne
  exact ⟨z, hz_eq,
    defense_continuous_on_boundary hD h_safe hz_mem,
    defense_preserves_boundary_value hD h_safe hz_eq hz_mem,
    defense_cannot_strictly_lower_boundary hD h_safe hz_eq hz_mem⟩

/-! ## 8. Closure characterization for boundary -/

/--
Every point in `closure {f < τ} \ {f < τ}` has function value exactly `τ`.
These are the boundary-value points where defenses are forced to be identity.
-/
theorem closure_boundary_value
    {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    {z : X} (hz_clos : z ∈ closure {x : X | f x < τ})
    (hz_not_safe : ¬ (f z < τ)) :
    f z = τ := by
  have hz_le : f z ≤ τ := by
    have : closure {x : X | f x < τ} ⊆ {x : X | f x ≤ τ} := by
      apply closure_minimal
      · intro x (hx : f x < τ); exact le_of_lt hx
      · exact isClosed_le hf continuous_const
    exact this hz_clos
  linarith [not_lt.mp hz_not_safe]

/--
The set of points in `closure {f < τ}` with value `≥ τ` is exactly the
set of boundary-value points in the closure. All of them are fixed by
any continuous utility-preserving defense.
-/
theorem defense_fixes_all_closure_boundary
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    {z : X} (hz_clos : z ∈ closure {x : X | f x < τ})
    (hz_not_safe : ¬ (f z < τ)) :
    D z = z ∧ f z = τ ∧ f (D z) = τ := by
  have hz_eq := closure_boundary_value hf hz_clos hz_not_safe
  exact ⟨defense_continuous_on_boundary hD h_safe hz_clos,
         hz_eq,
         defense_preserves_boundary_value hD h_safe hz_eq hz_clos⟩

/-! ## 9. Universal statement for closure boundary fixed points -/

/--
**Universal version of the defense fixed-point result.**

For ALL `z` in `closure {f < τ} \ {f < τ}`, the defense fixes `z` and
`f z = τ`. This wraps `defense_fixes_all_closure_boundary` as a clean
universal statement over the set difference, with no extra hypotheses
beyond membership.
-/
theorem defense_fixes_all_closure_boundary_points
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x) :
    ∀ z ∈ closure {x : X | f x < τ} \ {x : X | f x < τ},
      D z = z ∧ f z = τ := by
  intro z ⟨hz_clos, hz_not_safe⟩
  have hns : ¬ (f z < τ) := hz_not_safe
  exact ⟨defense_continuous_on_boundary hD h_safe hz_clos,
         closure_boundary_value hf hz_clos hns⟩

/-! ## 10. Not all points with `f z = τ` lie in `closure {f < τ}`

**Counterexample (documented).**

Consider `f(x, y) = (x² + y²) · ((x - 3)² + y² - 1)` with `τ = 0`.
The origin satisfies `f(0, 0) = 0 · (9 - 1) = 0`, so `f(0,0) = τ`.
However, in every neighborhood of the origin, `f` is strictly positive
(since near the origin `x² + y²` is small positive and `(x-3)²+y²-1`
is approximately `8 > 0`). Thus the origin is an *isolated* boundary-
value point — it does NOT belong to `closure {f < 0}` because `{f < 0}`
is entirely contained in the region near the circle `(x-3)²+y²=1`.

This shows: **the set `{z | f z = τ}` can be strictly larger than
`closure {f < τ} \ {f < τ}`.**  The theorems `defense_fixes_all_closure_boundary_points`
and `defense_incompleteness` apply only to points in the closure of the
safe region, not to every level-set point.
-/

/--
There exist spaces and continuous functions where some point has
`f z = τ` but `z ∉ closure {f < τ}`. In other words, NOT every
boundary-value point is necessarily in the closure of the safe region.

We witness this with `X = ℝ`, `f x = x²`, `τ = 0`: the origin has
`f 0 = 0 = τ` but `{x : ℝ | x² < 0} = ∅`, so
`closure {x : ℝ | x² < 0} = ∅` and `0 ∉ ∅`.
-/
theorem not_all_boundary_fixed :
    ∃ (f : ℝ → ℝ) (τ : ℝ), Continuous f ∧
      (∃ z : ℝ, f z = τ ∧ z ∉ closure {x : ℝ | f x < τ}) := by
  refine ⟨fun x => x ^ 2, 0, continuous_pow 2, 0, by norm_num, ?_⟩
  have hempty : {x : ℝ | x ^ 2 < 0} = ∅ := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_lt.mpr (sq_nonneg x)
  rw [hempty, closure_empty]
  exact fun h => h

/-! ## 11. The set of fixed boundary points is nonempty -/

/--
The set `{z | f z = τ ∧ z ∈ closure {f < τ} ∧ z ∉ {f < τ}}` of
closure-boundary fixed points is nonempty. This combines
`boundary_in_closure_of_safe` (existence of a boundary point in the
closure) with `closure_safe_strictly_larger` (the closure is strictly
larger than the safe region).
-/
theorem boundary_fixed_points_nonempty
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a : X, f a < τ)
    (h_unsafe_ne : ∃ b : X, f b > τ) :
    ∃ z : X, f z = τ ∧ z ∈ closure {x : X | f x < τ} ∧
      z ∉ {x : X | f x < τ} ∧ D z = z := by
  have h_strict := closure_safe_strictly_larger hf h_safe_ne h_unsafe_ne
  obtain ⟨z, hz_clos, hz_not_safe⟩ := Set.exists_of_ssubset h_strict
  have hns : ¬ (f z < τ) := hz_not_safe
  exact ⟨z,
    closure_boundary_value hf hz_clos hns,
    hz_clos,
    hz_not_safe,
    defense_continuous_on_boundary hD h_safe hz_clos⟩

end MoF
