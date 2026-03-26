/-
  MoF Part 1: Foundations (N-dimensional)
  =======================================
  Foundational definitions and basic topological properties for the
  "Manifold of Failure" (MoF) theory of LLM safety.

  Generalized to work over any topological space X with a continuous
  function f : X → ℝ. No dependence on ℝ × ℝ or ADFunction.

  We define:
    - SafeRegion, UnsafeRegion, Boundary, FailureManifold
  and prove basic topological properties (openness, closedness,
  compactness, disjointness, partition, subset relations).
-/

import Mathlib

open Set Topology Filter

namespace MoF

variable {X : Type*} [TopologicalSpace X]

/-! ## 1. Regions defined by threshold -/

/-- The safe region: where f is strictly below threshold. -/
def SafeRegion (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x < τ}

/-- The unsafe region: where f is strictly above threshold. -/
def UnsafeRegion (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x > τ}

/-- The boundary: where f equals the threshold exactly. -/
def Boundary (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x = τ}

/-- The failure manifold: the closed superlevel set {x | f x ≥ τ}. -/
def FailureManifold (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x ≥ τ}

/-! ## 2. Membership lemmas -/

omit [TopologicalSpace X] in
theorem mem_safeRegion (f : X → ℝ) (τ : ℝ) (x : X) :
    x ∈ SafeRegion f τ ↔ f x < τ :=
  Iff.rfl

omit [TopologicalSpace X] in
theorem mem_unsafeRegion (f : X → ℝ) (τ : ℝ) (x : X) :
    x ∈ UnsafeRegion f τ ↔ f x > τ :=
  Iff.rfl

omit [TopologicalSpace X] in
theorem mem_boundary (f : X → ℝ) (τ : ℝ) (x : X) :
    x ∈ Boundary f τ ↔ f x = τ :=
  Iff.rfl

omit [TopologicalSpace X] in
theorem mem_failureManifold (f : X → ℝ) (τ : ℝ) (x : X) :
    x ∈ FailureManifold f τ ↔ f x ≥ τ :=
  Iff.rfl

/-! ## 3. Openness and Closedness -/

/-- The safe region is open (preimage of an open set under a continuous map). -/
theorem safeRegion_isOpen {f : X → ℝ} (hf : Continuous f) (τ : ℝ) :
    IsOpen (SafeRegion f τ) :=
  isOpen_lt hf continuous_const

/-- The unsafe region is open (preimage of an open set under a continuous map). -/
theorem unsafeRegion_isOpen {f : X → ℝ} (hf : Continuous f) (τ : ℝ) :
    IsOpen (UnsafeRegion f τ) :=
  isOpen_lt continuous_const hf

/-- The boundary is closed (preimage of a closed set under a continuous map). -/
theorem boundary_isClosed {f : X → ℝ} (hf : Continuous f) (τ : ℝ) :
    IsClosed (Boundary f τ) :=
  isClosed_eq hf continuous_const

/-! ## 4. Compactness of boundary -/

/-- The boundary intersected with any compact set is compact
    (a closed set intersected with a compact set is compact). -/
theorem boundary_isCompact {f : X → ℝ} (hf : Continuous f) (τ : ℝ)
    (K : Set X) (hK : IsCompact K) :
    IsCompact (Boundary f τ ∩ K) :=
  hK.inter_left (boundary_isClosed hf τ)

/-! ## 5. Trichotomy / Partition -/

omit [TopologicalSpace X] in
/-- Every point belongs to exactly one of SafeRegion, Boundary, or UnsafeRegion. -/
theorem space_partition (f : X → ℝ) (τ : ℝ) (x : X) :
    (x ∈ SafeRegion f τ ∧ x ∉ Boundary f τ ∧ x ∉ UnsafeRegion f τ) ∨
    (x ∉ SafeRegion f τ ∧ x ∈ Boundary f τ ∧ x ∉ UnsafeRegion f τ) ∨
    (x ∉ SafeRegion f τ ∧ x ∉ Boundary f τ ∧ x ∈ UnsafeRegion f τ) := by
  simp only [mem_safeRegion, mem_boundary, mem_unsafeRegion]
  rcases lt_trichotomy (f x) τ with h | h | h
  · left; exact ⟨h, ne_of_lt h, not_lt.mpr (le_of_lt h)⟩
  · right; left; exact ⟨not_lt.mpr (ge_of_eq h), h, not_lt.mpr (h ▸ le_refl _)⟩
  · right; right; exact ⟨not_lt.mpr (le_of_lt h), ne_of_gt h, h⟩

/-! ## 6. Disjointness -/

omit [TopologicalSpace X] in
/-- SafeRegion and UnsafeRegion are disjoint. -/
theorem safe_unsafe_disjoint (f : X → ℝ) (τ : ℝ) :
    Disjoint (SafeRegion f τ) (UnsafeRegion f τ) := by
  rw [Set.disjoint_iff]
  intro x ⟨hlt, hgt⟩
  simp only [mem_safeRegion, mem_unsafeRegion] at hlt hgt
  exact absurd (lt_trans hlt hgt) (lt_irrefl _)

/-! ## 7. FailureManifold properties -/

/-- The failure manifold is closed (preimage of a closed set under continuous map). -/
theorem failureManifold_isClosed {f : X → ℝ} (hf : Continuous f) (τ : ℝ) :
    IsClosed (FailureManifold f τ) :=
  isClosed_le continuous_const hf

omit [TopologicalSpace X] in
/-- The unsafe region is contained in the failure manifold. -/
theorem unsafe_subset_failure (f : X → ℝ) (τ : ℝ) :
    UnsafeRegion f τ ⊆ FailureManifold f τ := by
  intro x hx
  rw [mem_unsafeRegion] at hx
  rw [mem_failureManifold]
  exact le_of_lt hx

omit [TopologicalSpace X] in
/-- The boundary is contained in the failure manifold. -/
theorem boundary_subset_failure (f : X → ℝ) (τ : ℝ) :
    Boundary f τ ⊆ FailureManifold f τ := by
  intro x hx
  rw [mem_boundary] at hx
  rw [mem_failureManifold]
  exact ge_of_eq hx

omit [TopologicalSpace X] in
/-- The failure manifold is the union of the boundary and the unsafe region. -/
theorem failureManifold_eq_union (f : X → ℝ) (τ : ℝ) :
    FailureManifold f τ = Boundary f τ ∪ UnsafeRegion f τ := by
  ext x
  simp only [FailureManifold, Boundary, UnsafeRegion, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · left; exact heq.symm
    · right; exact hlt
  · rintro (heq | hlt)
    · exact ge_of_eq heq
    · exact le_of_lt hlt

end MoF
