/-
  MoF Advanced Part 2: Boundary Dimension
  ========================================
  Structural properties of the boundary {x | f x = τ}.

  Key question: Is the boundary a smooth curve or a fractal?

  Full Hausdorff dimension theory is beyond current Mathlib. We instead
  prove achievable results about the topological and local structure of
  the level set {f = τ}.

  Results:
    1. boundary_is_closed
    2. boundary_is_compact_on_compact
    3. boundary_empty_of_no_crossing
    4. boundary_nonempty_connected
    5. boundary_is_preimage_singleton
    6. regular_value_boundary (1D inverse-function-theorem flavor)
    7. boundary_locally_finite_1d
-/

import Mathlib

open Set Topology Filter Metric

namespace MoF

variable {X : Type*} [TopologicalSpace X]

/-! ## Boundary = level set {x | f x = τ} -/

/-- The boundary (level set) as used throughout this file. -/
def BdrySet (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x = τ}

/-! ## 1. The boundary is closed -/

/-- The boundary {x | f x = τ} is closed for any continuous f. -/
theorem boundary_is_closed (f : X → ℝ) (τ : ℝ) (hf : Continuous f) :
    IsClosed (BdrySet f τ) :=
  isClosed_eq hf continuous_const

/-! ## 2. Boundary intersected with a compact set is compact -/

/-- On a compact set K, the boundary is compact. -/
theorem boundary_is_compact_on_compact (f : X → ℝ) (τ : ℝ) (hf : Continuous f)
    (K : Set X) (hK : IsCompact K) :
    IsCompact (BdrySet f τ ∩ K) :=
  hK.inter_left (isClosed_eq hf continuous_const)

/-! ## 3. Boundary is empty when f never equals τ -/

omit [TopologicalSpace X] in
/-- If f(x) ≠ τ for all x, the boundary is empty. -/
theorem boundary_empty_of_no_crossing (f : X → ℝ) (τ : ℝ)
    (h : ∀ x, f x ≠ τ) :
    BdrySet f τ = ∅ := by
  ext x
  simp only [BdrySet, mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact h x

/-! ## 4. Boundary is nonempty on a connected space (IVT) -/

/-- On a connected space, if f takes values above and below τ, the boundary
    is nonempty. This is the intermediate value theorem in topological form. -/
theorem boundary_nonempty_connected [PreconnectedSpace X]
    (f : X → ℝ) (τ : ℝ) (hf : Continuous f)
    (a b : X) (ha : f a < τ) (hb : f b > τ) :
    (BdrySet f τ).Nonempty := by
  have hmem : τ ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨c, hc⟩ := intermediate_value_univ a b hf hmem
  exact ⟨c, hc⟩

/-! ## 5. Boundary is the preimage of {τ} -/

omit [TopologicalSpace X] in
/-- The boundary is definitionally f⁻¹'({τ}). -/
theorem boundary_is_preimage_singleton (f : X → ℝ) (τ : ℝ) :
    BdrySet f τ = f ⁻¹' {τ} := by
  ext x
  simp [BdrySet]

/-! ## 6–7. Regular value results in 1D -/

section OneDimensional

/-! We work with f : ℝ → ℝ. When f has a nonzero derivative at a boundary
    point z, the implicit function theorem (in 1D: the inverse function theorem)
    tells us that f is locally injective, so z is an isolated boundary point. -/

/-- If f has nonzero derivative at z with f(z) = τ, then z is an isolated
    point of the level set: there exists a punctured neighborhood where f ≠ τ. -/
theorem regular_value_boundary
    (f : ℝ → ℝ) (τ d z : ℝ) (hderiv : HasDerivAt f d z)
    (hd : d ≠ 0) (_hfz : f z = τ) :
    ∃ ε > 0, ∀ x ∈ Ioo (z - ε) (z + ε), x ≠ z → f x ≠ τ := by
  -- Use Mathlib's HasDerivAt.eventually_ne: nonzero derivative implies
  -- f is eventually different from any constant near z.
  have hev := hderiv.eventually_ne hd (c := τ)
  rw [Filter.Eventually, mem_nhdsWithin] at hev
  obtain ⟨U, hU_open, hz_mem, hU_sub⟩ := hev
  obtain ⟨ε, hε_pos, hball⟩ := Metric.isOpen_iff.mp hU_open z hz_mem
  exact ⟨ε, hε_pos, fun x hx hxz => hU_sub ⟨hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩), hxz⟩⟩

/-- At a regular boundary point z (f(z) = τ, f'(z) ≠ 0), the boundary is
    locally exactly {z}. -/
theorem boundary_locally_finite_1d
    (f : ℝ → ℝ) (τ d z : ℝ) (hderiv : HasDerivAt f d z)
    (hd : d ≠ 0) (hfz : f z = τ) :
    ∃ ε > 0, {x ∈ Ioo (z - ε) (z + ε) | f x = τ} = {z} := by
  obtain ⟨ε, hε_pos, hε⟩ := regular_value_boundary f τ d z hderiv hd hfz
  refine ⟨ε, hε_pos, ?_⟩
  ext x
  simp only [mem_Ioo, mem_singleton_iff]
  constructor
  · rintro ⟨hx_mem, hfx⟩
    by_contra hxz
    exact hε x hx_mem hxz hfx
  · rintro rfl
    exact ⟨⟨by linarith, by linarith⟩, hfz⟩

end OneDimensional

end MoF
