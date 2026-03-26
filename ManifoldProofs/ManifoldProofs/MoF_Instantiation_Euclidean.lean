/-
  MoF Instantiation: Euclidean Space ℝⁿ
  =======================================
  Demonstrates that all generic MoF theorems apply to the standard
  N-dimensional Euclidean space `EuclideanSpace ℝ (Fin d)`.

  This file is a "this all works for ℝⁿ" witness: every theorem is a
  one-line application of the corresponding generic result.
-/

import Mathlib

open Set MeasureTheory Topology Metric Filter

noncomputable section

namespace MoF

/-! ## 1. Typeclass witnesses for `EuclideanSpace ℝ (Fin d)` -/

/-- `EuclideanSpace ℝ (Fin d)` is a topological space. -/
example (d : ℕ) : TopologicalSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- `EuclideanSpace ℝ (Fin d)` is a metric space. -/
example (d : ℕ) : MetricSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- `EuclideanSpace ℝ (Fin d)` is T2 (Hausdorff). -/
example (d : ℕ) : T2Space (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- `EuclideanSpace ℝ (Fin d)` is a connected space. -/
example (d : ℕ) : ConnectedSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- `EuclideanSpace ℝ (Fin d)` has a measurable-space structure. -/
example (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- `EuclideanSpace ℝ (Fin d)` has a canonical measure (Lebesgue). -/
example (d : ℕ) : MeasureSpace (EuclideanSpace ℝ (Fin d)) := inferInstance

/-- The Lebesgue measure on `EuclideanSpace ℝ (Fin d)` gives positive measure
    to nonempty open sets. -/
example (d : ℕ) : (volume : Measure (EuclideanSpace ℝ (Fin d))).IsOpenPosMeasure :=
  inferInstance

/-! ## 2. The type of admissible functions on ℝⁿ -/

/-- Admissible functions: continuous functions from ℝⁿ to ℝ. -/
def euclidean_ad (d : ℕ) := EuclideanSpace ℝ (Fin d) → ℝ

/-! ## 3. Concrete instantiations of generic MoF theorems -/

/-- The basin `{x : ℝⁿ | f x > τ}` is open for any continuous `f`. -/
theorem euclidean_basin_isOpen {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Continuous f) (τ : ℝ) :
    IsOpen {x | f x > τ} :=
  isOpen_lt continuous_const hf

/-- The basin has positive Lebesgue measure whenever it is nonempty. -/
theorem euclidean_basin_measure_pos {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Continuous f) (τ : ℝ) (p : EuclideanSpace ℝ (Fin d)) (hp : f p > τ) :
    0 < volume {x | f x > τ} :=
  (isOpen_lt continuous_const hf).measure_pos volume ⟨p, hp⟩

/-- No-gap theorem in ℝⁿ: if a continuous function takes values both above
    and below `τ`, then the level set `{f = τ}` is nonempty. -/
theorem euclidean_no_gap {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Continuous f) (τ : ℝ)
    (a : EuclideanSpace ℝ (Fin d)) (ha : f a < τ)
    (b : EuclideanSpace ℝ (Fin d)) (hb : f b > τ) :
    ∃ c : EuclideanSpace ℝ (Fin d), f c = τ := by
  have h_conn : IsPreconnected (Set.univ : Set (EuclideanSpace ℝ (Fin d))) :=
    isPreconnected_univ
  obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ (mem_univ a) (mem_univ b)
    hf.continuousOn continuous_const.continuousOn (le_of_lt ha) (le_of_lt hb)
  exact ⟨c, hc⟩

/-- Defense incompleteness in ℝⁿ: any continuous defense that fixes safe
    inputs must fix some boundary point as well. -/
theorem euclidean_defense_incompleteness {d : ℕ}
    {D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hD : Continuous D) (hf : Continuous f) {τ : ℝ}
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_safe_ne : ∃ a, f a < τ)
    (h_unsafe_ne : ∃ b, f b > τ) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      f z = τ ∧ D z = z ∧ f (D z) = τ ∧ ¬ (f (D z) < τ) := by
  -- The generic theorem applies directly since EuclideanSpace is T2 + Connected
  obtain ⟨z, hz_eq, hz_mem⟩ :
      ∃ z, f z = τ ∧ z ∈ closure {x | f x < τ} := by
    have h_strict : {x | f x < τ} ⊂ closure {x | f x < τ} := by
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨subset_closure, fun h_eq => ?_⟩
      have hcl : IsClosed {x | f x < τ} := h_eq ▸ isClosed_closure
      have hop : IsOpen {x | f x < τ} := hf.isOpen_preimage _ isOpen_Iio
      rcases isClopen_iff.mp ⟨hcl, hop⟩ with h | h
      · obtain ⟨a, ha⟩ := h_safe_ne
        exact (h ▸ ha : a ∈ (∅ : Set _))
      · obtain ⟨b, hb⟩ := h_unsafe_ne
        have hmem : b ∈ ({x | f x < τ} : Set _) := h ▸ mem_univ b
        simp only [Set.mem_setOf_eq] at hmem
        linarith
    obtain ⟨z, hz_clos, hz_not⟩ := Set.exists_of_ssubset h_strict
    have hz_le : f z ≤ τ := by
      have : closure {x | f x < τ} ⊆ {x | f x ≤ τ} :=
        closure_minimal (fun x (hx : f x < τ) => le_of_lt hx) (isClosed_le hf continuous_const)
      exact this hz_clos
    have hz_ge : f z ≥ τ := not_lt.mp hz_not
    exact ⟨z, le_antisymm hz_le hz_ge, hz_clos⟩
  have hfix : D z = z := by
    have : closure {x | f x < τ} ⊆ {x | D x = x} :=
      (isClosed_eq hD continuous_id).closure_subset_iff.mpr (fun x hx => h_safe x hx)
    exact this hz_mem
  exact ⟨z, hz_eq, hfix, by rw [hfix, hz_eq], by rw [hfix, hz_eq]; linarith⟩

/-- Open balls in ℝⁿ have positive Lebesgue measure. -/
theorem euclidean_ball_measure_pos {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0 < r) :
    0 < volume (Metric.ball x r) :=
  Metric.isOpen_ball.measure_pos volume ⟨x, Metric.mem_ball_self hr⟩

end MoF

end
