import Mathlib

/-!
# Manifold of Failure — Part 2: Vulnerability Basin Structure (N-dimensional)

We prove that vulnerability basins (superlevel sets of continuous functions)
are open sets with positive measure, generalized to arbitrary topological,
metric, and measure spaces.

Given a continuous function `f : X → ℝ` and a threshold `τ : ℝ`,
the **vulnerability basin** is the superlevel set `{x | f x > τ}`.

## Main results

- `Basin` — definition of the superlevel set, generic over any type `X`
- `Sublevel` — definition of the sublevel set, generic over any type `X`
- `basin_isOpen` — the basin is open (preimage of open ray) for any `TopologicalSpace X`
- `basin_nonempty` — nonemptiness from a witness, for any type
- `basin_contains_ball` — metric characterization of openness for `PseudoMetricSpace X`
- `basin_measure_pos` — positive measure when nonempty, for `MeasureSpace X` with
  `IsOpenPosMeasure`
- `sublevel_isClosed` — the sublevel set is closed for any `TopologicalSpace X`
- `basin_complement_unsafe` — complement of basin is the sublevel set
- `basin_interior_eq_self` — the interior of the basin equals itself
-/

open Set MeasureTheory Topology Metric Filter

noncomputable section

namespace MoF

variable {X : Type*}

/-- The vulnerability basin: the superlevel set `{x : X | f x > τ}`. -/
def Basin (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x > τ}

/-- The sublevel set `{x : X | f x ≤ τ}`. -/
def Sublevel (f : X → ℝ) (τ : ℝ) : Set X :=
  {x : X | f x ≤ τ}

/-! ## Basin is open -/

/-- The vulnerability basin is an open set: it is the preimage of `(τ, ∞)` under
a continuous map, for any topological space `X`. -/
theorem basin_isOpen [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsOpen (Basin f τ) := by
  exact isOpen_lt continuous_const hf

/-! ## Basin is nonempty given a witness -/

/-- If there exists a point `p` with `f p > τ`, then the basin is nonempty. -/
theorem basin_nonempty (f : X → ℝ) (τ : ℝ) (p : X) (hp : f p > τ) :
    (Basin f τ).Nonempty :=
  ⟨p, hp⟩

/-! ## Basin contains a ball around every interior point -/

/-- Every point in the basin has an open ball around it contained in the basin,
for any pseudo-metric space `X`. -/
theorem basin_contains_ball [PseudoMetricSpace X] (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (p : X) (hp : f p > τ) :
    ∃ r > 0, Metric.ball p r ⊆ Basin f τ := by
  have hopen := basin_isOpen f hf τ
  rw [Metric.isOpen_iff] at hopen
  exact hopen p hp

/-! ## Basin interior equals itself -/

/-- Since the basin is open, its interior is itself. -/
theorem basin_interior_eq_self [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    interior (Basin f τ) = Basin f τ :=
  (basin_isOpen f hf τ).interior_eq

/-! ## Basin has positive measure -/

/-- The vulnerability basin has positive measure whenever it is nonempty,
in any measure space where nonempty open sets have positive measure. -/
theorem basin_measure_pos [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] (f : X → ℝ) (hf : Continuous f) (τ : ℝ)
    (p : X) (hp : f p > τ) :
    0 < μ (Basin f τ) :=
  IsOpen.measure_pos μ (basin_isOpen f hf τ) (basin_nonempty f τ p hp)

/-! ## Sublevel set is closed -/

/-- The sublevel set `{x | f x ≤ τ}` is closed, for any topological space `X`. -/
theorem sublevel_isClosed [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) (τ : ℝ) :
    IsClosed (Sublevel f τ) := by
  exact isClosed_le hf continuous_const

/-! ## Complement of basin is the sublevel set -/

/-- The complement of the basin is exactly the sublevel set `{x | f x ≤ τ}`. -/
theorem basin_complement_unsafe (f : X → ℝ) (τ : ℝ) :
    (Basin f τ)ᶜ = Sublevel f τ := by
  ext x
  simp only [Basin, Sublevel, mem_compl_iff, mem_setOf_eq, not_lt]

end MoF

end
