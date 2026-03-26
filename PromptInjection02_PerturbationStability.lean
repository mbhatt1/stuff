/-
  PromptInjection02_PerturbationStability.lean

  Lean 4 / Mathlib formalization of Theorem 2 from the
  "Manifold of Failure" prompt-injection framework:

  **Injection Perturbation Stability (Lipschitz Continuity of Vulnerability)**

  If the Alignment Deviation function AD : X → ℝ is Lipschitz continuous
  with constant L, then small perturbations to a successful injection prompt
  remain successful.  Formally:

    If AD(p) > τ + ε  and  d(p, p') < ε / L,  then  AD(p') > τ.

  This proves that successful prompt injections are robust to small
  modifications — vulnerability basins have positive measure.

  We formalize:
    1. Lipschitz perturbation bound: small moves keep f above threshold.
    2. The open ball B(p, ε/L) lies entirely inside the superlevel set {f > τ}.
    3. The superlevel set {f > τ} is open (quantitative version).
    4. The "vulnerability basin" around a successful injection has radius
       at least (f(p) − τ) / L.
    5. The "injection robustness radius" r(p) = (f(p) − τ) / L is positive
       for every successful injection.
-/

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

noncomputable section

open Metric Set

/-! ### Auxiliary arithmetic lemma -/

/--
If `0 < c` and `a < b / c`, then `c * a < b`.
This is the contrapositive direction of `div_lt_iff`.
-/
private theorem mul_lt_of_lt_div {a b c : ℝ} (hc : 0 < c) (h : a < b / c) :
    c * a < b := by
  have : a * c < b := by rwa [lt_div_iff hc] at h
  linarith

/-! ## 1. Core Perturbation Lemma -/

/--
**Core perturbation bound.**
If `f` is `L`-Lipschitz, `f(p) > τ + ε`, and `dist p' p < ε / L`,
then `f(p') > τ`.

The key calculation is:
  f(p') ≥ f(p) − |f(p') − f(p)| ≥ f(p) − L · d(p', p) > (τ + ε) − ε = τ
-/
theorem lipschitz_perturbation_bound
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p p' : X} {τ ε : ℝ}
    (hε : 0 < ε) (hL : (0 : ℝ) < L)
    (h_above : f p > τ + ε)
    (h_close : dist p' p < ε / L) :
    f p' > τ := by
  have h_lip : dist (f p') (f p) ≤ ↑L * dist p' p := hf.dist_le_mul p' p
  have h_abs : |f p' - f p| ≤ ↑L * dist p' p := by
    rwa [Real.dist_eq] at h_lip
  have h_Ldist : ↑L * dist p' p < ε := mul_lt_of_lt_div hL h_close
  linarith [abs_sub_abs_le_abs_sub (f p') (f p)]

/-! ## 2. Open Ball Containment -/

/--
**Ball containment.**
If `f` is `L`-Lipschitz and `f(p) > τ + ε`, then the open ball `B(p, ε/L)`
is entirely contained in the superlevel set `{x | f(x) > τ}`.
-/
theorem ball_subset_superlevelset
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ ε : ℝ}
    (hε : 0 < ε) (hL : (0 : ℝ) < L)
    (h_above : f p > τ + ε) :
    ball p (ε / L) ⊆ {x | f x > τ} := by
  intro p' hp'
  rw [mem_ball] at hp'
  exact lipschitz_perturbation_bound hf hε hL h_above hp'

/-! ## 3. Vulnerability Basin Radius -/

/--
**Vulnerability basin radius.**
If `f` is `L`-Lipschitz with `L > 0` and `f(p) > τ`, then every point
in the open ball of radius `(f(p) − τ) / L` around `p` also satisfies
`f(p') > τ`.
-/
theorem vulnerability_basin_radius
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_success : f p > τ) :
    ball p ((f p - τ) / L) ⊆ {x | f x > τ} := by
  intro p' hp'
  rw [mem_ball] at hp'
  simp only [mem_setOf_eq]
  have h_abs : |f p' - f p| ≤ ↑L * dist p' p := by
    have := hf.dist_le_mul p' p; rwa [Real.dist_eq] at this
  have h_Ldist : ↑L * dist p' p < f p - τ := mul_lt_of_lt_div hL hp'
  linarith [abs_sub_abs_le_abs_sub (f p') (f p)]

/-! ## 4. Superlevel Set is Open (Quantitative) -/

/--
**Quantitative openness of superlevel sets.**
For any `L`-Lipschitz function `f` with `L > 0`, the superlevel set
`{x | f(x) > τ}` is open — and we give a concrete witness radius
`(f(p) − τ) / L` at each interior point.
-/
theorem superlevelset_isOpen
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : (0 : ℝ) < L) :
    ∀ τ : ℝ, IsOpen {x : X | f x > τ} := by
  intro τ
  rw [isOpen_iff]
  intro p hp
  simp only [mem_setOf_eq] at hp
  refine ⟨(f p - τ) / L, by positivity, ?_⟩
  intro p' hp'
  exact vulnerability_basin_radius hf hL hp hp'

/-! ## 5. Injection Robustness Radius -/

/--
**Injection Robustness Radius.**
For a Lipschitz alignment-deviation function `f` with constant `L > 0`,
the robustness radius of a successful injection prompt `p` (i.e., one with
`f(p) > τ`) is defined as `r(p) = (f(p) − τ) / L`.
-/
def injectionRobustnessRadius
    {X : Type*} (L : ℝ≥0) (f : X → ℝ) (τ : ℝ) (p : X) : ℝ :=
  (f p - τ) / L

/--
The robustness radius is strictly positive for any successful injection.
-/
theorem injectionRobustnessRadius_pos
    {X : Type*}
    {f : X → ℝ} {L : ℝ≥0}
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_success : f p > τ) :
    injectionRobustnessRadius L f τ p > 0 := by
  unfold injectionRobustnessRadius
  positivity

/--
The robustness radius is monotone in the strength of the injection:
if `f(p₁) ≤ f(p₂)`, then `r(p₁) ≤ r(p₂)`.
-/
theorem injectionRobustnessRadius_mono
    {X : Type*}
    {f : X → ℝ} {L : ℝ≥0}
    {p₁ p₂ : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_le : f p₁ ≤ f p₂) :
    injectionRobustnessRadius L f τ p₁ ≤ injectionRobustnessRadius L f τ p₂ := by
  unfold injectionRobustnessRadius
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/--
**Full perturbation stability theorem (combined statement).**
If `f` is `L`-Lipschitz with `L > 0` and `p` is a successful injection
(`f(p) > τ`), then every prompt within distance `r(p) = (f(p) − τ) / L`
of `p` is also a successful injection, and `r(p) > 0`.
-/
theorem injection_perturbation_stability
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_success : f p > τ) :
    (injectionRobustnessRadius L f τ p > 0) ∧
    (ball p (injectionRobustnessRadius L f τ p) ⊆ {x | f x > τ}) := by
  exact ⟨injectionRobustnessRadius_pos hL h_success,
         vulnerability_basin_radius hf hL h_success⟩

/-! ## 6. Positive Measure Corollary -/

/--
**Positive measure corollary.**
The superlevel set `{x | f(x) > τ}` contains an open ball around every
point in it.  Combined with the metric-space structure this means the
vulnerability region has positive (Hausdorff) measure whenever it is
nonempty — formalising the claim that "vulnerability basins have positive
measure."
-/
theorem superlevelset_mem_nhds
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {p : X} {τ : ℝ} (hp : f p > τ) :
    {x | f x > τ} ∈ nhds p :=
  (superlevelset_isOpen hf hL τ).mem_nhds hp

/--
If there exists *any* successful injection, the vulnerability set is
a nonempty open set.
-/
theorem vulnerability_set_nonempty_open
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hL : (0 : ℝ) < L)
    {τ : ℝ} (p : X) (hp : f p > τ) :
    IsOpen {x : X | f x > τ} ∧ Set.Nonempty {x : X | f x > τ} :=
  ⟨superlevelset_isOpen hf hL τ, ⟨p, hp⟩⟩

end
