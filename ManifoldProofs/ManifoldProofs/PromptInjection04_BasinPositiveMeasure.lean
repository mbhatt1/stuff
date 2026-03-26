import Mathlib
/-
  Prompt Injection Theorem 4 — Vulnerability Basin Has Positive Measure
  =====================================================================
  Lean 4 / Mathlib formalization from the "Manifold of Failure" framework.

  **Statement (informal):**
    If the Alignment Deviation function AD : ℝ² → ℝ is continuous and
    there exists a point p with AD(p) > τ, then the superlevel set
      S_τ = { x : ℝ² | AD(x) > τ }
    is open and nonempty, hence contains an open ball, hence has
    positive Lebesgue measure.

  **Interpretation:**
    Prompt injection vulnerabilities, once they exist at any single
    behavioral-space configuration, cannot be confined to a
    measure-zero "hair" — they occupy a positive-volume region of
    the prompt space.  The volume is bounded below by the area of
    an open ball whose radius depends on the continuity modulus of AD.

  We formalize:
    1. AD (called `f`) as a continuous function ℝ × ℝ → ℝ
    2. The superlevel set S_τ and its openness
    3. Nonemptiness from the witness hypothesis
    4. Existence of an open ball inside S_τ
    5. Positive Lebesgue measure of S_τ via MeasureTheory.IsOpen.measure_pos
    6. An interpretive corollary packaging the full theorem
-/


open Set MeasureTheory Topology Metric

noncomputable section

/-! ## 1. The Alignment Deviation function and threshold -/

/-- Bundle carrying a continuous "Alignment Deviation" map and a threshold. -/
structure AlignmentDeviationData where
  /-- The alignment deviation function AD : ℝ × ℝ → ℝ. -/
  f : ℝ × ℝ → ℝ
  /-- Continuity of f over the full behavioral space. -/
  hf_cont : Continuous f
  /-- The vulnerability threshold τ. -/
  τ : ℝ

namespace AlignmentDeviationData

variable (ad : AlignmentDeviationData)

/-! ## 2. The vulnerability basin (superlevel set) and its openness -/

/-- The vulnerability basin S_τ = { x : ℝ × ℝ | f(x) > τ }. -/
def vulnerabilityBasin : Set (ℝ × ℝ) :=
  { x | ad.τ < ad.f x }

/--
  The vulnerability basin is an open set.
  Proof: it is the preimage of the open ray (τ, ∞) under the continuous map f.
-/
theorem vulnerabilityBasin_isOpen : IsOpen ad.vulnerabilityBasin := by
  exact isOpen_lt continuous_const ad.hf_cont

/-! ## 3. Nonemptiness from a witness -/

/--
  If there exists a point p in the behavioral space with AD(p) > τ,
  then the vulnerability basin is nonempty.
-/
theorem vulnerabilityBasin_nonempty
    (p : ℝ × ℝ) (hp : ad.τ < ad.f p) :
    (ad.vulnerabilityBasin).Nonempty :=
  ⟨p, hp⟩

/-! ## 4. An open nonempty set contains an open ball -/

/--
  Every nonempty open set in a metric space contains an open ball.
-/
theorem exists_ball_subset_of_isOpen_nonempty
    {X : Type*} [MetricSpace X]
    {S : Set X} (hS_open : IsOpen S) (hS_ne : S.Nonempty) :
    ∃ c : X, ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ S := by
  obtain ⟨x, hx⟩ := hS_ne
  rw [Metric.isOpen_iff] at hS_open
  obtain ⟨ε, hε_pos, hε_sub⟩ := hS_open x hx
  exact ⟨x, ε, hε_pos, hε_sub⟩

/--
  The vulnerability basin contains an open ball when it is nonempty.
-/
theorem vulnerabilityBasin_contains_ball
    (p : ℝ × ℝ) (hp : ad.τ < ad.f p) :
    ∃ c : ℝ × ℝ, ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ ad.vulnerabilityBasin :=
  exists_ball_subset_of_isOpen_nonempty
    ad.vulnerabilityBasin_isOpen
    (ad.vulnerabilityBasin_nonempty p hp)

/-! ## 5. Positive Lebesgue measure -/

/--
  **Main theorem (Theorem 4).**
  The vulnerability basin has strictly positive Lebesgue measure
  whenever it is nonempty.

  This follows from the general Mathlib fact that every nonempty open
  set in ℝⁿ has positive measure with respect to the Lebesgue
  (volume) measure.
-/
theorem vulnerabilityBasin_measure_pos
    (p : ℝ × ℝ) (hp : ad.τ < ad.f p) :
    0 < MeasureTheory.volume ad.vulnerabilityBasin := by
  apply IsOpen.measure_pos
  · exact ad.vulnerabilityBasin_isOpen
  · exact ad.vulnerabilityBasin_nonempty p hp

/-! ## 6. Interpretive corollary -/

/--
  **Corollary (Vulnerability Cannot Be Measure-Zero).**

  If the Alignment Deviation function is continuous and exceeds the
  vulnerability threshold τ at even a single point, then the set of
  all vulnerable configurations has *positive* Lebesgue measure.

  In particular, the fraction of the behavioral space that is
  vulnerable is bounded below by a constant that depends on:
    • the continuity modulus of AD at the witness point, and
    • the amount by which AD(p) exceeds τ.

  Concretely, if AD is Lipschitz with constant L, and AD(p) − τ = δ,
  then the vulnerability basin contains a ball of radius δ/L, whose
  area π(δ/L)² is a lower bound on the measure.
-/
theorem vulnerability_basin_positive_measure_corollary
    (f : ℝ × ℝ → ℝ)
    (hf : Continuous f)
    (τ : ℝ)
    (p : ℝ × ℝ)
    (hp : τ < f p) :
    let ad : AlignmentDeviationData := ⟨f, hf, τ⟩
    IsOpen ad.vulnerabilityBasin ∧
    (ad.vulnerabilityBasin).Nonempty ∧
    (∃ c r, 0 < r ∧ Metric.ball c r ⊆ ad.vulnerabilityBasin) ∧
    0 < MeasureTheory.volume ad.vulnerabilityBasin := by
  intro ad
  exact ⟨
    ad.vulnerabilityBasin_isOpen,
    ad.vulnerabilityBasin_nonempty p hp,
    ad.vulnerabilityBasin_contains_ball p hp,
    ad.vulnerabilityBasin_measure_pos p hp
  ⟩

/-!
  ## Summary

  We have established a chain of four implications:

  ```
  AD continuous ∧ ∃ p, AD(p) > τ
    ⟹  S_τ is open and nonempty           (preimage of open set)
    ⟹  S_τ contains an open ball           (metric space property)
    ⟹  S_τ has positive Lebesgue measure   (IsOpen.measure_pos)
  ```

  **Security interpretation:**
  The theorem quantifies a fundamental barrier to "patching away"
  prompt injection vulnerabilities one at a time.  Because AD is
  continuous (small changes in the behavioral features produce small
  changes in the deviation score), every vulnerable point is surrounded
  by a neighborhood of other vulnerable points.  No isolated fix can
  reduce the vulnerability measure to zero; instead, the model's
  alignment boundary itself must shift so that the *supremum* of AD
  over the entire behavioral space drops below τ.
-/

end AlignmentDeviationData

end
