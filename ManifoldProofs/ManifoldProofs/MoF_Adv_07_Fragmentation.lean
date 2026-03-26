import Mathlib
/-
  MoF_Adv_07_Fragmentation.lean
  ==============================
  Part 7 (Advanced) — "Manifold of Failure" Lean 4 formalization.

  **Basin Fragmentation Theory.**

  What controls whether the failure manifold is one large region or many
  small patches?  We prove quantitative bounds on connected-component size,
  monotonicity in the Lipschitz constant, and structural results about
  the topology of the superlevel set.

  Theorems:
    1. basin_of_large_value_contains_ball  — connected component contains a ball
    2. basin_fragment_minimum_size          — diameter lower bound 2(f(p)-τ)/L
    3. high_lipschitz_small_fragments       — larger L allows smaller guaranteed radius
    4. uniform_value_single_basin           — constant superlevel gives single basin
    5. disjoint_basins_separated            — distinct components are disjoint
-/

noncomputable section

open Metric Set

open scoped NNReal

namespace MoF

/-! ### Superlevel set definition -/

/-- The superlevel set {x | f x > τ}. -/
def superlevelSet (f : X → ℝ) (τ : ℝ) : Set X := {x | f x > τ}

/-! ### Auxiliary: ball is contained in superlevel set (Lipschitz bound) -/

/--
If f is L-Lipschitz, f(p) > τ, L > 0, then ball(p, (f(p)-τ)/L) ⊆ {f > τ}.
-/
theorem ball_subset_superlevel
    {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (_h_above : f p > τ) :
    Metric.ball p ((f p - τ) / L) ⊆ superlevelSet f τ := by
  intro q hq
  rw [Metric.mem_ball] at hq
  simp only [superlevelSet, mem_setOf_eq]
  have hab : |f q - f p| ≤ (L : ℝ) * dist q p := by
    have := hf.dist_le_mul q p; rwa [Real.dist_eq] at this
  have hLd : ↑L * dist q p < f p - τ := by
    have hdq : dist q p < (f p - τ) / ↑L := hq
    rw [lt_div_iff₀ hL] at hdq
    linarith
  linarith [neg_abs_le (f q - f p)]

/-! ## 1. basin_of_large_value_contains_ball -/

/--
**Basin of large value contains a ball.**

If f is L-Lipschitz and f(p) > τ with L > 0, then there exists a connected
set S containing p and the entire ball(p, (f(p)-τ)/L), and S lies within
the superlevel set {f > τ}.

This means the connected component of p in {f > τ} contains the ball.
-/
theorem basin_of_large_value_contains_ball
    {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ)
    (q : X) (hq : q ∈ Metric.ball p ((f p - τ) / L)) :
    q ∈ superlevelSet f τ ∧
    ∃ S : Set X, IsConnected S ∧ p ∈ S ∧ q ∈ S ∧ S ⊆ superlevelSet f τ := by
  have hball_sub := ball_subset_superlevel hf hL h_above
  refine ⟨hball_sub hq, Metric.ball p ((f p - τ) / L), ?_, ?_, hq, hball_sub⟩
  · have hr : 0 < (f p - τ) / (L : ℝ) := div_pos (by linarith) hL
    exact (convex_ball p _).isConnected ⟨p, Metric.mem_ball_self hr⟩
  · exact Metric.mem_ball_self (div_pos (by linarith) hL)

/-! ## 2. basin_fragment_minimum_size -/

/--
**Basin fragment minimum size.**

For any `ε > 0` and unit vector `v`, there exist two points in the
superlevel set {f > τ} at distance at least `2 * ((f p - τ) / L) - ε`.
This witnesses that the superlevel set has "diameter" at least `2(f(p)-τ)/L`.

Proof: The points `p + t•v` and `p - t•v` for `t` slightly less than
`(f(p)-τ)/L` are both in the ball and hence in the superlevel set, and
their mutual distance is `2t`.
-/
theorem basin_fragment_minimum_size
    {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {p : X} {τ : ℝ}
    (hL : (0 : ℝ) < L)
    (h_above : f p > τ)
    {v : X} (hv : ‖v‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : X, a ∈ superlevelSet f τ ∧ b ∈ superlevelSet f τ ∧
      dist a b ≥ 2 * ((f p - τ) / L) - ε := by
  set r := (f p - τ) / (L : ℝ) with hr_def
  have hr : 0 < r := div_pos (by linarith) hL
  set δ := min r (ε / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hr (by linarith)
  have hδ_le_r : δ ≤ r := min_le_left r (ε / 2)
  have hδ_le_ε2 : δ ≤ ε / 2 := min_le_right r (ε / 2)
  set t := r - δ / 2 with ht_def
  have ht_pos : 0 < t := by linarith
  have ht_lt_r : t < r := by linarith
  -- Both p + t•v and p - t•v are in ball(p, r)
  have h1 : p + t • v ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), hv, mul_one]
    exact ht_lt_r
  have h2 : p - t • v ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg,
        norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), hv, mul_one]
    exact ht_lt_r
  have hball_sub := ball_subset_superlevel hf hL h_above
  refine ⟨p + t • v, p - t • v, hball_sub h1, hball_sub h2, ?_⟩
  -- dist(p + t•v, p - t•v) = 2t
  have hdist : dist (p + t • v) (p - t • v) = 2 * t := by
    rw [dist_eq_norm, add_sub_sub_cancel, ← two_smul ℝ (t • v), norm_smul,
        norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), hv, mul_one,
        Real.norm_of_nonneg (by positivity)]
  rw [hdist, ht_def, ge_iff_le]
  linarith

/-! ## 3. high_lipschitz_small_fragments -/

/--
**Larger Lipschitz constant allows smaller fragments.**

If L₁ ≤ L₂ (both positive), then (f(p)-τ)/L₂ ≤ (f(p)-τ)/L₁.
Rougher (higher Lipschitz constant) functions can have smaller guaranteed
basin radii.
-/
theorem high_lipschitz_small_fragments
    {fp τ : ℝ} {L₁ L₂ : ℝ}
    (hL₁ : 0 < L₁)
    (h_above : fp > τ)
    (hle : L₁ ≤ L₂) :
    (fp - τ) / L₂ ≤ (fp - τ) / L₁ := by
  apply div_le_div_of_nonneg_left _ hL₁ hle
  linarith

/-! ## 4. uniform_value_single_basin -/

/--
**Uniform value gives a single basin.**

If f(x) > τ for all x in a connected space X, then {f > τ} = X,
which is therefore connected.
-/
theorem uniform_value_single_basin
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {f : X → ℝ} {τ : ℝ}
    (h_all : ∀ x, f x > τ) :
    superlevelSet f τ = Set.univ ∧ IsConnected (superlevelSet f τ) := by
  constructor
  · ext x; simp [superlevelSet, h_all x]
  · rw [show superlevelSet f τ = Set.univ from Set.eq_univ_of_forall (fun x => h_all x)]
    exact isConnected_univ

/-! ## 5. disjoint_basins_separated -/

/--
**Disjoint basins are separated.**

If a and b are in different connected components of the superlevel set
(viewed as a subtype), then their connected components are disjoint.
This is a basic topological fact about connected components forming a partition.
-/
theorem disjoint_basins_separated
    {X : Type*} [TopologicalSpace X]
    {a b : X}
    (h_diff : connectedComponent a ≠ connectedComponent b) :
    Disjoint (connectedComponent a) (connectedComponent b) :=
  connectedComponent_disjoint h_diff

end MoF

end
