import Mathlib

/-!
  MoF_Adv_05_Convexity.lean
  =========================
  Convexity of vulnerability basins and implications for optimization.

  **Key question: Are basins convex?**
  If yes, gradient ascent on AD finds the global maximum within the basin.

  We prove:
    1. concave_superlevel_convex    — concave f ⟹ strict superlevel sets are convex
    2. convex_basin_connected       — convex basins are connected
    3. convex_basin_path_connected  — convex basins are path-connected
    4. non_concave_can_be_nonconvex — not all basins are convex (sin counterexample)
    5. quasiconcave_superlevel_convex — quasiconcave is the exact characterization
-/

noncomputable section

open Set Real

namespace MoF

/-! ## 1. Concave functions have convex strict superlevel sets -/

/--
If `f` is concave on a convex set `S`, then for every threshold `τ`,
the strict superlevel set `{x ∈ S | τ < f x}` is convex.

This is the key structural result: when the alignment deviation function
is concave, basins (superlevel sets above the attack threshold) are convex,
so gradient ascent finds the global maximum.
-/
theorem concave_superlevel_convex
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ S f) (τ : ℝ) :
    Convex ℝ {x | x ∈ S ∧ τ < f x} :=
  hf.convex_gt τ

/-! ## 2. Convex basins are connected -/

/--
A convex nonempty basin in a topological vector space is connected.
This means there is no way to partition the basin into two disjoint
open nonempty pieces — the unsafe region is "all one piece."
-/
theorem convex_basin_connected
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {B : Set E} (hB : Convex ℝ B) (hne : B.Nonempty) :
    IsConnected B :=
  hB.isConnected hne

/-! ## 3. Convex basins are path-connected -/

/--
A convex nonempty basin is path-connected: any two unsafe points
can be joined by a continuous path lying entirely within the basin.
In particular the straight-line segment `t ↦ (1-t)x + ty` stays in `B`.
-/
theorem convex_basin_path_connected
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {B : Set E} (hB : Convex ℝ B) (hne : B.Nonempty) :
    IsPathConnected B :=
  hB.isPathConnected hne

/-! ## 4. Non-concave functions can have non-convex basins -/

/--
Not every strict superlevel set is convex. We exhibit a concrete
counterexample: `f = sin` with threshold `τ = 0`.

The set `{x : ℝ | sin x > 0}` contains `π/2` and `π/2 + 2π` but
their midpoint `π/2 + π = 3π/2` satisfies `sin(3π/2) = -1 < 0`,
so it is not in the set. Hence `{sin > 0}` is not convex.
-/
theorem non_concave_can_be_nonconvex :
    ¬ Convex ℝ {x : ℝ | Real.sin x > 0} := by
  intro hconv
  -- π/2 is in {sin > 0}
  have h1 : Real.sin (π / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [pi_pos]
    · linarith [pi_pos]
  -- π/2 + 2π is in {sin > 0} since sin(π/2 + 2π) = sin(π/2)
  have h2 : Real.sin (π / 2 + 2 * π) > 0 := by
    rw [sin_add_two_pi]; exact h1
  -- Convexity gives midpoint in the set:
  -- (1/2) • (π/2) + (1/2) • (π/2 + 2π) = π/2 + π
  have hmid : Real.sin (π / 2 + π) > 0 := by
    have step := hconv (show π / 2 ∈ {x : ℝ | Real.sin x > 0} from h1)
             (show π / 2 + 2 * π ∈ {x : ℝ | Real.sin x > 0} from h2)
             (show (0 : ℝ) ≤ 1 / 2 from by norm_num)
             (show (0 : ℝ) ≤ 1 / 2 from by norm_num)
             (show (1 : ℝ) / 2 + 1 / 2 = 1 from by norm_num)
    simp only [mem_setOf_eq, smul_eq_mul] at step
    have : (1 : ℝ) / 2 * (π / 2) + (1 : ℝ) / 2 * (π / 2 + 2 * π) = π / 2 + π := by ring
    rwa [this] at step
  -- sin(π/2 + π) = sin(π + π/2) = -sin(π/2) = -1
  have : Real.sin (π / 2 + π) = -Real.sin (π / 2) := by
    rw [show π / 2 + π = π + π / 2 from by ring]
    rw [sin_add, cos_pi, sin_pi]
    ring
  rw [this] at hmid
  have : Real.sin (π / 2) > 0 := h1
  linarith

/-! ## 5. Quasiconcavity is the exact characterization -/

/--
A function is quasiconcave on `S` if and only if all its superlevel sets
`{x ∈ S | r ≤ f x}` are convex. This is strictly weaker than concavity.

If `f` is quasiconcave, then the strict superlevel sets (basins) are also convex.
This is the most general sufficient condition for basin convexity.
-/
theorem quasiconcave_superlevel_convex
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : QuasiconcaveOn ℝ S f) (τ : ℝ) :
    Convex ℝ {x | x ∈ S ∧ τ < f x} :=
  hf.convex_gt τ

end MoF
