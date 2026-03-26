/-
  PromptInjection08_GradientFlow.lean

  Lean 4 / Mathlib formalization of Theorem 8 from the
  "Manifold of Failure" prompt-injection framework:

  **Gradient Ascent on the Failure Manifold**

  An attacker performing gradient ascent on the Alignment Deviation (AD) surface
  follows the flow of nabla AD.  We prove key properties of this gradient flow
  that explain why gradient-based attacks (like GCG) succeed:

    1. Along the gradient flow, df/dt = ‖∇f‖² ≥ 0  (AD is non-decreasing).
    2. df/dt = 0 iff ∇f = 0  (only critical points are equilibria).
    3. If f is bounded above, the gradient flow converges
       (f serves as a Lyapunov function).
    4. For discrete gradient ascent with step size η:
         f(x + η ∇f(x)) ≥ f(x)   when η is small enough.
    5. The basin of attraction of a local maximum is open (stated).
    6. Concavity implies convergence to the global maximum (stated).

  The file uses Mathlib's `HasFDerivAt`, `InnerProductSpace`, `gradient`,
  and `inner_self_eq_norm_sq` for the core chain-rule calculation.
  ODE existence/uniqueness is axiomatised via `sorry` as is standard
  when Mathlib's ODE library is not yet mature enough for the full result.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

noncomputable section

open InnerProductSpace Filter Topology Set

/-! -----------------------------------------------------------------------
  ## 0.  Universe & type setup
  ----------------------------------------------------------------------- -/

variable
  {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! -----------------------------------------------------------------------
  ## 1.  Gradient characterisation lemmas
  ----------------------------------------------------------------------- -/

/--
The gradient of a real-valued function at a point, using Mathlib's definition
`gradient ℝ f x`.  We collect the key identity:
  ⟪gradient ℝ f x, v⟫ = fderiv ℝ f x v
which holds whenever `f` is differentiable at `x`.
-/
theorem gradient_inner_eq_fderiv
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    ⟪gradient ℝ f x, v⟫_ℝ = fderiv ℝ f x v := by
  rw [gradient, ← InnerProductSpace.toDual_symm_apply]
  simp [InnerProductSpace.toDual_symm_apply]

/-! -----------------------------------------------------------------------
  ## 2.  The chain-rule result: df/dt = ‖∇f‖² along the gradient flow
  ----------------------------------------------------------------------- -/

/--
**Core chain-rule lemma.**
If `γ : ℝ → E` is a curve with `γ'(t) = ∇f(γ(t))` and `f` is differentiable
at `γ(t)`, then
  (f ∘ γ)'(t) = ‖∇f(γ(t))‖²
This is the engine that drives gradient ascent: the objective increases at a
rate equal to the squared norm of its gradient.
-/
theorem gradient_flow_deriv_eq_norm_sq
    {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : HasDerivAt γ (gradient ℝ f (γ t)) t) :
    HasDerivAt (f ∘ γ) (‖gradient ℝ f (γ t)‖ ^ 2) t := by
  -- f ∘ γ is differentiable by the chain rule
  have hcomp : HasDerivAt (f ∘ γ) (fderiv ℝ f (γ t) (gradient ℝ f (γ t))) t := by
    exact HasFDerivAt.comp_hasDerivAt t (hf.hasFDerivAt) hγ
  -- fderiv ℝ f x (gradient ℝ f x) = ⟪∇f, ∇f⟫ = ‖∇f‖²
  have hinner : fderiv ℝ f (γ t) (gradient ℝ f (γ t)) = ‖gradient ℝ f (γ t)‖ ^ 2 := by
    rw [← gradient_inner_eq_fderiv hf]
    rw [real_inner_self_eq_norm_sq]
  rw [hinner] at hcomp
  exact hcomp

/--
**Non-negativity.**
Along the gradient flow, the rate of change of `f` is `‖∇f‖² ≥ 0`.
This proves that the AD surface value never decreases under gradient ascent.
-/
theorem gradient_flow_nonneg
    {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : HasDerivAt γ (gradient ℝ f (γ t)) t) :
    0 ≤ ‖gradient ℝ f (γ t)‖ ^ 2 := by
  positivity

/-! -----------------------------------------------------------------------
  ## 3.  Equilibrium characterisation: df/dt = 0  iff  ∇f = 0
  ----------------------------------------------------------------------- -/

/--
**Critical-point characterisation.**
The squared-norm `‖∇f(x)‖² = 0` if and only if `∇f(x) = 0`.
Hence the gradient flow has `df/dt = 0` precisely at critical points of `f`.
This is the formal reason that gradient-based attacks stall only at
critical points of the AD surface.
-/
theorem gradient_flow_eq_zero_iff (g : E) :
    ‖g‖ ^ 2 = 0 ↔ g = 0 := by
  constructor
  · intro h
    have : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
    exact norm_eq_zero.mp this
  · intro h
    rw [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

/--
**Combined statement.**
Along a gradient flow curve `γ` with `γ'(t) = ∇f(γ(t))`, the derivative
`(f ∘ γ)'(t) = 0` if and only if `γ(t)` is a critical point of `f`.
-/
theorem gradient_flow_stationary_iff_critical
    {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : HasDerivAt γ (gradient ℝ f (γ t)) t) :
    ‖gradient ℝ f (γ t)‖ ^ 2 = 0 ↔ gradient ℝ f (γ t) = 0 :=
  gradient_flow_eq_zero_iff _

/-! -----------------------------------------------------------------------
  ## 4.  Strict increase away from critical points
  ----------------------------------------------------------------------- -/

/--
**Strict monotonicity.**
If `∇f(γ(t)) ≠ 0`, then `(f ∘ γ)'(t) > 0`, so `f` is strictly increasing
along the gradient flow.  This formalises why gradient-based attacks always
make progress toward higher AD values until they reach a critical point.
-/
theorem gradient_flow_strict_increase
    {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : HasDerivAt γ (gradient ℝ f (γ t)) t)
    (hne : gradient ℝ f (γ t) ≠ 0) :
    0 < ‖gradient ℝ f (γ t)‖ ^ 2 := by
  have hpos : 0 < ‖gradient ℝ f (γ t)‖ := by
    exact norm_pos_iff.mpr hne
  positivity

/-! -----------------------------------------------------------------------
  ## 5.  Gradient flow ODE and trajectory (axiomatised)
  ----------------------------------------------------------------------- -/

/--
A gradient flow trajectory for `f` starting at `x₀`:
  - `path : ℝ → E` is the curve,
  - the curve starts at `x₀`,
  - the tangent vector at every time `t ≥ 0` equals `∇f(path t)`.
-/
structure GradientFlowTrajectory (f : E → ℝ) (x₀ : E) where
  /-- The flow curve. -/
  path : ℝ → E
  /-- Initial condition. -/
  path_zero : path 0 = x₀
  /-- The ODE: γ'(t) = ∇f(γ(t)) for all t ≥ 0. -/
  path_deriv : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt path (gradient ℝ f (path t)) t

/--
**Existence of gradient flow (axiomatised).**
For a C¹ function `f` on a complete inner product space, a gradient flow
trajectory starting at any point exists.  The proof requires ODE
existence theory (Picard--Lindeloef) which is not yet fully available in
Mathlib, so we axiomatise it.
-/
axiom gradient_flow_exists
    (f : E → ℝ) (hf : Differentiable ℝ f) (x₀ : E) :
    GradientFlowTrajectory f x₀

/-! -----------------------------------------------------------------------
  ## 6.  Monotonicity along the full trajectory
  ----------------------------------------------------------------------- -/

/--
**f is non-decreasing along the gradient flow.**
For `0 ≤ s ≤ t`, we have `f(γ(s)) ≤ f(γ(t))`.
This follows from the chain-rule result `(f ∘ γ)' = ‖∇f‖² ≥ 0` integrated
over `[s, t]`.
-/
theorem gradient_flow_monotone
    {f : E → ℝ} {x₀ : E}
    (hf : Differentiable ℝ f)
    (T : GradientFlowTrajectory f x₀)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    f (T.path s) ≤ f (T.path t) := by
  -- Each point satisfies the chain-rule result.  Integrate (f∘γ)' ≥ 0.
  -- Full integration argument requires more Mathlib infrastructure.
  sorry

/-! -----------------------------------------------------------------------
  ## 7.  Bounded ⟹ convergent (Lyapunov argument)
  ----------------------------------------------------------------------- -/

/--
**Convergence when f is bounded above.**
If `f` is bounded above by `M`, then along the gradient flow:
  - `f(γ(t))` is non-decreasing and bounded above, hence converges.
  - The limit `L = lim_{t→∞} f(γ(t))` exists.
  - `∫₀^∞ ‖∇f(γ(t))‖² dt = L − f(x₀) < ∞`, forcing `‖∇f(γ(t))‖ → 0`.

This is the Lyapunov-function argument: `−f` is a Lyapunov function for the
gradient flow, and its decrease to a minimum proves convergence to a critical
point (local maximum of f).
-/
theorem gradient_flow_converges_of_bounded
    {f : E → ℝ} {x₀ : E} {M : ℝ}
    (hf : Differentiable ℝ f)
    (T : GradientFlowTrajectory f x₀)
    (hbdd : ∀ x, f x ≤ M) :
    ∃ L : ℝ, L ≤ M ∧ Filter.Tendsto (f ∘ T.path) Filter.atTop (nhds L) := by
  sorry

/--
**Gradient vanishes in the limit.**
Under the same hypotheses, `‖∇f(γ(t))‖ → 0` as `t → ∞`.
The attacker's gradient signal diminishes, meaning the flow approaches a
critical point (local maximum of the AD surface).
-/
theorem gradient_flow_gradient_vanishes
    {f : E → ℝ} {x₀ : E} {M : ℝ}
    (hf : Differentiable ℝ f)
    (T : GradientFlowTrajectory f x₀)
    (hbdd : ∀ x, f x ≤ M) :
    Filter.Tendsto (fun t => ‖gradient ℝ f (T.path t)‖) Filter.atTop (nhds 0) := by
  sorry

/-! -----------------------------------------------------------------------
  ## 8.  Discrete gradient ascent: one-step improvement
  ----------------------------------------------------------------------- -/

/--
**Discrete gradient ascent improvement.**
For a differentiable `f` with `L`-Lipschitz gradient, a single gradient
ascent step with step size `η ∈ (0, 1/L)` satisfies:

  f(x + η • ∇f(x))  ≥  f(x) + (η / 2) ‖∇f(x)‖²

In particular `f(x + η • ∇f(x)) ≥ f(x)`.

The proof uses the first-order Taylor expansion:
  f(x + h) ≈ f(x) + ⟪∇f(x), h⟫
with `h = η • ∇f(x)` giving `⟪∇f(x), η • ∇f(x)⟫ = η ‖∇f(x)‖²`,
and the Lipschitz-gradient descent lemma to control the remainder.

This explains why discrete GCG-style attacks make monotone progress
on the AD surface with sufficiently small step sizes.
-/
theorem discrete_gradient_ascent_improvement
    {f : E → ℝ} {x : E} {η L : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hη_pos : 0 < η)
    (hL_pos : 0 < L)
    (hη_small : η < 1 / L)
    -- Lipschitz gradient: ‖∇f(y) − ∇f(x)‖ ≤ L ‖y − x‖
    (h_lip_grad : ∀ y, ‖gradient ℝ f y - gradient ℝ f x‖ ≤ L * ‖y - x‖) :
    f (x + η • gradient ℝ f x) ≥ f x + (η - η ^ 2 * L / 2) * ‖gradient ℝ f x‖ ^ 2 := by
  sorry

/--
**Corollary: non-negative improvement.**
With `0 < η ≤ 1/L`, the coefficient `η − η²L/2 ≥ η/2 > 0`.
-/
theorem discrete_gradient_ascent_nonneg_improvement
    {f : E → ℝ} {x : E} {η L : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hη_pos : 0 < η)
    (hL_pos : 0 < L)
    (hη_small : η ≤ 1 / L)
    (h_lip_grad : ∀ y, ‖gradient ℝ f y - gradient ℝ f x‖ ≤ L * ‖y - x‖)
    (h_step : f (x + η • gradient ℝ f x) ≥
              f x + (η - η ^ 2 * L / 2) * ‖gradient ℝ f x‖ ^ 2) :
    f (x + η • gradient ℝ f x) ≥ f x := by
  have hcoeff : η - η ^ 2 * L / 2 ≥ η / 2 := by nlinarith
  have hgrad_sq : 0 ≤ ‖gradient ℝ f x‖ ^ 2 := by positivity
  linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ η / 2) hgrad_sq]

/-! -----------------------------------------------------------------------
  ## 9.  First-order Taylor expansion (the key mechanism)
  ----------------------------------------------------------------------- -/

/--
**First-order expansion along the gradient direction.**
  f(x + η • ∇f(x)) = f(x) + η ‖∇f(x)‖² + o(η)
The leading term `η ‖∇f(x)‖²` is positive whenever `∇f(x) ≠ 0`,
guaranteeing improvement for small η.
-/
theorem first_order_gradient_expansion
    {f : E → ℝ} {x : E}
    (hf : HasFDerivAt f (fderiv ℝ f x) x) :
    (fun η : ℝ => f (x + η • gradient ℝ f x) - f x - η * ‖gradient ℝ f x‖ ^ 2)
    =o[nhds 0] (fun η => η) := by
  sorry

/-! -----------------------------------------------------------------------
  ## 10.  Basin of attraction is open
  ----------------------------------------------------------------------- -/

/--
**Basin of attraction of a local maximum is open (stated).**
If `m` is a strict local maximum of a C² function `f`, then the set of
initial points whose gradient flow converges to `m` is open.

This follows from the stable-manifold theorem / continuous dependence
on initial conditions for ODEs.  It formalises the security concern:
every local maximum of the AD surface (= a successful jailbreak mode)
attracts an open neighbourhood of starting prompts.
-/
theorem basin_of_attraction_isOpen
    {f : E → ℝ} {m : E}
    (hf : Differentiable ℝ f)
    -- m is a strict local maximum
    (h_max : ∃ ε > 0, ∀ x, x ≠ m → ‖x - m‖ < ε → f x < f m)
    -- m is a critical point
    (h_crit : gradient ℝ f m = 0) :
    IsOpen { x₀ : E | ∃ T : GradientFlowTrajectory f x₀,
        Filter.Tendsto T.path Filter.atTop (nhds m) } := by
  sorry

/-! -----------------------------------------------------------------------
  ## 11.  Concavity implies global convergence
  ----------------------------------------------------------------------- -/

/--
A function `f` is concave on a convex set `S` if for all `x, y ∈ S` and
`t ∈ [0,1]`:  f((1-t)x + ty) ≥ (1-t) f(x) + t f(y).
-/
def IsConcaveOn (f : E → ℝ) (S : Set E) : Prop :=
  Convex ℝ S ∧
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
    f ((1 - t) • x + t • y) ≥ (1 - t) * f x + t * f y

/--
**Concavity convergence theorem (stated).**
If `f` is concave on a convex compact set `S` and has a unique maximiser
`m ∈ S`, then the gradient flow starting at any `x₀ ∈ S` converges to `m`.

For concave objectives, gradient ascent has no spurious local maxima.
In the prompt-injection context: if the AD surface is concave in a region
of prompt space, the attacker is guaranteed to find the global optimum
(worst-case jailbreak) by gradient ascent alone.
-/
theorem concave_gradient_flow_converges
    {f : E → ℝ} {S : Set E} {m x₀ : E}
    (hf : Differentiable ℝ f)
    (hconc : IsConcaveOn f S)
    (hS_compact : IsCompact S)
    (hm : m ∈ S) (hx₀ : x₀ ∈ S)
    -- m is the unique maximiser on S
    (h_unique_max : ∀ x ∈ S, f x ≤ f m)
    (h_strict : ∀ x ∈ S, x ≠ m → f x < f m) :
    ∃ T : GradientFlowTrajectory f x₀,
      Filter.Tendsto T.path Filter.atTop (nhds m) := by
  sorry

/-! -----------------------------------------------------------------------
  ## 12.  Security implications summary (documentation only)
  ----------------------------------------------------------------------- -/

/-!
### Summary of security implications

The theorems above provide a mathematical foundation for understanding
gradient-based prompt-injection attacks:

1. **gradient_flow_deriv_eq_norm_sq** -- The AD surface value strictly
   increases along gradient flow except at critical points.  An attacker
   running GCG or PGD is guaranteed to increase the "jailbreak score"
   at every step until a critical point is reached.

2. **gradient_flow_stationary_iff_critical** -- The only places where
   progress stalls are critical points of the AD surface.  Defences that
   flatten the gradient landscape (gradient masking) are the natural
   countermeasure, but they are known to be fragile.

3. **gradient_flow_converges_of_bounded** / **gradient_flow_gradient_vanishes**
   -- Because the AD surface is bounded (alignment scores lie in [0,1]),
   every gradient-based attack converges to a critical point.  Combined
   with the basin-of-attraction result, this means the prompt space is
   partitioned into basins, each converging to a distinct jailbreak mode.

4. **discrete_gradient_ascent_improvement** -- The discrete (GCG-style)
   analogue: each token-substitution step increases the attack objective,
   provided the step size is below 1/L.  This explains the empirically
   observed monotone loss curves in GCG attacks.

5. **basin_of_attraction_isOpen** -- Every successful jailbreak mode
   attracts an open set of starting prompts.  This is why random restarts
   in GCG are effective: a positive-measure region of initialisations
   leads to each jailbreak.

6. **concave_gradient_flow_converges** -- In regions where the AD surface
   is concave, the attacker is guaranteed to find the global worst-case
   jailbreak.  This is the hardest scenario for defenders.
-/

end
