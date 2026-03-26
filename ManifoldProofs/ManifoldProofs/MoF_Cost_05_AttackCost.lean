import Mathlib

/-!
# Attack Cost Model: Iterative Convergence Bound + Robustness Radius

We formalize the attack cost model that combines iterative convergence bounds
(from monotone attack sequences) with the Lipschitz robustness radius.  The key
results show:

1. The attacker needs at most ⌈1/δ⌉ steps (finite bound).
2. After n steps the score is at least score₀ + n·δ (linear progress).
3. A threshold τ is exceeded after enough steps.
4. The number of steps to exceed τ from s₀ is at most ⌈(τ - s₀)/δ⌉ + 1.
5. Upon exceeding the threshold the attacker gains a robustness ball.
6. The defender/attacker cost ratio grows exponentially with dimension.
-/

noncomputable section

open Set Filter Topology

namespace MoF

/-! ## 1. Finite steps bound (self-contained) -/

/--
If each step of an attack gains at least δ > 0 in a score bounded by [0,1],
then `n * δ ≤ 1` for all n.  Equivalently the number of useful steps is
at most ⌈1/δ⌉.
-/
theorem attack_cost_upper_bound
    (δ : ℝ) (_hδ : 0 < δ)
    (score : ℕ → ℝ)
    (h_nonneg : ∀ n, 0 ≤ score n)
    (h_le_one : ∀ n, score n ≤ 1)
    (h_step : ∀ n, score n + δ ≤ score (n + 1))
    (n : ℕ) : ↑n * δ ≤ 1 := by
  have h_lower : ∀ k : ℕ, score 0 + ↑k * δ ≤ score k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have : score 0 + ↑(k + 1) * δ = (score 0 + ↑k * δ) + δ := by push_cast; ring
      rw [this]
      linarith [h_step k]
  have := h_lower n
  have := h_le_one n
  have := h_nonneg 0
  linarith

/-! ## 2. Attack value after n steps -/

/--
After n steps with minimum gain δ per step, the attack score is at least
`score₀ + n * δ`.  Proved by induction on n.
-/
theorem attack_value_after_n_steps
    (score₀ δ : ℝ)
    (score : ℕ → ℝ)
    (h_init : score 0 = score₀)
    (h_step : ∀ n, score n + δ ≤ score (n + 1))
    (n : ℕ) : score₀ + ↑n * δ ≤ score n := by
  induction n with
  | zero => simp [h_init]
  | succ n ih =>
    have : score₀ + ↑(n + 1) * δ = (score₀ + ↑n * δ) + δ := by push_cast; ring
    rw [this]
    linarith [h_step n]

/-! ## 3. Attack reaches threshold -/

/--
If `score₀ + n * δ > τ` then after n steps the attack exceeds threshold τ.
-/
theorem attack_reaches_threshold
    (score₀ δ τ : ℝ)
    (score : ℕ → ℝ)
    (h_init : score 0 = score₀)
    (h_step : ∀ n, score n + δ ≤ score (n + 1))
    (n : ℕ)
    (h_exceed : score₀ + ↑n * δ > τ) : score n > τ := by
  have := attack_value_after_n_steps score₀ δ score h_init h_step n
  linarith

/-! ## 4. Steps to threshold -/

/--
If `n ≥ (τ - s₀) / δ + 1` then `s₀ + n * δ > τ`.
So the number of steps to exceed threshold τ from initial score s₀
is at most `⌈(τ - s₀)/δ⌉ + 1`.
-/
theorem steps_to_threshold
    (s₀ τ δ : ℝ) (hδ : 0 < δ)
    (n : ℕ)
    (hn : (τ - s₀) / δ + 1 ≤ ↑n) : s₀ + ↑n * δ > τ := by
  have h1 : (τ - s₀) / δ < ↑n := by linarith
  rw [div_lt_iff₀ hδ, sub_lt_iff_lt_add] at h1
  linarith

/-! ## 5. Total attack cost: effective coverage via robustness ball -/

/--
The effective coverage radius: after reaching AD score `ad > τ` with
Lipschitz constant `L`, the attacker's robustness ball has radius
`(ad - τ) / L`.
-/
def effective_coverage (ad τ L : ℝ) : ℝ := (ad - τ) / L

/--
The effective coverage is positive when `ad > τ` and `L > 0`.
-/
theorem total_attack_cost
    (ad τ L : ℝ) (h_ad : ad > τ) (hL : L > 0) :
    0 < effective_coverage ad τ L := by
  unfold effective_coverage
  exact div_pos (by linarith) hL

/-! ## 6. Attack cost ratio and dimensional scaling -/

/--
The ratio of defender cells N^d to attacker steps 1/δ equals δ * N^d.
-/
theorem attack_cost_ratio
    (N : ℝ) (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    N ^ d / (1 / δ) = δ * N ^ d := by
  field_simp

/--
For N ≥ 2 and fixed δ > 0, the cost ratio δ * N^d → ∞ as d → ∞.
-/
theorem attack_cost_ratio_tends_to_infinity
    {N : ℝ} (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun d => δ * N ^ d) atTop atTop := by
  have hN1 : (1 : ℝ) < N := by linarith
  exact Filter.Tendsto.const_mul_atTop hδ (tendsto_pow_atTop_atTop_of_one_lt hN1)

end MoF
