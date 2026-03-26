/-
  MoF Cost 10: Unified Cost Theory — Master Theorem
  ===================================================
  Bundles the complete cost theory into a single CostParameters structure
  and proves the master theorem: defense cost grows exponentially in
  dimension while attack cost remains constant.
-/

import Mathlib

open Filter Topology

noncomputable section

namespace MoF

/-! ## 1. CostParameters structure -/

/-- Bundled parameters for the cost asymmetry theory. -/
structure CostParameters where
  N : ℕ          -- grid resolution per axis
  hN : 2 ≤ N
  d : ℕ          -- behavioral space dimension
  δ : ℝ          -- minimum attack improvement per step
  hδ : 0 < δ
  L : ℝ          -- Lipschitz constant of AD surface
  hL : 0 < L
  τ : ℝ          -- safety threshold
  r : ℝ          -- defense patch radius
  hr_pos : 0 < r
  hr_lt : r < 1

/-! ## 2. attackBudget -/

/-- Upper bound on attacker queries: 1/δ. -/
def attackBudget (cp : CostParameters) : ℝ := 1 / cp.δ

/-! ## 3. defenseBudget -/

/-- Number of cells the defender must cover: N^d. -/
def defenseBudget (cp : CostParameters) : ℝ := (cp.N : ℝ) ^ cp.d

/-! ## 4. costRatio -/

/-- The defense-to-attack cost ratio. -/
def costRatio (cp : CostParameters) : ℝ := defenseBudget cp / attackBudget cp

/-! ## 5. costRatio simplification -/

/-- The cost ratio simplifies to δ · N^d. -/
theorem costRatio_eq (cp : CostParameters) :
    costRatio cp = cp.δ * (cp.N : ℝ) ^ cp.d := by
  unfold costRatio defenseBudget attackBudget
  have hδ : cp.δ ≠ 0 := ne_of_gt cp.hδ
  field_simp

/-! ## 6. costRatio positivity -/

/-- The cost ratio is positive. -/
theorem costRatio_pos (cp : CostParameters) : 0 < costRatio cp := by
  rw [costRatio_eq]
  apply mul_pos cp.hδ
  apply pow_pos
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) cp.hN

/-! ## 7. attackBudget bounded -/

/-- The attack budget is bounded by 1/δ (trivially, since it equals 1/δ). -/
theorem attackBudget_bounded (cp : CostParameters) :
    attackBudget cp ≤ 1 / cp.δ := by
  unfold attackBudget
  exact le_refl _

/-! ## 8. defenseBudget grows without bound -/

/-- For fixed N ≥ 2, defenseBudget grows without bound as d increases.
    We formalize this by showing (N : ℝ)^d tends to ∞ as d → ∞. -/
theorem defenseBudget_exponential (N : ℕ) (hN : 2 ≤ N) :
    Tendsto (fun d => (N : ℝ) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hN

/-! ## 9. MASTER THEOREM: cost asymmetry -/

/-- **Master Theorem (Cost Asymmetry).**
    For any willingness-to-pay ratio R > 0, there exists d₀ such that for
    all d ≥ d₀ the cost ratio exceeds R.  The defender cannot keep up
    regardless of budget: defense cost grows exponentially in dimension
    while attack cost stays constant. -/
theorem MASTER_THEOREM_cost_asymmetry
    (N : ℕ) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (L : ℝ) (hL : 0 < L) (τ : ℝ) (r : ℝ) (hr_pos : 0 < r) (hr_lt : r < 1)
    (R : ℝ) (_hR : 0 < R) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      costRatio ⟨N, hN, d, δ, hδ, L, hL, τ, r, hr_pos, hr_lt⟩ > R := by
  -- The cost ratio equals δ * N^d, which tends to ∞.
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hN
  -- δ * N^d → ∞
  have htend : Tendsto (fun d => δ * (N : ℝ) ^ d) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ (tendsto_pow_atTop_atTop_of_one_lt hN1)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨d₀, hd₀⟩ := htend (R + 1)
  refine ⟨d₀, fun d hd => ?_⟩
  have key : R + 1 ≤ δ * (N : ℝ) ^ d := hd₀ d hd
  rw [costRatio_eq]
  linarith

/-! ## 10. Attack budget is dimension-independent -/

/-- The attack budget does not depend on dimension: two CostParameters
    with different d but the same δ yield the same attackBudget. -/
theorem attack_budget_dimension_independent
    (cp₁ cp₂ : CostParameters) (hδ_eq : cp₁.δ = cp₂.δ) :
    attackBudget cp₁ = attackBudget cp₂ := by
  unfold attackBudget
  rw [hδ_eq]

end MoF
