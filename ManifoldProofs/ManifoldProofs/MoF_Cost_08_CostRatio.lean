/-
  MoF Cost 08: Cost Ratio — The Main Cost Theorem
  =================================================
  The defense-to-attack cost ratio grows exponentially in dimension.
  This is the central quantitative result of the cost theory.

  costRatio N d δ = N^d * δ represents the ratio:
    (defender cells = N^d) / (attacker steps = 1/δ) = δ * N^d
-/

import Mathlib

open Filter Topology

namespace MoF

/-! ## 1. Definition of costRatio -/

/-- The defense-to-attack cost ratio: δ · N^d. -/
noncomputable def costRatio (N : ℕ) (d : ℕ) (δ : ℝ) : ℝ :=
  (N : ℝ) ^ d * δ

/-- Definitional unfolding of costRatio. -/
theorem cost_ratio_def (N : ℕ) (d : ℕ) (δ : ℝ) :
    costRatio N d δ = (N : ℝ) ^ d * δ :=
  rfl

/-! ## 2. Positivity -/

/-- costRatio is positive when N ≥ 2, d ≥ 1, δ > 0. -/
theorem cost_ratio_pos {N : ℕ} {d : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (_hd : 1 ≤ d) (hδ : 0 < δ) :
    0 < costRatio N d δ := by
  unfold costRatio
  apply mul_pos
  · apply pow_pos
    exact Nat.ofNat_pos.trans_le (Nat.cast_le.mpr hN)
  · exact hδ

/-! ## 3. Monotonicity in dimension -/

/-- costRatio is monotone non-decreasing in d for N ≥ 2 and δ > 0. -/
theorem cost_ratio_mono_d {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) :
    costRatio N d₁ δ ≤ costRatio N d₂ δ := by
  unfold costRatio
  gcongr
  exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (Nat.ofNat_le_cast.mpr hN)

/-! ## 4. Tends to infinity -/

/-- For fixed N ≥ 2 and δ > 0, costRatio N d δ → ∞ as d → ∞. -/
theorem cost_ratio_tends_to_infinity {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) :
    Tendsto (fun d => costRatio N d δ) atTop atTop := by
  unfold costRatio
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    calc (1 : ℝ) < 2 := by norm_num
    _ ≤ (N : ℝ) := Nat.ofNat_le_cast.mpr hN
  apply Filter.Tendsto.atTop_mul_const hδ
  exact tendsto_pow_atTop_atTop_of_one_lt hN1

/-! ## 5. Exceeds any bound -/

/-- For any bound B > 0, there exists d₀ such that costRatio exceeds B for all d ≥ d₀. -/
theorem cost_ratio_exceeds_any_bound {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (B : ℝ) (_hB : 0 < B) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < costRatio N d δ := by
  have htend := cost_ratio_tends_to_infinity hN hδ
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨d₀, hd₀⟩ := htend (B + 1)
  exact ⟨d₀, fun d hd => lt_of_lt_of_le (by linarith) (hd₀ d hd)⟩

/-! ## 6. Attacker advantage quantified -/

/-- Given any "fairness ratio" R > 0, there exists a dimension where the cost ratio exceeds R.
    The attacker wins in sufficiently high dimension regardless of the defender's willingness
    to overspend. -/
theorem attacker_advantage_quantified {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (R : ℝ) (hR : 0 < R) :
    ∃ d : ℕ, R < costRatio N d δ := by
  obtain ⟨d₀, hd₀⟩ := cost_ratio_exceeds_any_bound hN hδ R hR
  exact ⟨d₀, hd₀ d₀ le_rfl⟩

/-! ## 7. Concrete computation: d = 2, N = 25, δ = 0.01 -/

/-- At d = 2, N = 25, δ = 0.01, the cost ratio is 6.25. -/
theorem two_dimension_ratio :
    costRatio 25 2 0.01 = 6.25 := by
  unfold costRatio
  norm_num

end MoF
