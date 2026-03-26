/-
  MoF Cost 06: Defense Cost Model — Exponential Scaling
  =====================================================
  Formalizes the exponential scaling of defense effort in high-dimensional
  spaces. A defender must cover a d-dimensional space with small patches,
  and the number of patches grows exponentially in d, while an attacker
  only needs to find a single vulnerability.

  We prove:
    1. defense_coverage_fraction  — r^d < 1 for 0 < r < 1, d ≥ 1
    2. patches_needed             — α / r^d = (1/r)^d · α
    3. defense_cost_exponential   — (1/r)^d → ∞ as d → ∞ for 0 < r < 1
    4. defense_vs_attack_ratio    — δ · N^d → ∞ as d → ∞ for N ≥ 2, δ > 0
    5. critical_dimension         — ∃ d₀, ∀ d ≥ d₀, defense_cost d > B
    6. asymmetry_grows            — N^d₁ ≤ N^d₂ when d₁ ≤ d₂ and N ≥ 2
-/

import Mathlib

open Filter Topology

namespace MoF

/-! ## 1. defense_coverage_fraction -/

/--
A single defense patch of radius `r` in `d` dimensions covers at most `r^d`
fraction of `[0,1]^d`. For `0 < r < 1` and `d ≥ 1`, we have `r^d < 1`.
-/
theorem defense_coverage_fraction {r : ℝ} {d : ℕ}
    (hr0 : 0 < r) (hr1 : r < 1) (hd : 1 ≤ d) :
    r ^ d < 1 :=
  pow_lt_one₀ hr0.le hr1 (by omega)

/-! ## 2. patches_needed -/

/--
To cover fraction `α` of the space with patches each covering `r^d`,
you need `α / r^d` patches. This equals `(1/r)^d · α`, showing that
the patch count grows as `(1/r)^d` times the desired coverage.
-/
theorem patches_needed {r : ℝ} {d : ℕ} {α : ℝ} :
    α / r ^ d = (1 / r) ^ d * α := by
  rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]

/-! ## 3. defense_cost_exponential -/

/--
The number of patches `(1/r)^d` tends to `∞` as `d → ∞` for `0 < r < 1`.
Since `1/r > 1`, this follows from `tendsto_pow_atTop_atTop_of_one_lt`.
-/
theorem defense_cost_exponential {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun d : ℕ => (1 / r) ^ d) atTop atTop := by
  apply tendsto_pow_atTop_atTop_of_one_lt
  rw [one_div]
  exact one_lt_inv_iff₀.mpr ⟨hr0, hr1⟩

/-! ## 4. defense_vs_attack_ratio -/

/--
The defense-to-attack cost ratio `δ · N^d` tends to `∞` as `d → ∞`
for fixed `N ≥ 2` and `δ > 0`. The attacker pays `1/δ` to find one
flaw, while the defender pays `N^d` to cover all patches.
-/
theorem defense_vs_attack_ratio {N : ℕ} {δ : ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) :
    Tendsto (fun d : ℕ => δ * (N : ℝ) ^ d) atTop atTop := by
  apply Tendsto.const_mul_atTop hδ
  exact tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < N by omega))

/-! ## 5. critical_dimension -/

/--
For any budget `B > 0`, there exists a critical dimension `d₀` such that
the defense cost `(1/r)^d` exceeds `B` for all `d ≥ d₀`. This is the
"budget breaking point" — the dimension beyond which defense is unaffordable.
-/
theorem critical_dimension {r : ℝ} {B : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (_hB : 0 < B) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → B < (1 / r) ^ d := by
  have htend := defense_cost_exponential hr0 hr1
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨d₀, hd₀⟩ := htend (B + 1)
  exact ⟨d₀, fun d hd => lt_of_lt_of_le (by linarith) (hd₀ d hd)⟩

/-! ## 6. asymmetry_grows -/

/--
The defense-to-attack cost ratio is monotonically increasing in dimension:
if `d₁ ≤ d₂` and `N ≥ 2`, then `N^d₁ ≤ N^d₂`. Defense gets strictly
harder as dimensionality increases.
-/
theorem asymmetry_grows {N : ℕ} {d₁ d₂ : ℕ}
    (hN : 2 ≤ N) (hd : d₁ ≤ d₂) :
    (N : ℝ) ^ d₁ ≤ (N : ℝ) ^ d₂ :=
  pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega)) hd

end MoF
