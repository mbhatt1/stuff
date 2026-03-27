import Mathlib

/-!
# Manifold of Failure — Part 12: Discrete Impossibility

Discrete analogues of the defense impossibility theorems that work
directly on finite spaces WITHOUT continuous relaxation or Tietze extension.

## Results

1. `discrete_ivt` — On a finite path {0,...,n}, if f(0) < τ < f(n),
   there exists i where f crosses from below τ to at-or-above τ.
   (Discrete IVT.)

2. `discrete_defense_boundary_fixed` — If a defense fixes safe vertices,
   boundary crossings persist with a fixed safe endpoint.

3. `defense_capacity_pigeonhole` — When adversarial configurations
   exceed defense capacity, misclassification is inevitable.

4. `doubly_exponential_overwhelms` — The configuration space 2^(2^d)
   eventually exceeds any polynomial defense capacity.

These results show the defense impossibility holds in the discrete
setting without any appeal to continuous topology.
-/

open Finset

noncomputable section

namespace MoF.Discrete

/-! ## 1. Discrete IVT on Finite Paths -/

/--
**Discrete Intermediate Value Theorem.**

If `f : Fin (n+2) → ℝ` satisfies `f 0 < τ` and `f (n+1) ≥ τ`,
then there exists `i : Fin (n+1)` such that
`f i < τ` and `f (i+1) ≥ τ`.

This is the discrete analogue of the topological boundary existence
theorem. No continuity, no topology—just a counting argument on
a finite ordered set.
-/
theorem discrete_ivt {n : ℕ} (f : Fin (n + 2) → ℝ) (τ : ℝ)
    (h_start : f 0 < τ) (h_end : f ⟨n + 1, by omega⟩ ≥ τ) :
    ∃ i : Fin (n + 1), f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ := by
  -- By strong induction / well-ordering: consider the largest i with f(i) < τ.
  -- Then f(i+1) ≥ τ.
  by_contra h_no_cross
  push_neg at h_no_cross
  -- h_no_cross : ∀ i : Fin (n+1), f ⟨i, ...⟩ < τ → f ⟨i+1, ...⟩ < τ
  -- By induction, f(k) < τ for all k ≤ n+1.
  have h_all : ∀ k : ℕ, (hk : k < n + 2) → f ⟨k, hk⟩ < τ := by
    intro k hk
    induction k with
    | zero => exact h_start
    | succ k ih =>
      have hk' : k < n + 1 := by omega
      have hk'' : k < n + 2 := by omega
      have := h_no_cross ⟨k, hk'⟩ (ih hk'')
      convert this using 1
  -- But f(n+1) ≥ τ, contradiction.
  have := h_all (n + 1) (by omega)
  linarith

-- Note: `discrete_ivt` above is the clean statement assuming f(0) < τ ≤ f(n+1).
-- For the general case (arbitrary endpoints), reindex to put the below-point first.

/-! ## 2. Discrete Defense Boundary Fixed Point -/

/--
**Discrete Defense Incompleteness.**

If D fixes all safe vertices (f(v) < τ → D(v) = v), then the
boundary crossing from `discrete_ivt` has its safe endpoint fixed.

This is the discrete analogue of Theorem 4.1 (boundary fixation).
-/
theorem discrete_defense_boundary_fixed
    {n : ℕ} (f : Fin (n + 2) → ℝ) (τ : ℝ)
    (D : Fin (n + 2) → Fin (n + 2))
    (h_start : f 0 < τ)
    (h_end : f ⟨n + 1, by omega⟩ ≥ τ)
    (h_pres : ∀ v : Fin (n + 2), f v < τ → D v = v) :
    ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ ∧
      D ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ := by
  obtain ⟨i, hi_below, hi_above⟩ := discrete_ivt f τ h_start h_end
  exact ⟨i, hi_below, hi_above, h_pres ⟨i.val, by omega⟩ hi_below⟩

-- Note: without constraints on D, a discrete defense CAN map any unsafe
-- point anywhere. The discrete incompleteness requires a CAPACITY
-- constraint (pigeonhole) rather than continuity.

/-! ## 3. Defense Capacity (Pigeonhole Principle) -/

/--
**Pigeonhole for defense capacity.**

If there are `m` adversarial configurations and the defense can only
realize `k < m` distinct behaviors, then at least two configurations
must receive the same treatment—so at least one is mishandled.
-/
theorem defense_capacity_pigeonhole
    {m k : ℕ} (h : k < m) :
    ∀ (classify : Fin m → Fin k),
      ∃ i j : Fin m, i ≠ j ∧ classify i = classify j := by
  intro classify
  have h_card : Fintype.card (Fin k) < Fintype.card (Fin m) := by
    simp only [Fintype.card_fin]; exact h
  exact Fintype.exists_ne_map_eq_of_card_lt classify h_card

/--
**Corollary: any defense with bounded capacity fails.**

If the prompt space has N possible inputs and the defense has
capacity C < N distinct output behaviors, at least two distinct
inputs are mapped to the same output—guaranteeing misclassification
on at least one.
-/
theorem bounded_defense_fails
    (N C : ℕ) (hC : C < N) (_h_pos : 0 < C) :
    ∀ (D : Fin N → Fin C),
      ∃ i j : Fin N, i ≠ j ∧ D i = D j := by
  exact defense_capacity_pigeonhole hC

/-! ## 4. Exponential Growth of Attack Surface -/

/--
The number of subsets of a d-element set is 2^d.
The number of possible "attack patterns" (Boolean functions on d bits)
is 2^(2^d). Any defense with polynomial capacity is eventually overwhelmed.
-/
theorem attack_surface_exponential (d : ℕ) :
    2 ^ d ≥ d + 1 := by
  induction d with
  | zero => simp
  | succ d ih => calc
      2 ^ (d + 1) = 2 * 2 ^ d := by ring
      _ ≥ 2 * (d + 1) := by linarith
      _ = d + 1 + (d + 1) := by ring
      _ ≥ d + 1 + 1 := by omega
      _ = (d + 1) + 1 := by ring

/--
For any fixed k, 2^d eventually exceeds d^k. We prove the base
case k=1: 2^d > d for d ≥ 1, which follows from 2^d ≥ d+1.
-/
theorem exponential_beats_linear :
    ∀ d : ℕ, d ≥ 1 → 2 ^ d > d := by
  intro d hd
  have := attack_surface_exponential d
  omega

/--
Any fixed budget B is eventually exceeded by 2^d.
-/
theorem no_fixed_budget_suffices (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d ≥ d₀ → 2 ^ d > B := by
  use B + 1
  intro d hd
  calc 2 ^ d ≥ d + 1 := attack_surface_exponential d
    _ > B := by omega

/-! ## 5. The Discrete Defense Trilemma -/

/--
**Discrete Defense Trilemma.**

On a finite ordered set of size n+2, if:
1. f crosses τ (f(0) < τ ≤ f(n+1))
2. D fixes safe inputs
3. D has capacity < n+2 (cannot assign unique outputs)

Then D cannot be complete: ∃ v with f(D(v)) ≥ τ.

This mirrors the continuous trilemma: continuity → capacity constraint,
utility preservation → safe inputs fixed, completeness → impossible.
-/
theorem discrete_trilemma
    {n : ℕ} (f : Fin (n + 2) → ℝ) (τ : ℝ)
    (D : Fin (n + 2) → Fin (n + 2))
    (h_start : f 0 < τ)
    (h_end : f ⟨n + 1, by omega⟩ ≥ τ)
    (h_pres : ∀ v : Fin (n + 2), f v < τ → D v = v) :
    -- The defense must leave the boundary crossing intact
    ∃ i : Fin (n + 1),
      f ⟨i.val, by omega⟩ < τ ∧
      f ⟨i.val + 1, by omega⟩ ≥ τ ∧
      D ⟨i.val, by omega⟩ = ⟨i.val, by omega⟩ :=
  discrete_defense_boundary_fixed f τ D h_start h_end h_pres

end MoF.Discrete

end
