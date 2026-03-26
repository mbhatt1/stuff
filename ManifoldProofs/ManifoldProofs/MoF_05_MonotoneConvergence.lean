import Mathlib

/-!
# Manifold of Failure — Part 5: Monotone Convergence of Iterative Attacks

We formalize the observation that iterative attack refinement methods (PAIR, TAP,
MAP-Elites, etc.) produce monotonically non-decreasing score sequences that
converge.  The key insight is that any attack operator which never decreases the
alignment-deviation (AD) score yields a bounded monotone sequence in [0,1],
hence convergent by the monotone convergence theorem.

## Main results

- `AttackOperator` — structure bundling score, operator, bounds, and monotonicity
- `attackSeq` — the AD score sequence after n iterations
- `attackSeq_monotone` — the sequence is monotone non-decreasing
- `attackSeq_bounded` — each term is ≤ 1
- `attackSeq_convergent` — the sequence converges
- `attackSeq_limit_le_one` — the limit is ≤ 1
- `attackSeq_limit_ge_initial` — the limit is ≥ score(x₀)
- `finite_steps_bound` — if each step gains ≥ δ > 0, convergence in ⌈1/δ⌉ steps
-/

open Filter Topology Set Function

noncomputable section

namespace MoF

/-- An attack operator: a type `X`, a score function `score : X → ℝ` taking values
    in `[0, 1]`, an operator `T : X → X`, and proof that `T` never decreases score. -/
structure AttackOperator where
  X : Type
  score : X → ℝ
  T : X → X
  score_nonneg : ∀ x, 0 ≤ score x
  score_le_one : ∀ x, score x ≤ 1
  score_mono : ∀ x, score x ≤ score (T x)

/-- The AD score after `n` iterations of the attack operator starting from `x₀`. -/
def attackSeq (op : AttackOperator) (x₀ : op.X) (n : ℕ) : ℝ :=
  op.score (op.T^[n] x₀)

/-! ## Monotonicity -/

/-- One step of the attack sequence is non-decreasing. -/
private theorem attackSeq_succ_le (op : AttackOperator) (x₀ : op.X) (n : ℕ) :
    attackSeq op x₀ n ≤ attackSeq op x₀ (n + 1) := by
  simp only [attackSeq, Function.iterate_succ']
  exact op.score_mono _

/-- The attack sequence is monotone non-decreasing. -/
theorem attackSeq_monotone (op : AttackOperator) (x₀ : op.X) :
    Monotone (attackSeq op x₀) :=
  monotone_nat_of_le_succ (fun n => attackSeq_succ_le op x₀ n)

/-! ## Boundedness -/

/-- Each term of the attack sequence is at most 1. -/
theorem attackSeq_bounded (op : AttackOperator) (x₀ : op.X) (n : ℕ) :
    attackSeq op x₀ n ≤ 1 :=
  op.score_le_one _

/-- The range of the attack sequence is bounded above. -/
theorem attackSeq_bddAbove (op : AttackOperator) (x₀ : op.X) :
    BddAbove (range (attackSeq op x₀)) := by
  exact ⟨1, fun _ ⟨n, hn⟩ => hn ▸ attackSeq_bounded op x₀ n⟩

/-! ## Convergence -/

/-- The attack sequence converges. -/
theorem attackSeq_convergent (op : AttackOperator) (x₀ : op.X) :
    ∃ L, Tendsto (attackSeq op x₀) atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciSup (attackSeq_monotone op x₀) (attackSeq_bddAbove op x₀)⟩

/-- The limit of the attack sequence is at most 1. -/
theorem attackSeq_limit_le_one (op : AttackOperator) (x₀ : op.X) :
    ∀ L, Tendsto (attackSeq op x₀) atTop (nhds L) → L ≤ 1 := by
  intro L hL
  exact le_of_tendsto hL (Eventually.of_forall (fun n => attackSeq_bounded op x₀ n))

/-- The limit of the attack sequence is at least the initial score. -/
theorem attackSeq_limit_ge_initial (op : AttackOperator) (x₀ : op.X) :
    ∀ L, Tendsto (attackSeq op x₀) atTop (nhds L) → op.score x₀ ≤ L := by
  intro L hL
  exact ge_of_tendsto hL (Eventually.of_forall (fun n => by
    exact (attackSeq_monotone op x₀) (Nat.zero_le n)))

/-! ## Finite convergence under positive step size -/

/-- If each application of `T` increases the score by at least `δ > 0`, then after
    `n` steps the score is at least `n * δ`. -/
theorem score_after_n_steps (op : AttackOperator) (x₀ : op.X)
    (δ : ℝ) (_hδ : 0 < δ)
    (hstep : ∀ x, op.score x + δ ≤ op.score (op.T x)) :
    ∀ n : ℕ, op.score x₀ + n * δ ≤ attackSeq op x₀ n := by
  intro n
  induction n with
  | zero =>
    simp [attackSeq]
  | succ n ih =>
    simp only [attackSeq, Function.iterate_succ']
    have : op.score x₀ + (↑(n + 1)) * δ = (op.score x₀ + ↑n * δ) + δ := by
      push_cast; ring
    rw [this]
    calc (op.score x₀ + ↑n * δ) + δ
        ≤ attackSeq op x₀ n + δ := by linarith
      _ = op.score (op.T^[n] x₀) + δ := by simp [attackSeq]
      _ ≤ op.score (op.T (op.T^[n] x₀)) := hstep _

/-- If each step increases score by at least `δ > 0`, then the score must reach 1
    within `⌈1/δ⌉` steps. Equivalently, `n * δ ≤ 1` for all valid `n`, so there
    can be at most `⌈1/δ⌉` improving steps. -/
theorem finite_steps_bound (op : AttackOperator) (x₀ : op.X)
    (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ x, op.score x + δ ≤ op.score (op.T x))
    (n : ℕ) : ↑n * δ ≤ 1 := by
  have h1 : op.score x₀ + ↑n * δ ≤ attackSeq op x₀ n :=
    score_after_n_steps op x₀ δ hδ hstep n
  have h2 : attackSeq op x₀ n ≤ 1 := attackSeq_bounded op x₀ n
  have h3 : 0 ≤ op.score x₀ := op.score_nonneg x₀
  linarith

end MoF
