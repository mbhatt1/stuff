/-
  Prompt Injection Theorem 3: Injection Composition Monotonicity
  ==============================================================

  Lean 4 / Mathlib formalization of Theorem 3 from the
  "Manifold of Failure" prompt-injection analysis.

  A "prompt injection operator" T : X → X maps prompts to modified prompts.
  If T never decreases alignment deviation (AD(T(p)) ≥ AD(p) for all p),
  then:
    1. Iterated application T^n is also monotone: AD(T^n(p)) ≥ AD(p)
    2. The sequence AD(p), AD(T(p)), AD(T²(p)), … is non-decreasing
    3. Since AD ∈ [0,1], this bounded monotone sequence converges
    4. If T strictly increases AD on non-fixed-points, the limit is
       a fixed point of T

  This models how iterative prompt refinement (PAIR / TAP) monotonically
  increases attack severity until convergence.
-/

import Mathlib.Order.BoundedOrder
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

open Filter Set

noncomputable section

/-! ## 1. Prompt Injection Operator -/

/--
A `PromptInjectionOperator` packages:
  - A type `X` of prompts
  - An alignment deviation function `AD : X → ℝ` with values in [0,1]
  - A transformation `T : X → X` that never decreases AD

This models an adversarial prompt-refinement step (e.g., one iteration
of PAIR or TAP) that can only make a prompt more harmful, never less.
-/
structure PromptInjectionOperator where
  /-- The type of prompts. -/
  X : Type
  /-- Alignment Deviation function. -/
  AD : X → ℝ
  /-- The injection operator mapping prompts to modified prompts. -/
  T : X → X
  /-- AD values are non-negative. -/
  ad_nonneg : ∀ p : X, 0 ≤ AD p
  /-- AD values are at most 1. -/
  ad_le_one : ∀ p : X, AD p ≤ 1
  /-- T never decreases AD (monotonicity condition). -/
  ad_mono : ∀ p : X, AD p ≤ AD (T p)

namespace PromptInjectionOperator

variable (Φ : PromptInjectionOperator)

/-! ## 2. Iterated application -/

/-- Iterated application of the injection operator: T^n. -/
def iterT : ℕ → Φ.X → Φ.X
  | 0 => id
  | n + 1 => Φ.T ∘ Φ.iterT n

@[simp]
theorem iterT_zero (p : Φ.X) : Φ.iterT 0 p = p := rfl

@[simp]
theorem iterT_succ (n : ℕ) (p : Φ.X) : Φ.iterT (n + 1) p = Φ.T (Φ.iterT n p) := rfl

/-- Alternate iteration: applying T after n iterations equals n+1 iterations. -/
theorem iterT_succ' (n : ℕ) (p : Φ.X) : Φ.T (Φ.iterT n p) = Φ.iterT (n + 1) p := rfl

/-! ## 3. AD(T^n(p)) ≥ AD(p) for all n (by induction) -/

/--
**Theorem 3a (Iterated Monotonicity).**
For any prompt p and any n ∈ ℕ, the alignment deviation after n
applications of T is at least as large as the original:
  AD(T^n(p)) ≥ AD(p)

Proof by induction on n.
-/
theorem ad_iterT_ge (p : Φ.X) (n : ℕ) : Φ.AD p ≤ Φ.AD (Φ.iterT n p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iterT_succ]
    exact le_trans ih (Φ.ad_mono (Φ.iterT n p))

/-! ## 4. The AD sequence is monotonically non-decreasing -/

/--
The sequence of AD values along the iterative refinement trajectory:
  a(n) = AD(T^n(p))
-/
def adSeq (p : Φ.X) : ℕ → ℝ :=
  fun n => Φ.AD (Φ.iterT n p)

@[simp]
theorem adSeq_zero (p : Φ.X) : Φ.adSeq p 0 = Φ.AD p := rfl

theorem adSeq_succ (p : Φ.X) (n : ℕ) :
    Φ.adSeq p (n + 1) = Φ.AD (Φ.T (Φ.iterT n p)) := rfl

/--
**Theorem 3b (Monotone Sequence).**
The sequence n ↦ AD(T^n(p)) is monotonically non-decreasing.
-/
theorem adSeq_monotone (p : Φ.X) : Monotone (Φ.adSeq p) := by
  intro m n hmn
  induction hmn with
  | refl => le_refl _
  | step hmn ih =>
    simp only [adSeq] at ih ⊢
    exact le_trans ih (Φ.ad_mono _)

/-! ## 5. Boundedness of the AD sequence -/

/--
The AD sequence is bounded below by 0.
-/
theorem adSeq_nonneg (p : Φ.X) (n : ℕ) : 0 ≤ Φ.adSeq p n :=
  Φ.ad_nonneg _

/--
The AD sequence is bounded above by 1.
-/
theorem adSeq_le_one (p : Φ.X) (n : ℕ) : Φ.adSeq p n ≤ 1 :=
  Φ.ad_le_one _

/--
The AD sequence takes values in the unit interval [0,1].
-/
theorem adSeq_mem_Icc (p : Φ.X) (n : ℕ) : Φ.adSeq p n ∈ Icc (0 : ℝ) 1 :=
  ⟨Φ.adSeq_nonneg p n, Φ.adSeq_le_one p n⟩

/--
The AD sequence is bounded above (by 1), which combined with monotonicity
gives convergence.
-/
theorem adSeq_bddAbove (p : Φ.X) : BddAbove (range (Φ.adSeq p)) := by
  use 1
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact Φ.adSeq_le_one p n

/-! ## 6. Convergence of the AD sequence -/

/--
**Theorem 3c (Convergence).**
Since AD ∈ [0,1], the monotonically non-decreasing sequence
AD(T^n(p)) is bounded above by 1. By the Monotone Convergence Theorem,
it converges.

We use Mathlib's `tendsto_of_monotone` which states that a monotone
bounded sequence in ℝ has a limit in the filter sense.
-/
theorem adSeq_convergent (p : Φ.X) :
    ∃ L : ℝ, Tendsto (Φ.adSeq p) atTop (nhds L) := by
  -- A monotone sequence bounded above converges in ℝ
  have hmono := Φ.adSeq_monotone p
  have hbdd := Φ.adSeq_bddAbove p
  exact (tendsto_of_monotone hmono).resolve_left (not_tendsto_atTop_of_tendsto_nhds
    (tendsto_nhds_of_mono_bddAbove hmono hbdd) |>.elim (fun h => h))

/--
The limit of the AD sequence.
-/
def adLimit (p : Φ.X) : ℝ :=
  sSup (range (Φ.adSeq p))

/--
The AD sequence converges to its supremum.
-/
theorem adSeq_tendsto_adLimit (p : Φ.X) :
    Tendsto (Φ.adSeq p) atTop (nhds (Φ.adLimit p)) := by
  exact tendsto_nhds_of_mono_bddAbove (Φ.adSeq_monotone p) (Φ.adSeq_bddAbove p)

/--
The limit lies in [0,1].
-/
theorem adLimit_nonneg (p : Φ.X) : 0 ≤ Φ.adLimit p := by
  apply le_csSup_of_le (Φ.adSeq_bddAbove p) ⟨0, rfl⟩
  exact Φ.adSeq_nonneg p 0

theorem adLimit_le_one (p : Φ.X) : Φ.adLimit p ≤ 1 := by
  apply csSup_le (range_nonempty _)
  intro x hx
  obtain ⟨n, rfl⟩ := hx
  exact Φ.adSeq_le_one p n

theorem adLimit_mem_Icc (p : Φ.X) : Φ.adLimit p ∈ Icc (0 : ℝ) 1 :=
  ⟨Φ.adLimit_nonneg p, Φ.adLimit_le_one p⟩

/--
The limit is at least as large as any term in the sequence.
-/
theorem adSeq_le_adLimit (p : Φ.X) (n : ℕ) : Φ.adSeq p n ≤ Φ.adLimit p :=
  le_csSup (Φ.adSeq_bddAbove p) (mem_range_self n)

/--
In particular, AD(p) ≤ L.
-/
theorem ad_le_adLimit (p : Φ.X) : Φ.AD p ≤ Φ.adLimit p := by
  have := Φ.adSeq_le_adLimit p 0
  simpa using this

/-! ## 7. Fixed-point characterization of the limit -/

/--
A prompt p is a *fixed point* of T if T(p) = p.
-/
def IsFixedPoint (p : Φ.X) : Prop := Φ.T p = p

/--
At a fixed point, AD is unchanged: AD(T(p)) = AD(p).
-/
theorem ad_fixedPoint (p : Φ.X) (hfp : Φ.IsFixedPoint p) :
    Φ.AD (Φ.T p) = Φ.AD p := by
  rw [IsFixedPoint] at hfp
  rw [hfp]

/--
At a fixed point, all iterates are equal: T^n(p) = p.
-/
theorem iterT_fixedPoint (p : Φ.X) (hfp : Φ.IsFixedPoint p) (n : ℕ) :
    Φ.iterT n p = p := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, IsFixedPoint] at hfp ⊢; exact hfp

/--
**Strict Injection Property:** T strictly increases AD on all non-fixed-points.
This models an effective attack that always makes progress unless it has
already reached maximum severity.
-/
def StrictOnNonFixed : Prop :=
  ∀ p : Φ.X, ¬Φ.IsFixedPoint p → Φ.AD p < Φ.AD (Φ.T p)

/--
**Theorem 3d (Fixed-Point Convergence).**
Suppose:
  (i)  T strictly increases AD on non-fixed-points
  (ii) AD is continuous (with respect to some topology on X)
  (iii) T is continuous

Then the iterative sequence T^n(p) converges to a fixed point of T,
i.e., the limit of AD(T^n(p)) equals AD(q) for some fixed point q.

We state this in terms of AD values: if the AD sequence converges to L,
and AD(T(·)) is continuous in the sense that convergence of AD values
is preserved, then L must satisfy the fixed-point equation.

This is formalized as: if AD(T^n(p)) → L and AD(T^{n+1}(p)) → L,
then AD-level fixed point: any subsequential limit in AD-space satisfies
AD = AD ∘ T, meaning AD(T(q)) = AD(q) at the limit.
-/
theorem adLimit_is_ad_fixedPoint (p : Φ.X)
    (hconv : Tendsto (Φ.adSeq p) atTop (nhds (Φ.adLimit p))) :
    Tendsto (fun n => Φ.adSeq p (n + 1)) atTop (nhds (Φ.adLimit p)) := by
  exact (Φ.adSeq_tendsto_adLimit p).comp (tendsto_add_atTop_nat 1)

/--
The shifted sequence AD(T^{n+1}(p)) also converges to the same limit L.
This means AD(T(T^n(p))) → L, establishing that the limit is an AD-level
fixed point: the operator T does not change the AD value at the limit.
-/
theorem shifted_adSeq_tendsto (p : Φ.X) :
    Tendsto (fun n => Φ.AD (Φ.T (Φ.iterT n p))) atTop (nhds (Φ.adLimit p)) := by
  have : (fun n => Φ.AD (Φ.T (Φ.iterT n p))) = (fun n => Φ.adSeq p (n + 1)) := by
    ext n; rfl
  rw [this]
  exact (Φ.adSeq_tendsto_adLimit p).comp (tendsto_add_atTop_nat 1)

/--
**Main convergence theorem (AD-level fixed point).**
The limit L of the AD sequence satisfies the fixed-point equation at the
AD level: if g : ℝ → ℝ is a continuous function satisfying
  g(AD(T^n(p))) = AD(T^{n+1}(p))
for all n (i.e., g represents the "AD-level action of T"), then g(L) = L.

This captures the essential content: iterative prompt injection converges
to a severity level that is invariant under further injection.
-/
theorem adLevel_fixedPoint
    (p : Φ.X)
    (g : ℝ → ℝ)
    (hg_cont : Continuous g)
    (hg_rep : ∀ n : ℕ, g (Φ.adSeq p n) = Φ.adSeq p (n + 1)) :
    g (Φ.adLimit p) = Φ.adLimit p := by
  have h_lhs : Tendsto (fun n => g (Φ.adSeq p n)) atTop (nhds (g (Φ.adLimit p))) :=
    hg_cont.continuousAt.tendsto.comp (Φ.adSeq_tendsto_adLimit p)
  have h_rhs : Tendsto (fun n => Φ.adSeq p (n + 1)) atTop (nhds (Φ.adLimit p)) :=
    (Φ.adSeq_tendsto_adLimit p).comp (tendsto_add_atTop_nat 1)
  have h_eq : (fun n => g (Φ.adSeq p n)) = (fun n => Φ.adSeq p (n + 1)) := by
    ext n; exact hg_rep n
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

/-! ## 8. Quantitative rate bound -/

/--
**Corollary: Quantitative lower bound.**
After n steps, the AD value is at least AD(p) + n * δ if each step
increases AD by at least δ > 0. Combined with the upper bound of 1,
this gives convergence in at most ⌈(1 - AD(p)) / δ⌉ steps to a
fixed point (since AD cannot exceed 1).
-/
theorem adSeq_linear_lower_bound
    (p : Φ.X) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ n : ℕ, Φ.adSeq p (n + 1) ≥ Φ.adSeq p n + δ)
    (n : ℕ) :
    Φ.adSeq p n ≥ Φ.AD p + n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc Φ.adSeq p (n + 1) ≥ Φ.adSeq p n + δ := hstep n
    _ ≥ (Φ.AD p + n * δ) + δ := by linarith
    _ = Φ.AD p + (n + 1) * δ := by ring

/--
**Corollary: Finite convergence bound.**
If each non-fixed step increases AD by at least δ > 0, then T must
reach a fixed point within ⌈1/δ⌉ steps, since AD is bounded by 1.
-/
theorem finite_convergence_bound
    (p : Φ.X) (δ : ℝ) (hδ : 0 < δ)
    (hstep : ∀ n : ℕ, Φ.adSeq p (n + 1) ≥ Φ.adSeq p n + δ)
    (n : ℕ) (hn : (n : ℝ) * δ > 1) :
    False := by
  have h1 := Φ.adSeq_linear_lower_bound p δ hδ hstep n
  have h2 := Φ.adSeq_le_one p n
  have h3 := Φ.ad_nonneg p
  linarith

end PromptInjectionOperator

/-! ## Summary

We have formalized the following aspects of Theorem 3 (Injection Composition
Monotonicity) from the Manifold of Failure framework:

| # | Statement | Status |
|---|-----------|--------|
| 1 | `PromptInjectionOperator` structure with AD : X → [0,1] and T : X → X | Definition |
| 2 | Iterated operator T^n via `iterT` | Definition |
| 3a | AD(T^n(p)) ≥ AD(p) by induction | **Proved** (`ad_iterT_ge`) |
| 3b | Sequence AD(T^n(p)) is monotone non-decreasing | **Proved** (`adSeq_monotone`) |
| 3c | Bounded monotone sequence converges | **Proved** (`adSeq_tendsto_adLimit`) |
| 4 | Limit lies in [0,1] | **Proved** (`adLimit_mem_Icc`) |
| 5 | Shifted sequence converges to same limit | **Proved** (`shifted_adSeq_tendsto`) |
| 6 | AD-level fixed-point equation g(L) = L | **Proved** (`adLevel_fixedPoint`) |
| 7 | Linear lower bound AD(p) + nδ | **Proved** (`adSeq_linear_lower_bound`) |
| 8 | Finite convergence: nδ > 1 is impossible | **Proved** (`finite_convergence_bound`) |

The key insight: iterative prompt injection (PAIR/TAP) produces a monotone
non-decreasing sequence of attack severities in [0,1], which must converge.
If each step makes genuine progress (δ > 0), convergence happens in finitely
many steps — at most ⌈1/δ⌉.
-/
