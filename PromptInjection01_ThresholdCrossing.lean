/-
  PromptInjection01_ThresholdCrossing.lean

  Lean 4 / Mathlib formalization of the Injection Threshold Crossing theorem
  from the "Manifold of Failure" framework for prompt injection analysis.

  **Theorem (Injection Threshold Crossing)**:
  If the Alignment Deviation function AD is continuous over the behavioral
  space [0,1]^2, and there exist a safe prompt (AD < τ) and an unsafe prompt
  (AD > τ), then every continuous path connecting them must cross the
  threshold level set {x | AD(x) = τ}.

  This is a topological inevitability result: continuous defenses cannot
  create "gaps" that prevent an attacker from finding the exact threshold.

  We prove:
    1. Main theorem via composition of continuous path with AD, then IVT.
    2. Corollary: the level set L_τ separates safe from unsafe points
       (in the path-connected sense).
    3. Corollary: if the behavioral space is path-connected, then L_τ is
       nonempty whenever both safe and unsafe prompts exist.
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Order.Bounds.Basic

noncomputable section

open Set Topology unitInterval

/-! ## 1. Definitions: AD Surface, Safety Predicates, Level Set -/

/--
The Alignment Deviation surface: a continuous function from the unit square
I × I (the behavioral space) to ℝ.  We use ℝ-valued output so that the
standard IVT applies directly; the range-restriction to [0,1] is handled
by the caller's hypotheses.
-/
structure ADSurfaceR where
  /-- The underlying function on the unit square. -/
  toFun : I × I → ℝ
  /-- Continuity of the surface. -/
  continuous_toFun : Continuous toFun

namespace ADSurfaceR

instance : CoeFun ADSurfaceR (fun _ => I × I → ℝ) :=
  { coe := ADSurfaceR.toFun }

variable (f : ADSurfaceR)

/-- A point is *safe* at threshold τ when the AD value is strictly below τ. -/
def Safe (τ : ℝ) (x : I × I) : Prop := f x < τ

/-- A point is *unsafe* at threshold τ when the AD value is strictly above τ. -/
def Unsafe (τ : ℝ) (x : I × I) : Prop := f x > τ

/-- The level set at threshold τ: where AD equals exactly τ. -/
def levelSetR (τ : ℝ) : Set (I × I) :=
  { x | f x = τ }

/-- The safe region at threshold τ. -/
def safeRegion (τ : ℝ) : Set (I × I) :=
  { x | f x < τ }

/-- The unsafe region at threshold τ. -/
def unsafeRegion (τ : ℝ) : Set (I × I) :=
  { x | f x > τ }

/-! ## 2. Continuous Paths in the Behavioral Space -/

/--
A continuous path in the behavioral space I × I: a continuous function
γ : I → I × I with specified endpoints.
-/
structure BehavioralPath (p_s p_u : I × I) where
  /-- The underlying path function. -/
  toFun : I → I × I
  /-- Continuity of the path. -/
  continuous_toFun : Continuous toFun
  /-- The path starts at the safe prompt. -/
  at_zero : toFun ⟨0, unitInterval.zero_mem⟩ = p_s
  /-- The path ends at the unsafe prompt. -/
  at_one : toFun ⟨1, unitInterval.one_mem⟩ = p_u

/-! ## 3. Main Theorem: Injection Threshold Crossing -/

/--
**Theorem 1 (Injection Threshold Crossing).**
If f is a continuous AD function, p_s is safe (f(p_s) < τ), p_u is unsafe
(f(p_u) > τ), and γ is any continuous path from p_s to p_u, then there
exists a parameter t ∈ [0,1] such that f(γ(t)) = τ.

Proof strategy: The composition f ∘ γ : I → ℝ is continuous. At t=0 it
takes value f(p_s) < τ, at t=1 it takes value f(p_u) > τ. Since I = [0,1]
is connected, its image under f ∘ γ is an interval, hence contains τ.
We use Mathlib's `IsPreconnected.intermediate_value₂` for the core IVT step.
-/
theorem injection_threshold_crossing
    (f : ADSurfaceR)
    (τ : ℝ)
    (p_s p_u : I × I)
    (h_safe : f p_s < τ)
    (h_unsafe : f p_u > τ)
    (γ : BehavioralPath p_s p_u) :
    ∃ t : I, f (γ.toFun t) = τ := by
  -- The composition g = f ∘ γ : I → ℝ is continuous
  set g : I → ℝ := f.toFun ∘ γ.toFun with hg_def
  have hg_cont : Continuous g := f.continuous_toFun.comp γ.continuous_toFun
  -- g(0) < τ and g(1) > τ
  have hg0 : g ⟨0, unitInterval.zero_mem⟩ < τ := by
    simp only [hg_def, Function.comp]
    rw [γ.at_zero]
    exact h_safe
  have hg1 : g ⟨1, unitInterval.one_mem⟩ > τ := by
    simp only [hg_def, Function.comp]
    rw [γ.at_one]
    exact h_unsafe
  -- I is connected, so we can apply IVT
  -- Use the fact that unitInterval is a connected space
  have h_conn : IsPreconnected (Set.univ : Set I) := isPreconnected_univ
  -- g and the constant function τ are continuous
  have h_const : Continuous (fun _ : I => τ) := continuous_const
  -- Apply IsPreconnected.intermediate_value₂ on Set.univ
  have h0_mem : (⟨0, unitInterval.zero_mem⟩ : I) ∈ (Set.univ : Set I) := Set.mem_univ _
  have h1_mem : (⟨1, unitInterval.one_mem⟩ : I) ∈ (Set.univ : Set I) := Set.mem_univ _
  obtain ⟨t, _, ht⟩ := h_conn.intermediate_value₂ h0_mem h1_mem
    hg_cont.continuousOn h_const.continuousOn (le_of_lt hg0) (le_of_lt hg1)
  exact ⟨t, ht⟩

/-! ## 4. Corollary: Level Set Separates Safe from Unsafe Points -/

/--
**Corollary 1 (Level Set Separation).**
The level set L_τ = {x | f(x) = τ} separates every safe point from every
unsafe point in the path-connected sense: every continuous path from a safe
point to an unsafe point must pass through L_τ.
-/
theorem levelSet_separates
    (f : ADSurfaceR)
    (τ : ℝ)
    (p_s p_u : I × I)
    (h_safe : f.Safe τ p_s)
    (h_unsafe : f.Unsafe τ p_u)
    (γ : BehavioralPath p_s p_u) :
    ∃ t : I, γ.toFun t ∈ f.levelSetR τ := by
  obtain ⟨t, ht⟩ := injection_threshold_crossing f τ p_s p_u h_safe h_unsafe γ
  exact ⟨t, ht⟩

/-! ## 5. Corollary: Nonemptiness of Level Set in Path-Connected Spaces -/

/--
**Corollary 2 (Level Set Nonemptiness).**
If the behavioral space I × I is path-connected (which it is, as a convex
subset of ℝ²), and there exist both a safe prompt and an unsafe prompt,
then the level set L_τ is nonempty.

This means: any continuous defense threshold τ that is actually tested
(i.e., some prompts are below it and some above) must have a nonempty
boundary — there is always a prompt achieving exactly the threshold.
-/
theorem levelSetR_nonempty_of_safe_and_unsafe
    (f : ADSurfaceR)
    (τ : ℝ)
    (p_s p_u : I × I)
    (h_safe : f.Safe τ p_s)
    (h_unsafe : f.Unsafe τ p_u)
    (γ : BehavioralPath p_s p_u) :
    (f.levelSetR τ).Nonempty := by
  obtain ⟨t, ht⟩ := levelSet_separates f τ p_s p_u h_safe h_unsafe γ
  exact ⟨γ.toFun t, ht⟩

/--
**Corollary 2' (Path-Connected Variant).**
Since I × I is path-connected, we can always *construct* such a path and
therefore the level set is nonempty whenever safe and unsafe points exist.
We use the fact that I × I, as a product of convex subsets of ℝ, is
path-connected.
-/
theorem levelSetR_nonempty_of_pathConnected
    (f : ADSurfaceR)
    (τ : ℝ)
    (p_s p_u : I × I)
    (h_safe : f.Safe τ p_s)
    (h_unsafe : f.Unsafe τ p_u) :
    (f.levelSetR τ).Nonempty := by
  -- I × I is a connected space (product of connected spaces)
  -- Use the connected IVT directly on the full space
  have h_conn : IsPreconnected (Set.univ : Set (I × I)) := isPreconnected_univ
  have hs_mem : p_s ∈ (Set.univ : Set (I × I)) := Set.mem_univ _
  have hu_mem : p_u ∈ (Set.univ : Set (I × I)) := Set.mem_univ _
  obtain ⟨x, _, hx⟩ := h_conn.intermediate_value₂ hs_mem hu_mem
    f.continuous_toFun.continuousOn continuous_const.continuousOn
    (le_of_lt h_safe) (le_of_lt h_unsafe)
  exact ⟨x, hx⟩

/-! ## 6. Topological Structure of the Level Set -/

/-- The level set is closed (preimage of a closed singleton). -/
theorem levelSetR_isClosed (τ : ℝ) : IsClosed (f.levelSetR τ) :=
  isClosed_eq f.continuous_toFun continuous_const

/-- The level set is compact (closed subset of a compact space). -/
theorem levelSetR_isCompact (τ : ℝ) : IsCompact (f.levelSetR τ) :=
  (f.levelSetR_isClosed τ).isCompact

/-- The safe region is open. -/
theorem safeRegion_isOpen (τ : ℝ) : IsOpen (f.safeRegion τ) :=
  isOpen_lt f.continuous_toFun continuous_const

/-- The unsafe region is open. -/
theorem unsafeRegion_isOpen (τ : ℝ) : IsOpen (f.unsafeRegion τ) :=
  isOpen_lt continuous_const f.continuous_toFun

/--
The behavioral space decomposes into three disjoint parts:
safe region, level set, and unsafe region.
-/
theorem behavioral_space_trichotomy (τ : ℝ) :
    (Set.univ : Set (I × I)) =
      f.safeRegion τ ∪ f.levelSetR τ ∪ f.unsafeRegion τ := by
  ext x
  simp only [safeRegion, levelSetR, unsafeRegion, mem_union, mem_setOf_eq, mem_univ,
    iff_true]
  rcases lt_trichotomy (f x) τ with h | h | h
  · left; left; exact h
  · left; right; exact h
  · right; exact h

/--
The safe and unsafe regions are disjoint.
-/
theorem safe_unsafe_disjoint (τ : ℝ) :
    Disjoint (f.safeRegion τ) (f.unsafeRegion τ) := by
  rw [Set.disjoint_iff]
  intro x ⟨hs, hu⟩
  simp only [safeRegion, unsafeRegion, mem_setOf_eq] at hs hu
  linarith

end ADSurfaceR

/-! ## Summary

We have formalized the following from the "Manifold of Failure" prompt
injection analysis:

| # | Statement | Status |
|---|-----------|--------|
| 1 | AD surface as continuous I × I → ℝ | Definition (`ADSurfaceR`) |
| 2 | Safe / Unsafe predicates | Definitions (`Safe`, `Unsafe`) |
| 3 | Continuous behavioral paths | Definition (`BehavioralPath`) |
| 4 | **Threshold Crossing (IVT)** | **Proved** (`injection_threshold_crossing`) |
| 5 | Level set separates safe from unsafe | **Proved** (`levelSet_separates`) |
| 6 | Level set nonempty (path variant) | **Proved** (`levelSetR_nonempty_of_safe_and_unsafe`) |
| 7 | Level set nonempty (connected variant) | **Proved** (`levelSetR_nonempty_of_pathConnected`) |
| 8 | Level set is closed and compact | **Proved** (`levelSetR_isClosed`, `levelSetR_isCompact`) |
| 9 | Safe/unsafe regions are open | **Proved** (`safeRegion_isOpen`, `unsafeRegion_isOpen`) |
| 10 | Behavioral space trichotomy | **Proved** (`behavioral_space_trichotomy`) |
| 11 | Safe/unsafe disjoint | **Proved** (`safe_unsafe_disjoint`) |

All results are sorry-free.
-/
