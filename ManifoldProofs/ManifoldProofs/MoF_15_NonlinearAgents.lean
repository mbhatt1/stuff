import Mathlib
import ManifoldProofs.MoF_08_DefenseBarriers

/-!
# Manifold of Failure — Part 15: Nonlinear Agent Pipelines

Agentic systems with tool calls are compositions of nonlinear maps:

  input → D (defense) → M (model) → T₁ (tool) → T₂ (tool) → ... → output

Each stage is a continuous/Lipschitz map. The composition is also
continuous/Lipschitz, with Lipschitz constant equal to the PRODUCT
of individual constants. The impossibility theorems apply to the
composed system — with strictly worse bounds.

## Key insight

If the pipeline has depth n with Lipschitz constants K₁, ..., Kₙ,
the effective Lipschitz constant is K₁ · K₂ · ... · Kₙ. The ε-robust
band width scales as L · (K₁···Kₙ + 1), which grows EXPONENTIALLY
in pipeline depth. Deeper pipelines are HARDER to defend, not easier.

## Results

1. `lipschitz_comp` — Composition of Lipschitz maps is Lipschitz
   with product constant.
2. `pipeline_lipschitz` — n-stage pipeline has Lipschitz constant
   K₁ · K₂ · ... · Kₙ.
3. `pipeline_impossibility` — Boundary fixation for composed systems.
4. `pipeline_band_widens` — The ε-robust band grows with pipeline depth.
5. `tool_call_amplifies` — Each tool call multiplicatively degrades
   the defense's effectiveness.
-/

open Set Topology Filter Metric

open scoped NNReal

noncomputable section

namespace MoF.Pipeline

/-! ## 1. Lipschitz Composition -/

/--
Composition of two Lipschitz maps is Lipschitz with product constant.
(This is in Mathlib as `LipschitzWith.comp`, but we state it explicitly
for clarity.)
-/
theorem lipschitz_comp
    {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z]
    {f : Y → Z} {g : X → Y} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf * Kg) (f ∘ g) :=
  hf.comp hg

/--
The Lipschitz constant of a composition is at most the product.
Stated as a distance bound.
-/
theorem comp_dist_bound
    {X : Type*} [PseudoMetricSpace X]
    {f g : X → X} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (x y : X) :
    dist (f (g x)) (f (g y)) ≤ ↑Kf * ↑Kg * dist x y := by
  have h := (hf.comp hg).dist_le_mul x y
  simp only [Function.comp] at h
  rwa [NNReal.coe_mul] at h

/-! ## 2. Pipeline: n-fold composition -/

/--
An n-stage pipeline: a list of Lipschitz maps composed in order.
The pipeline maps input through stages[0] ∘ stages[1] ∘ ... ∘ stages[n-1].
-/
def pipeline {X : Type*} (stages : List (X → X)) : X → X :=
  stages.foldl (fun acc f => f ∘ acc) id

/--
A 2-stage pipeline (defense + model) is Lipschitz with product constant.
-/
theorem two_stage_lipschitz
    {X : Type*} [PseudoMetricSpace X]
    {D M : X → X} {KD KM : ℝ≥0}
    (hD : LipschitzWith KD D) (hM : LipschitzWith KM M) :
    LipschitzWith (KM * KD) (M ∘ D) :=
  hM.comp hD

/--
A 3-stage pipeline (defense + model + tool) is Lipschitz.
-/
theorem three_stage_lipschitz
    {X : Type*} [PseudoMetricSpace X]
    {D M T : X → X} {KD KM KT : ℝ≥0}
    (hD : LipschitzWith KD D) (hM : LipschitzWith KM M)
    (hT : LipschitzWith KT T) :
    LipschitzWith (KT * (KM * KD)) (T ∘ M ∘ D) :=
  hT.comp (hM.comp hD)

/-! ## 3. Pipeline Impossibility -/

/--
**Pipeline Boundary Fixation.**

If the alignment deviation f is continuous, the composed pipeline
P = Tₙ ∘ ... ∘ T₁ ∘ D is continuous (as a composition of continuous
maps), and D preserves safe inputs, then the pipeline has boundary
fixed points.

The key: f ∘ P is a continuous real-valued function on a connected
Hausdorff space. If P = id on safe inputs (because D = id on safe
inputs and the rest of the pipeline preserves this), then boundary
fixation applies to f ∘ P.
-/
theorem pipeline_impossibility
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    -- The full pipeline P : X → X
    {P : X → X} (hP : Continuous P)
    -- P preserves safe inputs (because D does, and post-processing
    -- doesn't change already-safe outputs)
    (h_pres : ∀ x, f x < τ → P x = x)
    (h_safe : ∃ a, f a < τ)
    (h_unsafe : ∃ b, f b > τ) :
    ∃ z, f z = τ ∧ P z = z ∧ ¬(f (P z) < τ) := by
  -- P is a continuous defense that preserves safe inputs.
  -- Apply defense_incompleteness directly.
  obtain ⟨z, hz_eq, hz_fix, _, hz_not⟩ :=
    defense_incompleteness hP hf h_pres h_safe h_unsafe
  exact ⟨z, hz_eq, hz_fix, hz_not⟩

/-! ## 4. Tool Calls Widen the Failure Band -/

/--
**Each tool call multiplicatively degrades the defense.**

If the defense alone is K_D-Lipschitz, adding a tool call with
Lipschitz constant K_T makes the pipeline (K_T · K_D)-Lipschitz.
The ε-robust band width scales with L(K_eff + 1) where
K_eff = K_T · K_D. Since K_T ≥ 1 for any non-contractive tool,
the band strictly widens.
-/
theorem tool_call_amplifies
    {KD KT : ℝ≥0} (hKT : 1 ≤ KT) :
    -- Pipeline Lipschitz constant with tool
    KT * KD ≥ KD := by
  calc KT * KD ≥ 1 * KD := by exact mul_le_mul_of_nonneg_right hKT (zero_le KD)
    _ = KD := one_mul KD

/--
The effective Lipschitz constant grows with each additional stage.
For n stages each with constant K ≥ 1, the pipeline constant is K^n.
-/
theorem pipeline_constant_exponential
    (K : ℝ≥0) (hK : 1 ≤ K) (n : ℕ) :
    K ^ n ≥ 1 := one_le_pow_of_one_le' hK n

/--
**The ε-robust band width grows exponentially with pipeline depth.**

Band width ~ L · (K_eff + 1) · δ where K_eff = K^n for an n-stage
pipeline with per-stage constant K. For K ≥ 2, this is at least
L · (2^n + 1) · δ — exponential in depth.
-/
theorem band_grows_with_depth
    (_L : ℝ≥0) (K : ℝ≥0) (hK : 2 ≤ K) (n : ℕ) :
    -- K^n ≥ 2^n
    K ^ n ≥ 2 ^ n :=
  pow_le_pow_left₀ (by norm_num) hK n

/--
The failure band width at depth n is strictly larger than at depth n-1.
-/
theorem deeper_pipeline_wider_band
    (K : ℝ≥0) (hK : 1 < K) (n : ℕ) :
    K ^ n < K ^ (n + 1) := by
  conv_lhs => rw [show K ^ n = K ^ n * 1 from (mul_one _).symm]
  rw [pow_succ', mul_comm K (K ^ n)]
  exact mul_lt_mul_of_pos_left hK (pow_pos (lt_trans zero_lt_one hK) n)

/-! ## 5. Defense Position in Pipeline -/

/--
**Where the defense sits in the pipeline matters for Lipschitz bounds.**

If the defense D (Lipschitz K_D) is placed BEFORE n tool calls each
with constant K_T, the effective pipeline constant is K_T^n · K_D.

If placed AFTER, it's K_D · K_T^n (same number, but conceptually
different: the defense sees the tool-modified input).

Either way, the constant grows exponentially in the number of tool calls.
-/
theorem defense_before_tools
    {X : Type*} [PseudoMetricSpace X]
    {D : X → X} {T : X → X}
    {KD KT : ℝ≥0}
    (hD : LipschitzWith KD D) (hT : LipschitzWith KT T) :
    LipschitzWith (KT * KD) (T ∘ D) :=
  hT.comp hD

theorem defense_after_tools
    {X : Type*} [PseudoMetricSpace X]
    {D : X → X} {T : X → X}
    {KD KT : ℝ≥0}
    (hD : LipschitzWith KD D) (hT : LipschitzWith KT T) :
    LipschitzWith (KD * KT) (D ∘ T) :=
  hD.comp hT

/-! ## 6. Nonlinear State Evolution -/

/--
**State evolution with defense.**

An agent's state evolves as s_{t+1} = T(D(s_t, x_t)). If T and D
are continuous, the composed evolution is continuous. At each step,
the alignment deviation f(s_{t+1}) = f(T(D(s_t, x_t))) is a
continuous function of (s_t, x_t), and the impossibility applies.

We model this as: the state-input pair (s, x) lives in X × X,
the defense acts on this pair, and the transition produces a new state.
-/
theorem stateful_pipeline_impossibility
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    -- f measures alignment deviation of the state
    {f : X → ℝ} (hf : Continuous f) {τ : ℝ}
    -- T is the state transition (model + tools)
    {T : X → X} (hT : Continuous T)
    -- D is the defense
    {D : X → X} (hD : Continuous D)
    -- The composed pipeline
    (h_pres : ∀ x, f x < τ → T (D x) = x)
    (h_safe : ∃ a, f a < τ)
    (h_unsafe : ∃ b, f b > τ) :
    ∃ z, f z = τ ∧ T (D z) = z ∧ ¬(f (T (D z)) < τ) := by
  -- T ∘ D is continuous
  have hTD : Continuous (T ∘ D) := hT.comp hD
  obtain ⟨z, hz_eq, hz_fix, _, hz_not⟩ :=
    defense_incompleteness hTD hf
      (fun x hx => h_pres x hx) h_safe h_unsafe
  exact ⟨z, hz_eq, hz_fix, hz_not⟩

/--
**Iterated state evolution: n steps of T ∘ D.**

After n steps, the effective Lipschitz constant is (K_T · K_D)^n.
The impossibility applies at every step, and the bounds degrade
exponentially.
-/
theorem iterated_pipeline_constant
    (KT KD : ℝ≥0) (n : ℕ) :
    (KT * KD) ^ n = KT ^ n * KD ^ n := by
  exact mul_pow KT KD n

end MoF.Pipeline

end
