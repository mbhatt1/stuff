/-
  Manifold of Failure — Mutation Operators and Probability Distribution
  Lean 4 formalization (Mathlib-compatible)

  Formalizes:
    1. Mutation strategy enumeration (6 strategies)
    2. Probability mass functions over finite types
    3. The specific mutation probability distribution
    4. Proof that probabilities sum to 1
    5. Semantic interpolation in ℝ^n
    6. Convex combination membership in convex sets
    7. Abstract crossover operator
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

-- ============================================================================
-- § 1. Mutation Strategy Type
-- ============================================================================

/-- The six mutation strategies from the Manifold of Failure framework. -/
inductive MutationStrategy where
  | randomAxisPerturbation
  | paraphrasing
  | entitySubstitution
  | adversarialSuffix
  | crossover
  | semanticInterpolation
  deriving DecidableEq, Repr

namespace MutationStrategy

/-- MutationStrategy is a finite type with exactly 6 inhabitants. -/
instance : Fintype MutationStrategy where
  elems := {randomAxisPerturbation, paraphrasing, entitySubstitution,
            adversarialSuffix, crossover, semanticInterpolation}
  complete := by
    intro x; fin_cases x <;> simp

/-- There are exactly 6 mutation strategies. -/
theorem card_eq : Fintype.card MutationStrategy = 6 := by
  rfl

end MutationStrategy

-- ============================================================================
-- § 2. Probability Mass Function over a Finite Type
-- ============================================================================

/-- A probability mass function over a finite type α.
    Consists of a weight function with non-negativity and summation-to-one. -/
structure PMF (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  sum_one : ∑ x : α, prob x = 1

namespace PMF

variable {α : Type*} [Fintype α]

/-- Every probability in a PMF is at most 1. -/
theorem prob_le_one (p : PMF α) (x : α) : p.prob x ≤ 1 := by
  have h := p.sum_one
  have hle : p.prob x ≤ ∑ y : α, p.prob y := by
    apply Finset.single_le_sum (f := p.prob) (s := Finset.univ)
    · intro i _; exact p.nonneg i
    · exact Finset.mem_univ x
  linarith

/-- The probability of any element lies in [0, 1]. -/
theorem prob_mem_Icc (p : PMF α) (x : α) : p.prob x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨p.nonneg x, p.prob_le_one x⟩

end PMF

-- ============================================================================
-- § 3–4. The Mutation Probability Distribution and Summation Proof
-- ============================================================================

namespace MutationStrategy

/-- The probability assigned to each mutation strategy per the paper:
    Random Axis Perturbation: 50%, Paraphrasing: 10%, Entity Substitution: 10%,
    Adversarial Suffix: 10%, Crossover: 10%, Semantic Interpolation: 10%. -/
def mutationProb : MutationStrategy → ℝ
  | .randomAxisPerturbation => 1 / 2
  | .paraphrasing           => 1 / 10
  | .entitySubstitution     => 1 / 10
  | .adversarialSuffix      => 1 / 10
  | .crossover              => 1 / 10
  | .semanticInterpolation  => 1 / 10

/-- All mutation probabilities are non-negative. -/
theorem mutationProb_nonneg : ∀ s : MutationStrategy, 0 ≤ mutationProb s := by
  intro s; fin_cases s <;> simp [mutationProb] <;> norm_num

/-- The mutation probabilities sum to 1:
    1/2 + 1/10 + 1/10 + 1/10 + 1/10 + 1/10 = 1. -/
theorem mutationProb_sum_one : ∑ s : MutationStrategy, mutationProb s = 1 := by
  simp only [Fintype.sum_fin_eq_sum_range]
  -- Unfold the finite sum over MutationStrategy
  have : (Finset.univ : Finset MutationStrategy) =
    {.randomAxisPerturbation, .paraphrasing, .entitySubstitution,
     .adversarialSuffix, .crossover, .semanticInterpolation} := by
    ext x; simp [Finset.mem_univ]
  rw [Fintype.sum_equiv (Equiv.refl _) (by simp)]
  simp only [Finset.sum_cons, Finset.sum_empty, mutationProb]
  norm_num

/-- The mutation probability distribution as a formal PMF. -/
def mutationPMF : PMF MutationStrategy :=
  { prob := mutationProb
    nonneg := mutationProb_nonneg
    sum_one := mutationProb_sum_one }

/-- Random axis perturbation has the highest probability. -/
theorem rap_dominates (s : MutationStrategy) :
    mutationProb s ≤ mutationProb .randomAxisPerturbation := by
  fin_cases s <;> simp [mutationProb] <;> norm_num

/-- All non-RAP strategies have equal probability 0.1. -/
theorem non_rap_uniform (s : MutationStrategy) (hs : s ≠ .randomAxisPerturbation) :
    mutationProb s = 1 / 10 := by
  fin_cases s <;> simp_all [mutationProb]

end MutationStrategy

-- ============================================================================
-- § 5. Semantic Interpolation in ℝ^n
-- ============================================================================

section SemanticInterpolation

variable {n : ℕ}

/-- Semantic interpolation: given embedding vectors e₁, e₂ ∈ ℝ^n and λ ∈ [0,1],
    produce e_new = λ • e₁ + (1 - λ) • e₂. -/
def semanticInterpolation (λ_ : ℝ) (e₁ e₂ : Fin n → ℝ) : Fin n → ℝ :=
  λ_ • e₁ + (1 - λ_) • e₂

/-- Semantic interpolation is a convex combination (alternative phrasing). -/
theorem semanticInterpolation_eq (λ_ : ℝ) (e₁ e₂ : Fin n → ℝ) :
    semanticInterpolation λ_ e₁ e₂ = fun i => λ_ * e₁ i + (1 - λ_) * e₂ i := by
  ext i
  simp [semanticInterpolation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- When λ = 0, semantic interpolation yields e₂. -/
theorem semanticInterpolation_zero (e₁ e₂ : Fin n → ℝ) :
    semanticInterpolation 0 e₁ e₂ = e₂ := by
  ext i; simp [semanticInterpolation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- When λ = 1, semantic interpolation yields e₁. -/
theorem semanticInterpolation_one (e₁ e₂ : Fin n → ℝ) :
    semanticInterpolation 1 e₁ e₂ = e₁ := by
  ext i; simp [semanticInterpolation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Semantic interpolation at λ = 1/2 yields the midpoint. -/
theorem semanticInterpolation_half (e₁ e₂ : Fin n → ℝ) :
    semanticInterpolation (1 / 2) e₁ e₂ = fun i => (e₁ i + e₂ i) / 2 := by
  ext i
  simp [semanticInterpolation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end SemanticInterpolation

-- ============================================================================
-- § 6. Convex Combination Membership
-- ============================================================================

section ConvexMembership

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If S is a convex set and e₁, e₂ ∈ S, then for any λ ∈ [0,1],
    the interpolation λ • e₁ + (1 - λ) • e₂ ∈ S.
    This guarantees semantic interpolation stays within any convex
    region of the embedding space. -/
theorem convex_semanticInterpolation
    {S : Set E} (hS : Convex ℝ S)
    {e₁ e₂ : E} (h₁ : e₁ ∈ S) (h₂ : e₂ ∈ S)
    {λ_ : ℝ} (hλ₀ : 0 ≤ λ_) (hλ₁ : λ_ ≤ 1) :
    λ_ • e₁ + (1 - λ_) • e₂ ∈ S := by
  have h1λ : 0 ≤ 1 - λ_ := by linarith
  have hsum : λ_ + (1 - λ_) = 1 := by ring
  exact hS h₁ h₂ hλ₀ h1λ hsum

/-- Specialized version for ℝ^n vectors, directly about `semanticInterpolation`. -/
theorem semanticInterpolation_mem_convex
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : Convex ℝ S)
    {e₁ e₂ : Fin n → ℝ} (h₁ : e₁ ∈ S) (h₂ : e₂ ∈ S)
    {λ_ : ℝ} (hλ₀ : 0 ≤ λ_) (hλ₁ : λ_ ≤ 1) :
    semanticInterpolation λ_ e₁ e₂ ∈ S := by
  unfold semanticInterpolation
  exact convex_semanticInterpolation hS h₁ h₂ hλ₀ hλ₁

end ConvexMembership

-- ============================================================================
-- § 7. Abstract Crossover Operator
-- ============================================================================

/-- A crossover operator on a type of prompts.
    Abstractly, crossover takes two parent prompts and produces an offspring.
    We require it to be idempotent (crossing a prompt with itself yields itself). -/
structure CrossoverOp (Prompt : Type*) where
  cross : Prompt → Prompt → Prompt
  idempotent : ∀ p, cross p p = p

/-- A crossover operator that additionally commutes (order of parents doesn't matter). -/
structure SymmetricCrossoverOp (Prompt : Type*) extends CrossoverOp Prompt where
  comm : ∀ p q, cross p q = cross q p

-- ============================================================================
-- § 8. Full Mutation Framework (tying it all together)
-- ============================================================================

/-- The full mutation framework: given a prompt type and an embedding dimension,
    packages together the strategy selection distribution and the operators. -/
structure MutationFramework (Prompt : Type*) (n : ℕ) where
  /-- The probability distribution over mutation strategies. -/
  strategyDist : PMF MutationStrategy
  /-- Embedding map: sends a prompt to a vector in ℝ^n. -/
  embed : Prompt → (Fin n → ℝ)
  /-- Decode an embedding back to a prompt (left inverse of embed on its image). -/
  decode : (Fin n → ℝ) → Prompt
  /-- Random axis perturbation mutator. -/
  perturbAxis : Prompt → Prompt
  /-- Paraphrasing mutator. -/
  paraphrase : Prompt → Prompt
  /-- Entity substitution mutator. -/
  substituteEntity : Prompt → Prompt
  /-- Adversarial suffix mutator. -/
  addSuffix : Prompt → Prompt
  /-- Crossover operator. -/
  crossoverOp : CrossoverOp Prompt
  /-- Interpolation parameter λ ∈ [0,1] for semantic interpolation. -/
  interpParam : ℝ
  interpParam_nonneg : 0 ≤ interpParam
  interpParam_le_one : interpParam ≤ 1

namespace MutationFramework

variable {Prompt : Type*} {n : ℕ} (M : MutationFramework Prompt n)

/-- Apply semantic interpolation via the embedding space. -/
def semanticInterp (p₁ p₂ : Prompt) : Prompt :=
  M.decode (semanticInterpolation M.interpParam (M.embed p₁) (M.embed p₂))

/-- Select and apply a mutation given a strategy. -/
def applyStrategy : MutationStrategy → Prompt → Prompt → Prompt
  | .randomAxisPerturbation, p, _ => M.perturbAxis p
  | .paraphrasing, p, _           => M.paraphrase p
  | .entitySubstitution, p, _     => M.substituteEntity p
  | .adversarialSuffix, p, _      => M.addSuffix p
  | .crossover, p, q              => M.crossoverOp.cross p q
  | .semanticInterpolation, p, q  => M.semanticInterp p q

end MutationFramework

-- ============================================================================
-- § 9. Key Metatheorems
-- ============================================================================

/-- The default mutation framework uses the paper's probability distribution. -/
theorem default_dist_is_paper_dist :
    MutationStrategy.mutationPMF.prob = MutationStrategy.mutationProb :=
  rfl

/-- The probability of selecting RAP is exactly 0.5 (50%). -/
theorem rap_prob_half :
    MutationStrategy.mutationPMF.prob .randomAxisPerturbation = 1 / 2 :=
  rfl

/-- The total probability of all embedding-space operations
    (semantic interpolation only) is 10%. -/
theorem embedding_op_prob :
    MutationStrategy.mutationProb .semanticInterpolation = 1 / 10 :=
  rfl

/-- Semantic interpolation is symmetric in the sense that swapping e₁, e₂
    and replacing λ with 1−λ gives the same result. -/
theorem semanticInterpolation_swap {n : ℕ} (λ_ : ℝ) (e₁ e₂ : Fin n → ℝ) :
    semanticInterpolation λ_ e₁ e₂ = semanticInterpolation (1 - λ_) e₂ e₁ := by
  ext i
  simp [semanticInterpolation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
