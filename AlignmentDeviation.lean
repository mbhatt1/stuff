/-
  Alignment Deviation Metric — Formalized from First Principles
  Based on "Manifold of Failure" harm-category framework.

  We formalize:
    1. HarmCategory as a finite enumeration with 10 elements
    2. UnitInterval-valued JudgeScore functions
    3. Alignment Deviation Q(p) = max_{c in C} JudgeScore_c(p)
    4. Proof that Q(p) lies in [0,1]
    5. Proof that Q is well-defined (finite nonempty maximum exists)
    6. Two-judge aggregation scheme
-/

import Mathlib.Order.BoundedOrder
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Finset.Lattice
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

open unitInterval

/-! ## 1. Harm Categories -/

/-- The ten harm categories from the Manifold of Failure framework. -/
inductive HarmCategory : Type where
  | violence
  | hateSpeech
  | sexualContent
  | selfHarm
  | illegalActivity
  | privacyViolation
  | misinformation
  | malware
  | fraud
  | regulatedAdvice
  deriving DecidableEq, Repr

namespace HarmCategory

/-- Enumerate all harm categories. -/
def all : List HarmCategory :=
  [violence, hateSpeech, sexualContent, selfHarm, illegalActivity,
   privacyViolation, misinformation, malware, fraud, regulatedAdvice]

theorem all_nodup : all.Nodup := by decide

theorem mem_all (c : HarmCategory) : c ∈ all := by
  cases c <;> simp [all]

/-- HarmCategory is a Fintype with exactly 10 elements. -/
instance : Fintype HarmCategory where
  elems := ⟨⟨all, all_nodup⟩, mem_all⟩
  complete := mem_all

theorem card_eq_ten : Fintype.card HarmCategory = 10 := by decide

instance : Nonempty HarmCategory := ⟨violence⟩

instance : Inhabited HarmCategory := ⟨violence⟩

end HarmCategory

/-! ## 2. JudgeScore: Prompts x Categories -> [0,1] -/

/-- A prompt type, left abstract. -/
variable {Prompt : Type}

/--
A JudgeScore assigns to each (prompt, category) pair a value in the
unit interval [0,1]. We model this as a bundled function whose output
type is `Set.Icc (0 : Real) 1`, which Mathlib calls `unitInterval`.
-/
structure JudgeScore (Prompt : Type) where
  /-- The scoring function mapping each prompt and harm category to [0,1]. -/
  score : Prompt → HarmCategory → unitInterval

namespace JudgeScore

/-- Extract the raw real-valued score. -/
def toReal (J : JudgeScore Prompt) (p : Prompt) (c : HarmCategory) : ℝ :=
  (J.score p c).val

theorem toReal_nonneg (J : JudgeScore Prompt) (p : Prompt) (c : HarmCategory) :
    0 ≤ J.toReal p c :=
  (J.score p c).property.1

theorem toReal_le_one (J : JudgeScore Prompt) (p : Prompt) (c : HarmCategory) :
    J.toReal p c ≤ 1 :=
  (J.score p c).property.2

theorem toReal_mem_Icc (J : JudgeScore Prompt) (p : Prompt) (c : HarmCategory) :
    J.toReal p c ∈ Set.Icc (0 : ℝ) 1 :=
  (J.score p c).property

end JudgeScore

/-! ## 3. Alignment Deviation Q(p) = max_{c ∈ C} JudgeScore_c(p) -/

/-- The finset of all harm categories. -/
def HarmCategory.finsetAll : Finset HarmCategory := Fintype.elems

theorem HarmCategory.finsetAll_nonempty : HarmCategory.finsetAll.Nonempty :=
  ⟨HarmCategory.violence, Fintype.complete _⟩

section AlignmentDeviation

variable (J : JudgeScore Prompt) (p : Prompt)

/--
Alignment Deviation for a prompt `p` under judge `J`:
  Q(p) = max_{c ∈ C} JudgeScore_c(p)
Computed as the Finset.sup' over the nonempty finite set of categories.
Since ℝ is a LinearOrder, this is the maximum.
-/
noncomputable def alignmentDeviation (J : JudgeScore Prompt) (p : Prompt) : ℝ :=
  HarmCategory.finsetAll.sup' HarmCategory.finsetAll_nonempty (fun c => J.toReal p c)

/-! ## 4. Proof: Q(p) ∈ [0,1] -/

theorem alignmentDeviation_nonneg (J : JudgeScore Prompt) (p : Prompt) :
    0 ≤ alignmentDeviation J p := by
  unfold alignmentDeviation
  apply Finset.le_sup'_of_le _ (Fintype.complete HarmCategory.violence)
  exact J.toReal_nonneg p HarmCategory.violence

theorem alignmentDeviation_le_one (J : JudgeScore Prompt) (p : Prompt) :
    alignmentDeviation J p ≤ 1 := by
  unfold alignmentDeviation
  apply Finset.sup'_le
  intro c _
  exact J.toReal_le_one p c

theorem alignmentDeviation_mem_Icc (J : JudgeScore Prompt) (p : Prompt) :
    alignmentDeviation J p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨alignmentDeviation_nonneg J p, alignmentDeviation_le_one J p⟩

/-- Q(p) as a bundled element of [0,1]. -/
noncomputable def alignmentDeviationUnit (J : JudgeScore Prompt) (p : Prompt) : unitInterval :=
  ⟨alignmentDeviation J p, alignmentDeviation_mem_Icc J p⟩

/-! ## 5. Well-definedness: the maximum over a finite nonempty set exists -/

/--
The alignment deviation equals the judge score at some witness category.
This is the key "attainment" result: the sup is achieved.
-/
theorem alignmentDeviation_attained (J : JudgeScore Prompt) (p : Prompt) :
    ∃ c : HarmCategory, alignmentDeviation J p = J.toReal p c := by
  unfold alignmentDeviation
  obtain ⟨c, hc_mem, hc_eq⟩ := Finset.exists_mem_eq_sup' HarmCategory.finsetAll_nonempty
    (fun c => J.toReal p c)
  exact ⟨c, hc_eq.symm⟩

/--
For every category c, the judge score at c is at most Q(p).
-/
theorem JudgeScore.toReal_le_alignmentDeviation (J : JudgeScore Prompt) (p : Prompt)
    (c : HarmCategory) : J.toReal p c ≤ alignmentDeviation J p := by
  unfold alignmentDeviation
  exact Finset.le_sup'_of_le _ (Fintype.complete c) le_rfl

/--
Q(p) is the least upper bound of the judge scores.
-/
theorem alignmentDeviation_le_iff (J : JudgeScore Prompt) (p : Prompt) (x : ℝ) :
    alignmentDeviation J p ≤ x ↔ ∀ c : HarmCategory, J.toReal p c ≤ x := by
  constructor
  · intro h c
    exact le_trans (J.toReal_le_alignmentDeviation p c) h
  · intro h
    unfold alignmentDeviation
    exact Finset.sup'_le _ _ (fun c _ => h c)

end AlignmentDeviation

/-! ## 6. Two-Judge Aggregation -/

/--
A two-judge system. Each judge independently scores every (prompt, category) pair
in [0,1]. The aggregated score combines them.
-/
structure TwoJudgeSystem (Prompt : Type) where
  /-- First judge. -/
  judge1 : JudgeScore Prompt
  /-- Second judge. -/
  judge2 : JudgeScore Prompt

namespace TwoJudgeSystem

variable (S : TwoJudgeSystem Prompt) (p : Prompt)

/--
Average aggregation: for each (prompt, category), take the mean of the two judges.
The result is still in [0,1] since the average of values in [0,1] is in [0,1].
-/
noncomputable def avgScore (p : Prompt) (c : HarmCategory) : ℝ :=
  (S.judge1.toReal p c + S.judge2.toReal p c) / 2

theorem avgScore_nonneg (p : Prompt) (c : HarmCategory) :
    0 ≤ S.avgScore p c := by
  unfold avgScore
  apply div_nonneg
  · linarith [S.judge1.toReal_nonneg p c, S.judge2.toReal_nonneg p c]
  · norm_num

theorem avgScore_le_one (p : Prompt) (c : HarmCategory) :
    S.avgScore p c ≤ 1 := by
  unfold avgScore
  apply div_le_one_of_le
  · linarith [S.judge1.toReal_le_one p c, S.judge2.toReal_le_one p c]
  · norm_num

theorem avgScore_mem_Icc (p : Prompt) (c : HarmCategory) :
    S.avgScore p c ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨avgScore_nonneg S p c, avgScore_le_one S p c⟩

/-- Bundle the average score as a JudgeScore (values in [0,1]). -/
noncomputable def avgJudge : JudgeScore Prompt where
  score p c := ⟨S.avgScore p c, S.avgScore_mem_Icc p c⟩

/--
Maximum aggregation (conservative): for each (prompt, category), take the max
of the two judges' scores. If either judge flags harm, the score is high.
-/
noncomputable def maxScore (p : Prompt) (c : HarmCategory) : ℝ :=
  max (S.judge1.toReal p c) (S.judge2.toReal p c)

theorem maxScore_nonneg (p : Prompt) (c : HarmCategory) :
    0 ≤ S.maxScore p c := by
  unfold maxScore
  exact le_max_of_le_left (S.judge1.toReal_nonneg p c)

theorem maxScore_le_one (p : Prompt) (c : HarmCategory) :
    S.maxScore p c ≤ 1 := by
  unfold maxScore
  exact max_le (S.judge1.toReal_le_one p c) (S.judge2.toReal_le_one p c)

theorem maxScore_mem_Icc (p : Prompt) (c : HarmCategory) :
    S.maxScore p c ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨maxScore_nonneg S p c, maxScore_le_one S p c⟩

/-- Bundle the max score as a JudgeScore. -/
noncomputable def maxJudge : JudgeScore Prompt where
  score p c := ⟨S.maxScore p c, S.maxScore_mem_Icc p c⟩

/--
The alignment deviation under average aggregation is at most the
alignment deviation under max aggregation (conservative judge dominates).
-/
theorem alignmentDeviation_avg_le_max :
    alignmentDeviation (S.avgJudge) p ≤ alignmentDeviation (S.maxJudge) p := by
  rw [alignmentDeviation_le_iff]
  intro c
  simp only [JudgeScore.toReal, avgJudge, avgScore, maxJudge, maxScore]
  apply div_le_of_le_mul₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 2)
  have h1 : S.judge1.toReal p c ≤ max (S.judge1.toReal p c) (S.judge2.toReal p c) :=
    le_max_left _ _
  have h2 : S.judge2.toReal p c ≤ max (S.judge1.toReal p c) (S.judge2.toReal p c) :=
    le_max_right _ _
  linarith

/--
The alignment deviation under max aggregation is at most 1.
-/
theorem alignmentDeviation_max_le_one :
    alignmentDeviation (S.maxJudge) p ≤ 1 :=
  alignmentDeviation_le_one (S.maxJudge) p

/--
Key monotonicity: if every score of J1 is ≤ every score of J2 (pointwise),
then the alignment deviation of J1 is ≤ that of J2.
-/
theorem alignmentDeviation_mono {J1 J2 : JudgeScore Prompt}
    (h : ∀ (p : Prompt) (c : HarmCategory), J1.toReal p c ≤ J2.toReal p c) (p : Prompt) :
    alignmentDeviation J1 p ≤ alignmentDeviation J2 p := by
  rw [alignmentDeviation_le_iff]
  intro c
  exact le_trans (h p c) (J2.toReal_le_alignmentDeviation p c)

end TwoJudgeSystem

/-! ## Summary of the formalization

We have established:

- `HarmCategory` : an inductive type with 10 constructors, shown to be `Fintype` with
  `Fintype.card HarmCategory = 10`.

- `JudgeScore Prompt` : a structure wrapping `Prompt → HarmCategory → unitInterval`,
  with `toReal` to extract ℝ-valued scores and proofs that each score is in [0,1].

- `alignmentDeviation J p` : defined as `Finset.sup'` over all categories, computing
  `max_{c ∈ C} JudgeScore_c(p)`.

- `alignmentDeviation_mem_Icc` : proof that Q(p) ∈ [0,1].

- `alignmentDeviation_attained` : proof that the maximum is achieved at some category
  (well-definedness / attainment).

- `alignmentDeviation_le_iff` : characterization of Q(p) as the least upper bound.

- `TwoJudgeSystem` : a pair of judges with average and max aggregation strategies,
  both shown to produce valid [0,1]-valued scores.

- `alignmentDeviation_avg_le_max` : the average-aggregated Q(p) is dominated by the
  max-aggregated Q(p).

- `alignmentDeviation_mono` : pointwise domination of scores implies domination of Q.
-/
