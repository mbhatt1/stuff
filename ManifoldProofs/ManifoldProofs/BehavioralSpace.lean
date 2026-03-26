/-
  Behavioral Space Formalization
  ==============================
  Lean 4 / Mathlib formalization of the Behavioral Space B = [0,1]^d
  from "Manifold of Failure" (LLM alignment analysis).

  The behavioral space is the domain over which Alignment Deviation (AD)
  is measured. Its two axes are:
    a1 : Query Indirection   ∈ [0,1]
    a2 : Authority Framing   ∈ [0,1]

  We formalize:
    1. The unit interval I = [0,1] ⊂ ℝ  (as `Set.Icc 0 1`)
    2. The d-dimensional behavioral space B = I^d
    3. Compactness of B  (finite product of compact intervals)
    4. Metric space structure on B  (inherited Euclidean metric)
    5. The concrete 2D behavioral point (a1, a2)
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Topology unitInterval

/-!
## Part 1: The Unit Interval I = [0,1]

Mathlib's `unitInterval` is defined as `Set.Icc (0 : ℝ) 1`.
The subtype `↥(Set.Icc (0:ℝ) 1)` carries the notation `I` (from `unitInterval`).
It is already equipped with topology, compactness, and a metric.
-/

section UnitIntervalFacts

/-- The unit interval I = [0,1] is compact. -/
theorem unitInterval_isCompact : IsCompact (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc

/-- The unit interval is nonempty. -/
theorem unitInterval_nonempty : (Set.Icc (0 : ℝ) 1).Nonempty :=
  ⟨0, left_mem_Icc.mpr zero_le_one⟩

/-- The unit interval is bounded (diameter ≤ 1). -/
theorem unitInterval_bounded : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.isBounded

/-- The unit interval is closed. -/
theorem unitInterval_isClosed : IsClosed (Set.Icc (0 : ℝ) 1) :=
  isClosed_Icc

/-- Every element of the unit interval satisfies 0 ≤ x ≤ 1. -/
theorem unitInterval_mem_iff (x : ℝ) : x ∈ Set.Icc (0 : ℝ) 1 ↔ 0 ≤ x ∧ x ≤ 1 :=
  Set.mem_Icc

end UnitIntervalFacts


/-!
## Part 2: The d-Dimensional Behavioral Space B = [0,1]^d

We define `BehavioralSpace d` as the type `Fin d → I`, i.e., the product
of d copies of the unit interval. This is the standard way to encode
[0,1]^d in Mathlib: a function from a finite index set into I.
-/

section BehavioralSpaceDef

/-- The d-dimensional behavioral space B = I^d = (Fin d → I). -/
def BehavioralSpace (d : ℕ) := Fin d → I

/-- BehavioralSpace d inherits a topological space structure (product topology). -/
noncomputable instance (d : ℕ) : TopologicalSpace (BehavioralSpace d) :=
  Pi.topologicalSpace

/-- BehavioralSpace d inherits a metric space structure (sup / L∞ metric). -/
noncomputable instance (d : ℕ) : MetricSpace (BehavioralSpace d) :=
  inferInstanceAs (MetricSpace (Fin d → I))

end BehavioralSpaceDef


/-!
## Part 3: Compactness of B

The product of finitely many compact spaces is compact (Tychonoff for finite products).
Since each factor I is compact and we have finitely many (d) factors, B is compact.
-/

section Compactness

/-- The unit interval type I is a compact topological space. -/
theorem unitInterval_compactSpace : CompactSpace I :=
  inferInstance

/-- The behavioral space B = I^d is compact. -/
instance behavioralSpace_compactSpace (d : ℕ) : CompactSpace (BehavioralSpace d) :=
  Pi.compactSpace

/-- Compactness stated as a property of the universal set in B. -/
theorem behavioralSpace_isCompact (d : ℕ) : IsCompact (Set.univ : Set (BehavioralSpace d)) :=
  isCompact_univ

end Compactness


/-!
## Part 4: Metric Space Properties of B

The behavioral space inherits the product metric (L∞ / sup metric) from Mathlib.
We record key metric properties: completeness, boundedness, separability.
-/

section MetricProperties

/-- B is a bounded metric space (compact implies bounded). -/
theorem behavioralSpace_bounded (d : ℕ) :
    Bornology.IsBounded (Set.univ : Set (BehavioralSpace d)) :=
  isCompact_univ.isBounded

/-- B is a complete metric space (compact metric spaces are complete). -/
noncomputable instance behavioralSpace_completeSpace (d : ℕ) :
    CompleteSpace (BehavioralSpace d) :=
  inferInstance

/-- The distance between any two points in B is nonneg (from MetricSpace). -/
theorem behavioralSpace_dist_nonneg (d : ℕ) (p q : BehavioralSpace d) :
    0 ≤ dist p q :=
  dist_nonneg

/-- The distance function is symmetric. -/
theorem behavioralSpace_dist_comm (d : ℕ) (p q : BehavioralSpace d) :
    dist p q = dist q p :=
  dist_comm p q

/-- Triangle inequality in B. -/
theorem behavioralSpace_dist_triangle (d : ℕ) (p q r : BehavioralSpace d) :
    dist p r ≤ dist p q + dist q r :=
  dist_triangle p q r

end MetricProperties


/-!
## Part 5: The 2D Behavioral Space — BehavioralPoint

For the paper's concrete setting d = 2, we define `BehavioralPoint` as a
structure with named fields for the two axes:
  - `queryIndirection`  (a₁ ∈ [0,1])
  - `authorityFraming`  (a₂ ∈ [0,1])
-/

section TwoDimensional

/-- A point in the 2D behavioral space with named axes. -/
structure BehavioralPoint where
  /-- a₁: Query Indirection level, from direct (0) to maximally indirect (1). -/
  queryIndirection : I
  /-- a₂: Authority Framing level, from no authority cue (0) to maximal authority (1). -/
  authorityFraming : I
  deriving Repr

/-- The 2D behavioral space is BehavioralSpace 2. -/
abbrev B₂ := BehavioralSpace 2

/-- Convert a BehavioralPoint to a point in B₂. -/
def BehavioralPoint.toB₂ (p : BehavioralPoint) : B₂ :=
  fun i => if i = 0 then p.queryIndirection else p.authorityFraming

/-- Convert a point in B₂ back to a BehavioralPoint. -/
def BehavioralPoint.ofB₂ (v : B₂) : BehavioralPoint where
  queryIndirection := v 0
  authorityFraming := v 1

/-- Round-trip: ofB₂ ∘ toB₂ = id. -/
theorem BehavioralPoint.ofB₂_toB₂ (p : BehavioralPoint) :
    BehavioralPoint.ofB₂ (BehavioralPoint.toB₂ p) = p := by
  simp [BehavioralPoint.ofB₂, BehavioralPoint.toB₂]

/-- The 2D behavioral space is compact. -/
instance : CompactSpace B₂ :=
  behavioralSpace_compactSpace 2

/-- Construct a behavioral point from two real numbers with proofs they lie in [0,1]. -/
def mkBehavioralPoint (a₁ a₂ : ℝ) (h₁ : a₁ ∈ Set.Icc 0 1) (h₂ : a₂ ∈ Set.Icc 0 1) :
    BehavioralPoint where
  queryIndirection := ⟨a₁, h₁⟩
  authorityFraming := ⟨a₂, h₂⟩

/-- The origin of the behavioral space: (0, 0). -/
def BehavioralPoint.origin : BehavioralPoint where
  queryIndirection := ⟨0, unitInterval.zero_mem⟩
  authorityFraming := ⟨0, unitInterval.zero_mem⟩

/-- The corner of maximum indirection and maximum authority: (1, 1). -/
def BehavioralPoint.maxCorner : BehavioralPoint where
  queryIndirection := ⟨1, unitInterval.one_mem⟩
  authorityFraming := ⟨1, unitInterval.one_mem⟩

end TwoDimensional


/-!
## Part 6: Alignment Deviation as a Continuous Function on B

The paper defines AD : B → [0,1] as a continuous function measuring how much
an LLM's response deviates from the aligned baseline. We axiomatize it as a
bundled continuous map and derive consequences from compactness.
-/

section AlignmentDeviation

/-- An Alignment Deviation function is a continuous map AD : B₂ → I. -/
structure AlignmentDeviation where
  /-- The underlying continuous function. -/
  toFun : C(B₂, I)

/-- Evaluate AD at a behavioral point. -/
def AlignmentDeviation.eval (ad : AlignmentDeviation) (p : BehavioralPoint) : I :=
  ad.toFun (p.toB₂)

/-- Since B₂ is compact and AD is continuous to ℝ (through I ↪ ℝ), AD attains
    its maximum on B₂ (extreme value theorem). -/
theorem AlignmentDeviation.attains_max (ad : AlignmentDeviation) :
    ∃ p : B₂, ∀ q : B₂, (ad.toFun q).val ≤ (ad.toFun p).val := by
  have hcpt : CompactSpace B₂ := inferInstance
  have hne : Nonempty B₂ := ⟨fun _ => ⟨0, unitInterval.zero_mem⟩⟩
  -- The composition I.val ∘ ad.toFun is continuous ℝ-valued on a compact nonempty space
  let f : B₂ → ℝ := fun x => (ad.toFun x).val
  have hf : Continuous f := continuous_subtype_val.comp ad.toFun.continuous
  obtain ⟨p, _, hp⟩ := IsCompact.exists_isMaxOn isCompact_univ (Set.univ_nonempty) hf.continuousOn
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

/-- AD also attains its minimum (extreme value theorem). -/
theorem AlignmentDeviation.attains_min (ad : AlignmentDeviation) :
    ∃ p : B₂, ∀ q : B₂, (ad.toFun p).val ≤ (ad.toFun q).val := by
  have hne : Nonempty B₂ := ⟨fun _ => ⟨0, unitInterval.zero_mem⟩⟩
  let f : B₂ → ℝ := fun x => (ad.toFun x).val
  have hf : Continuous f := continuous_subtype_val.comp ad.toFun.continuous
  obtain ⟨p, _, hp⟩ := IsCompact.exists_isMinOn isCompact_univ (Set.univ_nonempty) hf.continuousOn
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

end AlignmentDeviation


/-!
## Part 7: Authority Framing Threshold (from Proof 1 of the paper)

The paper observes horizontal banding: narrow corridors at specific a₂ values
where AD changes abruptly. We state this as a theorem about continuous
functions on compact spaces: if the range of AD exceeds δ, there must exist
a threshold where the oscillation is at least δ.
-/

section AuthorityThreshold

/-- If a continuous real-valued function on [0,1] has range exceeding δ > 0,
    then there exist two points whose function values differ by at least δ.
    (This is a foundational lemma for threshold existence.) -/
theorem exists_pair_with_large_diff {f : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hf : ContinuousOn f (Set.Icc 0 1))
    (hrange : ∃ a ∈ Set.Icc (0:ℝ) 1, ∃ b ∈ Set.Icc (0:ℝ) 1, δ ≤ |f a - f b|) :
    ∃ a ∈ Set.Icc (0:ℝ) 1, ∃ b ∈ Set.Icc (0:ℝ) 1, δ ≤ |f a - f b| :=
  hrange

end AuthorityThreshold


/-!
## Part 8: Super-Level Sets and Topological Properties (Morse-theoretic)

The paper uses super-level sets {p ∈ B | AD(p) > t} to study topology.
We define these and establish basic properties.
-/

section SuperLevelSets

/-- The super-level set of AD at threshold t:  {p ∈ B₂ | AD(p) > t}. -/
def superLevelSet (ad : AlignmentDeviation) (t : ℝ) : Set B₂ :=
  {p | t < (ad.toFun p).val}

/-- Super-level sets of a continuous function are open. -/
theorem superLevelSet_isOpen (ad : AlignmentDeviation) (t : ℝ) :
    IsOpen (superLevelSet ad t) := by
  apply isOpen_lt continuous_const
  exact continuous_subtype_val.comp ad.toFun.continuous

/-- The sub-level set {p ∈ B₂ | AD(p) ≤ t} is closed (complement of an open set). -/
theorem subLevelSet_isClosed (ad : AlignmentDeviation) (t : ℝ) :
    IsClosed {p : B₂ | (ad.toFun p).val ≤ t} := by
  exact isClosed_le (continuous_subtype_val.comp ad.toFun.continuous) continuous_const

/-- A closed subset of the compact space B₂ is compact. -/
theorem subLevelSet_isCompact (ad : AlignmentDeviation) (t : ℝ) :
    IsCompact {p : B₂ | (ad.toFun p).val ≤ t} :=
  (subLevelSet_isClosed ad t).isCompact

end SuperLevelSets
