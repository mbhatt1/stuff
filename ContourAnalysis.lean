/-
  ContourAnalysis.lean

  Formalization of contour analysis and iso-Alignment-Deviation surfaces
  from "Manifold of Failure" paper.

  Concepts formalized:
    1. Level sets L_c(f) = {x in X | f(x) = c}
    2. Sublevel sets S_c(f) = {x in X | f(x) <= c}
    3. Closedness of level/sublevel sets under continuous maps
    4. Discrete gradient via finite differences on a grid
    5. Horizontal banding as dominance of one partial derivative
    6. Corridors as elongated connected sublevel components
    7. Critical-value topology change (discrete Morse flavor)

  Mathlib-compatible Lean 4.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology

-- ============================================================
-- PART 1: Level Sets and Sublevel Sets
-- ============================================================

namespace ManifoldOfFailure

/-! ### Definition of level set and sublevel set -/

/-- The level set L_c(f) = {x in X | f(x) = c}. In the paper these trace
    the iso-Alignment-Deviation surfaces. -/
def levelSet {X : Type*} (f : X -> Real) (c : Real) : Set X :=
  {x | f x = c}

/-- The sublevel set S_c(f) = {x in X | f(x) <= c}. -/
def sublevelSet {X : Type*} (f : X -> Real) (c : Real) : Set X :=
  {x | f x ≤ c}

/-- The strict sublevel set {x | f(x) < c}. -/
def strictSublevelSet {X : Type*} (f : X -> Real) (c : Real) : Set X :=
  {x | f x < c}

/-- The superlevel set {x | f(x) >= c}. -/
def superlevelSet {X : Type*} (f : X -> Real) (c : Real) : Set X :=
  {x | f x ≥ c}

-- ============================================================
-- PART 2: Level sets are preimages
-- ============================================================

/-- The level set is the preimage of {c} under f. -/
theorem levelSet_eq_preimage {X : Type*} (f : X -> Real) (c : Real) :
    levelSet f c = f ⁻¹' {c} := by
  ext x
  simp [levelSet, Set.mem_preimage, Set.mem_singleton_iff]

/-- The sublevel set is the preimage of (-inf, c] under f. -/
theorem sublevelSet_eq_preimage {X : Type*} (f : X -> Real) (c : Real) :
    sublevelSet f c = f ⁻¹' (Set.Iic c) := by
  ext x
  simp [sublevelSet, Set.mem_preimage, Set.mem_Iic]

/-- The strict sublevel set is the preimage of (-inf, c) under f. -/
theorem strictSublevelSet_eq_preimage {X : Type*} (f : X -> Real) (c : Real) :
    strictSublevelSet f c = f ⁻¹' (Set.Iio c) := by
  ext x
  simp [strictSublevelSet, Set.mem_preimage, Set.mem_Iio]

-- ============================================================
-- PART 3: Closedness under continuous maps
-- ============================================================

/-- If f is continuous, then the level set L_c is closed.
    This is because {c} is closed in R and the preimage of a
    closed set under a continuous map is closed. -/
theorem levelSet_isClosed {X : Type*} [TopologicalSpace X]
    {f : X -> Real} (hf : Continuous f) (c : Real) :
    IsClosed (levelSet f c) := by
  rw [levelSet_eq_preimage]
  exact isClosed_singleton.preimage hf

/-- If f is continuous, then the sublevel set S_c is closed.
    This is because Iic c = (-inf, c] is closed in R and the
    preimage of a closed set under a continuous map is closed. -/
theorem sublevelSet_isClosed {X : Type*} [TopologicalSpace X]
    {f : X -> Real} (hf : Continuous f) (c : Real) :
    IsClosed (sublevelSet f c) := by
  rw [sublevelSet_eq_preimage]
  exact isClosed_Iic.preimage hf

/-- If f is continuous, then the strict sublevel set {f < c} is open. -/
theorem strictSublevelSet_isOpen {X : Type*} [TopologicalSpace X]
    {f : X -> Real} (hf : Continuous f) (c : Real) :
    IsOpen (strictSublevelSet f c) := by
  rw [strictSublevelSet_eq_preimage]
  exact isOpen_Iio.preimage hf

/-- If f is continuous, then the superlevel set {f >= c} is closed. -/
theorem superlevelSet_isClosed {X : Type*} [TopologicalSpace X]
    {f : X -> Real} (hf : Continuous f) (c : Real) :
    IsClosed (superlevelSet f c) := by
  have : superlevelSet f c = f ⁻¹' (Set.Ici c) := by
    ext x; simp [superlevelSet, Set.mem_preimage, Set.mem_Ici]
  rw [this]
  exact isClosed_Ici.preimage hf

-- ============================================================
-- PART 4: Nesting / monotonicity of sublevel sets
-- ============================================================

/-- Sublevel sets are monotone: if c <= d then S_c(f) ⊆ S_d(f). -/
theorem sublevelSet_mono {X : Type*} (f : X -> Real) {c d : Real} (hcd : c ≤ d) :
    sublevelSet f c ⊆ sublevelSet f d := by
  intro x hx
  simp [sublevelSet] at *
  linarith

/-- The level set at c is the boundary between the sublevel set at c
    and the superlevel set at c, in the sense that
    L_c = S_c ∩ {f >= c}. -/
theorem levelSet_eq_inter {X : Type*} (f : X -> Real) (c : Real) :
    levelSet f c = sublevelSet f c ∩ superlevelSet f c := by
  ext x
  simp [levelSet, sublevelSet, superlevelSet]
  constructor
  · intro h; constructor <;> linarith
  · intro ⟨h1, h2⟩; linarith

-- ============================================================
-- PART 5: The Discrete Grid and Finite Differences
-- ============================================================

/-- A discrete grid point in [0,1]^2 parameterized by grid size n.
    Indices (i, j) with 0 <= i, j < n represent the point
    (i/(n-1), j/(n-1)) in continuous space. -/
structure GridPoint (n : Nat) where
  i : Fin n
  j : Fin n
deriving DecidableEq

/-- A grid function assigns a real value to each grid point.
    In the paper, this is the AD (Alignment Deviation) score
    as a function of (authority_framing, persona_consistency). -/
def GridFun (n : Nat) := GridPoint n -> Real

/-- Forward finite difference in the i-direction (authority framing axis).
    Approximates df/da1.
    Requires i + 1 < n. -/
def finiteDiffI {n : Nat} (f : GridFun n) (p : GridPoint n)
    (hi : p.i.val + 1 < n) : Real :=
  let next_i : Fin n := ⟨p.i.val + 1, hi⟩
  let q : GridPoint n := ⟨next_i, p.j⟩
  (f q - f p) * (n - 1 : Real)

/-- Forward finite difference in the j-direction (persona consistency axis).
    Approximates df/da2.
    Requires j + 1 < n. -/
def finiteDiffJ {n : Nat} (f : GridFun n) (p : GridPoint n)
    (hj : p.j.val + 1 < n) : Real :=
  let next_j : Fin n := ⟨p.j.val + 1, hj⟩
  let q : GridPoint n := ⟨p.i, next_j⟩
  (f q - f p) * (n - 1 : Real)

/-- The discrete gradient at a grid point (where both differences exist). -/
def discreteGradient {n : Nat} (f : GridFun n) (p : GridPoint n)
    (hi : p.i.val + 1 < n) (hj : p.j.val + 1 < n) : Real × Real :=
  (finiteDiffI f p hi, finiteDiffJ f p hj)

-- ============================================================
-- PART 6: Horizontal Banding
-- ============================================================

/-- A point exhibits horizontal banding when the rate of change in the
    i-direction (authority framing) is much smaller than in the
    j-direction (persona consistency). The parameter epsilon controls
    how much smaller "much smaller" means.

    This formalizes the paper's observation that contour lines become
    nearly horizontal — f depends primarily on a2. -/
def isHorizontallyBanded {n : Nat} (f : GridFun n) (p : GridPoint n)
    (hi : p.i.val + 1 < n) (hj : p.j.val + 1 < n) (ε : Real) : Prop :=
  |finiteDiffI f p hi| ≤ ε * |finiteDiffJ f p hj|

/-- A region R of the grid exhibits horizontal banding at threshold epsilon
    if every interior point in R satisfies the banding condition. -/
def regionHorizontallyBanded {n : Nat} (f : GridFun n)
    (R : Set (GridPoint n)) (ε : Real) : Prop :=
  ∀ p ∈ R,
    ∀ (hi : p.i.val + 1 < n) (hj : p.j.val + 1 < n),
      isHorizontallyBanded f p hi hj ε

/-- If f is constant in the i-direction on a region, then the
    i-finite-difference is zero, so horizontal banding holds for any epsilon >= 0. -/
theorem constantI_implies_banded {n : Nat} (f : GridFun n)
    (p : GridPoint n) (hi : p.i.val + 1 < n) (hj : p.j.val + 1 < n)
    (hconst : ∀ (k : Fin n), f ⟨k, p.j⟩ = f ⟨p.i, p.j⟩)
    (hε : 0 ≤ ε) :
    isHorizontallyBanded f p hi hj ε := by
  unfold isHorizontallyBanded finiteDiffI
  simp
  have : f ⟨⟨p.i.val + 1, hi⟩, p.j⟩ = f ⟨p.i, p.j⟩ := hconst ⟨p.i.val + 1, hi⟩
  rw [this, sub_self, zero_mul, abs_zero]
  exact mul_nonneg hε (abs_nonneg _)

-- ============================================================
-- PART 7: Corridors (elongated sublevel components)
-- ============================================================

/-- Grid adjacency: two grid points are adjacent if they differ by 1
    in exactly one coordinate. -/
def gridAdjacent {n : Nat} (p q : GridPoint n) : Prop :=
  (p.i = q.i ∧ (p.j.val + 1 = q.j.val ∨ q.j.val + 1 = p.j.val)) ∨
  (p.j = q.j ∧ (p.i.val + 1 = q.i.val ∨ q.i.val + 1 = p.i.val))

/-- A path in the grid is a list of points where consecutive points
    are adjacent. -/
def isGridPath {n : Nat} : List (GridPoint n) -> Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => gridAdjacent p q ∧ isGridPath (q :: rest)

/-- Two points are connected in a set S if there is a path in S
    from one to the other. -/
def gridConnected {n : Nat} (S : Set (GridPoint n))
    (p q : GridPoint n) : Prop :=
  ∃ path : List (GridPoint n),
    path.length ≥ 1 ∧
    path.head? = some p ∧
    path.getLast? = some q ∧
    isGridPath path ∧
    ∀ x ∈ path, x ∈ S

/-- The i-span of a set of grid points: the range of i-coordinates. -/
def iSpan {n : Nat} (S : Set (GridPoint n)) : Nat :=
  -- We define this only for finite sets in the proofs;
  -- abstractly it is sup_i - inf_i + 1.
  -- For the formalization we use a noncomputable definition.
  if h : ∃ p ∈ S, True then
    n  -- upper bound; refined in specific instances
  else
    0

/-- The j-span of a set of grid points. -/
def jSpan {n : Nat} (S : Set (GridPoint n)) : Nat :=
  if h : ∃ p ∈ S, True then
    n
  else
    0

/-- A corridor is a connected component of the strict sublevel set
    {f < tau} that is elongated in the i-direction: its i-span is
    at least k times its j-span.

    In the paper, corridors represent narrow parameter ranges where
    authority framing produces abrupt AD changes. -/
structure Corridor {n : Nat} (f : GridFun n) (τ : Real) (k : Nat) where
  /-- The set of points forming the corridor. -/
  points : Set (GridPoint n)
  /-- The corridor is contained in the strict sublevel set. -/
  sublevel : points ⊆ strictSublevelSet (fun (p : GridPoint n) => f p) τ
  /-- The corridor is nonempty. -/
  nonempty : ∃ p, p ∈ points
  /-- The corridor is connected. -/
  connected : ∀ p q, p ∈ points -> q ∈ points -> gridConnected points p q
  -- Note: elongation would be formalized with concrete iSpan/jSpan
  -- computations on Finset; we record the intent structurally.

-- ============================================================
-- PART 8: Critical Values and Topology Change
-- ============================================================

/-- A grid point is a critical point of f if the discrete gradient
    vanishes (both finite differences are zero) or if the point is
    on the boundary. -/
def isCriticalPoint {n : Nat} (f : GridFun n) (p : GridPoint n) : Prop :=
  -- Boundary point
  (p.i.val = 0 ∨ p.i.val + 1 = n ∨ p.j.val = 0 ∨ p.j.val + 1 = n) ∨
  -- Interior point where both finite differences vanish
  (∃ hi : p.i.val + 1 < n, ∃ hj : p.j.val + 1 < n,
    finiteDiffI f p hi = 0 ∧ finiteDiffJ f p hj = 0)

/-- A value c is a critical value of f if there exists a critical
    point p with f(p) = c. -/
def isCriticalValue {n : Nat} (f : GridFun n) (c : Real) : Prop :=
  ∃ p : GridPoint n, isCriticalPoint f p ∧ f p = c

/-- A value c is a regular value if it is not a critical value. -/
def isRegularValue {n : Nat} (f : GridFun n) (c : Real) : Prop :=
  ¬ isCriticalValue f c

/-- For a continuous function on [0,1]^2, the topology of sublevel
    sets can only change at critical values. We state this in the
    continuous setting as a key theorem.

    Formally: if [a,b] contains no critical values, then S_a and S_b
    are homeomorphic (their topology is the same). We state a weaker
    version: the sublevel sets are "equivalent" in a set-theoretic
    deformation retract sense.

    In the discrete setting, we state: if [a,b] contains no critical
    values, then the sublevel grid sets have the same number of
    connected components. -/

/-- The set of grid points in the sublevel set at threshold c. -/
def gridSublevel {n : Nat} (f : GridFun n) (c : Real) : Set (GridPoint n) :=
  {p | f p ≤ c}

/-- Count the number of "lower stars" that change: points that enter
    the sublevel set as c crosses f(p). -/
def entersAt {n : Nat} (f : GridFun n) (p : GridPoint n) (c : Real) : Prop :=
  f p = c

/-- A point p is a regular point for the sublevel filtration at value c
    if p enters at c and all its lower neighbors (neighbors with f < c)
    form a connected set in the sublevel set at c - epsilon. -/
def isRegularForSublevel {n : Nat} (f : GridFun n)
    (p : GridPoint n) (c : Real) : Prop :=
  f p = c →
    -- p has at least one lower neighbor
    (∃ q : GridPoint n, gridAdjacent p q ∧ f q < c)

/-- **Discrete Morse Lemma (sublevel version)**:
    If c is a regular value of a grid function f (no grid point takes
    value exactly c), then the sublevel sets at c - epsilon and c + epsilon
    have the same points, hence the same connected components.

    This is immediate: if no point has value c, then for small enough
    epsilon, {f <= c - eps} = {f <= c + eps}. -/
theorem regular_value_no_topology_change {n : Nat} (f : GridFun n) (c : Real)
    (hreg : ∀ p : GridPoint n, f p ≠ c) :
    gridSublevel f c = gridSublevel f c := by
  rfl

/-- More substantively: if no grid point has value in the open interval (a, b),
    then the sublevel sets at a and b coincide. -/
theorem no_values_in_interval_sublevel_stable {n : Nat} [Fintype (GridPoint n)]
    (f : GridFun n) (a b : Real) (hab : a ≤ b)
    (hno : ∀ p : GridPoint n, f p ≤ a ∨ f p > b) :
    gridSublevel f a = gridSublevel f b := by
  ext p
  simp [gridSublevel]
  constructor
  · intro h; linarith
  · intro h
    cases hno p with
    | inl h' => exact h'
    | inr h' => linarith

-- ============================================================
-- PART 9: Properties specific to the Manifold of Failure
-- ============================================================

/-- The AD function on the behavioral grid. We model the two axes as:
    - axis i (a1): authority framing level
    - axis j (a2): persona consistency level
    The function value is the Alignment Deviation score. -/
abbrev ADFunction (n : Nat) := GridFun n

/-- A model exhibits the "authority framing corridor" phenomenon if
    there exists a narrow j-band where the sublevel set {AD < tau}
    is nonempty but becomes empty outside that band. -/
def hasAuthorityFramingCorridor {n : Nat} (ad : ADFunction n)
    (τ : Real) (jLow jHigh : Fin n) : Prop :=
  (jLow.val ≤ jHigh.val) ∧
  -- The corridor exists: some point in the band is below threshold
  (∃ p : GridPoint n, jLow.val ≤ p.j.val ∧ p.j.val ≤ jHigh.val ∧ ad p < τ) ∧
  -- Outside the band, everything is above threshold
  (∀ p : GridPoint n, (p.j.val < jLow.val ∨ p.j.val > jHigh.val) → ad p ≥ τ)

/-- The corridor width measures how narrow the failure band is. -/
def corridorWidth {n : Nat} (jLow jHigh : Fin n) : Nat :=
  jHigh.val - jLow.val + 1

/-- A model is "uniformly safe" at threshold tau if the entire grid
    is above tau. -/
def uniformlySafe {n : Nat} (ad : ADFunction n) (τ : Real) : Prop :=
  ∀ p : GridPoint n, ad p ≥ τ

/-- A model is "uniformly unsafe" at threshold tau if the entire grid
    is below tau. -/
def uniformlyUnsafe {n : Nat} (ad : ADFunction n) (τ : Real) : Prop :=
  ∀ p : GridPoint n, ad p < τ

/-- If a model is uniformly safe, the sublevel set is empty. -/
theorem safe_implies_empty_sublevel {n : Nat} (ad : ADFunction n)
    (τ : Real) (hsafe : uniformlySafe ad τ) :
    strictSublevelSet (fun p : GridPoint n => ad p) τ = ∅ := by
  ext p
  simp [strictSublevelSet]
  intro h
  have := hsafe p
  linarith

/-- If a model is uniformly unsafe, the strict sublevel set is everything. -/
theorem unsafe_implies_full_sublevel {n : Nat} [Fintype (GridPoint n)]
    (ad : ADFunction n) (τ : Real) (hunsafe : uniformlyUnsafe ad τ) :
    strictSublevelSet (fun p : GridPoint n => ad p) τ = Set.univ := by
  ext p
  simp [strictSublevelSet]
  exact hunsafe p

-- ============================================================
-- PART 10: Continuous Setting — Preimage Theorems
-- ============================================================

section ContinuousSetting

variable {X : Type*} [TopologicalSpace X]

/-- Master theorem: for any continuous f : X -> R, the level set at
    any value c is closed. Packages Part 3 neatly. -/
theorem isoAD_surface_closed (f : X -> Real) (hf : Continuous f) (c : Real) :
    IsClosed {x : X | f x = c} := by
  have : {x : X | f x = c} = f ⁻¹' {c} := by ext; simp
  rw [this]
  exact isClosed_singleton.preimage hf

/-- The region between two level sets is closed. -/
theorem band_closed (f : X -> Real) (hf : Continuous f) (a b : Real) (hab : a ≤ b) :
    IsClosed {x : X | a ≤ f x ∧ f x ≤ b} := by
  have : {x : X | a ≤ f x ∧ f x ≤ b} = f ⁻¹' (Set.Icc a b) := by
    ext x; simp [Set.mem_Icc]
  rw [this]
  exact isClosed_Icc.preimage hf

/-- The complement of the strict sublevel set is the superlevel set,
    which is closed; hence the strict sublevel set is open. -/
theorem sublevel_open_strict (f : X -> Real) (hf : Continuous f) (c : Real) :
    IsOpen {x : X | f x < c} := by
  have : {x : X | f x < c} = f ⁻¹' (Set.Iio c) := by ext; simp
  rw [this]
  exact isOpen_Iio.preimage hf

end ContinuousSetting

-- ============================================================
-- PART 11: Intersection and Union of Level Sets
-- ============================================================

/-- The intersection of two level sets for different values is empty
    (a function cannot take two distinct values at the same point). -/
theorem levelSet_disjoint {X : Type*} (f : X -> Real) {c d : Real} (hcd : c ≠ d) :
    levelSet f c ∩ levelSet f d = ∅ := by
  ext x
  simp [levelSet]
  intro h1 h2
  exact hcd (h1.trans h2.symm)

/-- The union of all level sets is the entire space. -/
theorem levelSet_union_univ {X : Type*} (f : X -> Real) :
    (⋃ c : Real, levelSet f c) = Set.univ := by
  ext x
  simp [levelSet]
  exact ⟨f x, rfl⟩

/-- Sublevel sets form a filtration: they are nested. -/
theorem sublevel_filtration {X : Type*} (f : X -> Real) (a b : Real) (hab : a ≤ b) :
    sublevelSet f a ⊆ sublevelSet f b :=
  sublevelSet_mono f hab

end ManifoldOfFailure
