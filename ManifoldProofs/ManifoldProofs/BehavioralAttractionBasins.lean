/-
  Behavioral Attraction Basins — Lean 4 / Mathlib Formalization
  =============================================================

  From "Manifold of Failure":
    An attraction basin is a connected component of the superlevel set
    {x ∈ B | Q(x) > τ} in the behavioral grid, where Q is the
    Alignment Deviation function and τ (default 0.5) is the threshold.

  We formalize:
    §1  Superlevel sets (continuous case)
    §2  Discrete grid, adjacency, reachability
    §3  Connected components = Attraction Basins
    §4  Basin rate ∈ [0, 1]
    §5  Topological openness of components (continuous case)
    §6  Counting distinct basins
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic

open Set Finset

noncomputable section

-- ════════════════════════════════════════════════════════════════════
-- §1. Superlevel Sets
-- ════════════════════════════════════════════════════════════════════

/-- The superlevel set S_τ = {x ∈ B | f(x) > τ}. -/
def superlevelSet {B : Type*} (f : B → ℝ) (τ : ℝ) : Set B :=
  {x | τ < f x}

/-- Notation: S_τ(f) -/
notation "S_{" τ "}(" f ")" => superlevelSet f τ

-- ════════════════════════════════════════════════════════════════════
-- §2. Discrete Grid and Adjacency
-- ════════════════════════════════════════════════════════════════════

/-- A cell in the N×N behavioral grid. -/
abbrev Cell (N : ℕ) := Fin N × Fin N

/-- Two cells are 4-adjacent if they share an edge (Manhattan distance = 1). -/
def adj4 {N : ℕ} (p q : Cell N) : Prop :=
  (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

/-- Two cells are 8-adjacent if they differ by at most 1 in each coordinate
    (Chebyshev distance = 1) and are distinct. -/
def adj8 {N : ℕ} (p q : Cell N) : Prop :=
  p ≠ q ∧
  (p.1.val = q.1.val ∨ p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val) ∧
  (p.2.val = q.2.val ∨ p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)

/-- Adjacency is symmetric (4-connectivity). -/
theorem adj4_symm {N : ℕ} (p q : Cell N) : adj4 p q → adj4 q p := by
  intro h
  unfold adj4 at *
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp_all [h1.symm]
  · left; exact ⟨h1.symm, Or.inr h2⟩
  · left; exact ⟨h1.symm, Or.inl h2⟩
  · right; exact ⟨h1.symm, Or.inr h2⟩
  · right; exact ⟨h1.symm, Or.inl h2⟩

/-- Adjacency is irreflexive (4-connectivity): no cell is adjacent to itself. -/
theorem adj4_irrefl {N : ℕ} (p : Cell N) : ¬adj4 p p := by
  intro h
  unfold adj4 at h
  rcases h with ⟨_, h2 | h2⟩ | ⟨_, h2 | h2⟩ <;> omega

-- ════════════════════════════════════════════════════════════════════
-- §3. Grid Paths and Reachability (Connected Components)
-- ════════════════════════════════════════════════════════════════════

/-- A path in a subset S of the grid: a list of cells, each adjacent to the
    next, all contained in S. We use 4-connectivity by default. -/
inductive GridPath {N : ℕ} (S : Set (Cell N)) : Cell N → Cell N → Prop where
  | refl (x : Cell N) (hx : x ∈ S) : GridPath S x x
  | step (x y z : Cell N) (hx : x ∈ S) (hxy : adj4 x y) (hyz : GridPath S y z) :
      GridPath S x z

/-- Reachability is reflexive on S. -/
theorem gridPath_refl {N : ℕ} {S : Set (Cell N)} {x : Cell N} (hx : x ∈ S) :
    GridPath S x x :=
  GridPath.refl x hx

/-- Reachability is transitive. -/
theorem gridPath_trans {N : ℕ} {S : Set (Cell N)} {x y z : Cell N}
    (hxy : GridPath S x y) (hyz : GridPath S y z) : GridPath S x z := by
  induction hxy with
  | refl _ _ => exact hyz
  | step a b _ ha hab _ ih => exact GridPath.step a b z ha hab (ih hyz)

/-- Every node on a GridPath lies in S. -/
theorem gridPath_mem {N : ℕ} {S : Set (Cell N)} {x y : Cell N}
    (h : GridPath S x y) : x ∈ S ∧ y ∈ S := by
  induction h with
  | refl x hx => exact ⟨hx, hx⟩
  | step a _ z ha _ _ ih => exact ⟨ha, ih.2⟩

/-- The first intermediate node in a GridPath step lies in S. -/
theorem gridPath_step_mem {N : ℕ} {S : Set (Cell N)} {x y z : Cell N}
    (_hx : x ∈ S) (_hxy : adj4 x y) (hyz : GridPath S y z) : y ∈ S :=
  (gridPath_mem hyz).1

/-- Reachability is symmetric. -/
theorem gridPath_symm {N : ℕ} {S : Set (Cell N)} {x y : Cell N}
    (hxy : GridPath S x y) : GridPath S y x := by
  induction hxy with
  | refl x hx => exact GridPath.refl x hx
  | step a b _ ha hab hbz ih =>
    exact gridPath_trans ih
      (GridPath.step b a a (gridPath_step_mem ha hab hbz)
        (adj4_symm a b hab) (GridPath.refl a ha))

-- ════════════════════════════════════════════════════════════════════
-- §4. Attraction Basins (Discrete)
-- ════════════════════════════════════════════════════════════════════

/-- The discrete superlevel set on the grid: cells where f exceeds threshold τ. -/
def discreteSuperlevel {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) : Set (Cell N) :=
  {c | τ < f c}

/-- The connected component of a cell x in the discrete superlevel set.
    This is the attraction basin containing x. -/
def attractionBasinOf {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (x : Cell N) : Set (Cell N) :=
  {y | GridPath (discreteSuperlevel f τ) x y}

/-- Every cell in a basin belongs to the superlevel set. -/
theorem basin_subset_superlevel {N : ℕ} {f : Cell N → ℝ} {τ : ℝ} {x : Cell N} :
    attractionBasinOf f τ x ⊆ discreteSuperlevel f τ := by
  intro y hy
  exact (gridPath_mem hy).2

/-- A cell is in its own basin iff it is in the superlevel set. -/
theorem mem_basin_self_iff {N : ℕ} {f : Cell N → ℝ} {τ : ℝ} {x : Cell N} :
    x ∈ attractionBasinOf f τ x ↔ x ∈ discreteSuperlevel f τ := by
  constructor
  · intro h; exact basin_subset_superlevel h
  · intro h; exact GridPath.refl x h

-- ════════════════════════════════════════════════════════════════════
-- §5. Basin Rate
-- ════════════════════════════════════════════════════════════════════

/-- The set of "filled" cells: cells that have been evaluated / explored. -/
def FilledCells {N : ℕ} (filled : Finset (Cell N)) : Finset (Cell N) := filled

/-- Cells in filled that belong to the superlevel set. -/
def basinCells {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)] : Finset (Cell N) :=
  filled.filter (· ∈ discreteSuperlevel f τ)

/-- Basin rate: fraction of filled cells that exceed the threshold.
    Returns 0 if there are no filled cells. -/
def basinRate {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)] : ℝ :=
  if filled.card = 0 then 0
  else (basinCells f τ filled).card / filled.card

/-- Basin rate is non-negative. -/
theorem basinRate_nonneg {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)] :
    0 ≤ basinRate f τ filled := by
  unfold basinRate
  split
  · linarith
  · apply div_nonneg
    · exact Nat.cast_nonneg'
    · exact Nat.cast_nonneg'

/-- Basin rate is at most 1. -/
theorem basinRate_le_one {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)] :
    basinRate f τ filled ≤ 1 := by
  unfold basinRate
  split
  · linarith
  · rename_i h
    apply div_le_one_of_le
    · exact_mod_cast Finset.card_filter_le filled _
    · exact_mod_cast Nat.pos_of_ne_zero h

/-- Basin rate ∈ [0, 1]. -/
theorem basinRate_mem_unitInterval {N : ℕ} (f : Cell N → ℝ) (τ : ℝ)
    (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)] :
    basinRate f τ filled ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨basinRate_nonneg f τ filled, basinRate_le_one f τ filled⟩

-- ════════════════════════════════════════════════════════════════════
-- §6. Continuous Case: Openness of Components
-- ════════════════════════════════════════════════════════════════════

/-- The (strict) superlevel set of a continuous function into ℝ is open,
    since (τ, ∞) is open in ℝ and preimages of open sets under continuous
    maps are open. -/
theorem superlevelSet_isOpen {B : Type*} [TopologicalSpace B] {f : B → ℝ}
    (hf : Continuous f) (τ : ℝ) : IsOpen (superlevelSet f τ) := by
  apply isOpen_lt continuous_const hf

/-- Each connected component of an open set in a topological space is open.
    (Standard fact: components of open sets in locally connected spaces are open.
     ℝ^n and metric spaces are locally connected.) -/
theorem connectedComponent_of_open_isOpen
    {B : Type*} [TopologicalSpace B] [LocallyConnectedSpace B]
    {U : Set B} (hU : IsOpen U) (x : B) (hx : x ∈ U) :
    IsOpen (connectedComponentIn U x) := by
  exact isOpen_connectedComponent_of_isOpen hU hx

/-- In the continuous setting, each attraction basin (= connected component
    of the superlevel set) is open, provided the ambient space is locally
    connected. -/
theorem attractionBasin_continuous_isOpen
    {B : Type*} [TopologicalSpace B] [LocallyConnectedSpace B]
    {f : B → ℝ} (hf : Continuous f) (τ : ℝ)
    (x : B) (hx : x ∈ superlevelSet f τ) :
    IsOpen (connectedComponentIn (superlevelSet f τ) x) := by
  exact connectedComponent_of_open_isOpen (superlevelSet_isOpen hf τ) x hx

-- ════════════════════════════════════════════════════════════════════
-- §7. Number of Distinct Basins
-- ════════════════════════════════════════════════════════════════════

/-- Two superlevel cells are in the same basin iff they are grid-path connected. -/
def sameBasin {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (x y : Cell N) : Prop :=
  GridPath (discreteSuperlevel f τ) x y

/-- sameBasin is an equivalence relation on the superlevel set.
    (Reflexivity requires membership; transitivity and symmetry follow
    from GridPath properties.) -/

/-- The quotient type of basins: equivalence classes of superlevel cells
    under grid-path connectivity. For a finite grid, we can enumerate them. -/

/-- For a finite decidable setting, the number of distinct basins is the
    number of connected components. We define it as the cardinality of the
    image of the component-assignment map. -/

/-- Given a computable connected-component labeling (e.g., union-find on
    the finite grid), the number of basins is the number of distinct labels
    among superlevel cells. We axiomatize the labeling here. -/
def numBasins {N : ℕ} (f : Cell N → ℝ) (τ : ℝ)
    (superlevelFinset : Finset (Cell N))
    (label : Cell N → ℕ)
    -- label assigns the same value to cells in the same component
    (_label_consistent : ∀ x y, x ∈ superlevelFinset → y ∈ superlevelFinset →
      sameBasin f τ x y → label x = label y)
    -- label assigns different values to cells in different components
    (_label_separating : ∀ x y, x ∈ superlevelFinset → y ∈ superlevelFinset →
      label x = label y → sameBasin f τ x y) :
    ℕ :=
  (superlevelFinset.image label).card

/-- The number of basins is zero iff the superlevel set is empty. -/
theorem numBasins_eq_zero_iff {N : ℕ} (f : Cell N → ℝ) (τ : ℝ)
    (superlevelFinset : Finset (Cell N))
    (label : Cell N → ℕ)
    (hc : ∀ x y, x ∈ superlevelFinset → y ∈ superlevelFinset →
      sameBasin f τ x y → label x = label y)
    (hs : ∀ x y, x ∈ superlevelFinset → y ∈ superlevelFinset →
      label x = label y → sameBasin f τ x y) :
    numBasins f τ superlevelFinset label hc hs = 0 ↔ superlevelFinset = ∅ := by
  unfold numBasins
  simp [Finset.image_eq_empty]

-- ════════════════════════════════════════════════════════════════════
-- §8. Key Domain Theorems (Manifold of Failure specific)
-- ════════════════════════════════════════════════════════════════════

/-- Default threshold from the paper. -/
def defaultThreshold : ℝ := 0.5

/-- Basin rate with the paper's default threshold τ = 0.5. -/
def basinRate_default {N : ℕ} (f : Cell N → ℝ) (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f defaultThreshold)] : ℝ :=
  basinRate f defaultThreshold filled

/-- A model is "basin-free" at threshold τ if no filled cell exceeds τ. -/
def basinFree {N : ℕ} (f : Cell N → ℝ) (τ : ℝ) (filled : Finset (Cell N)) : Prop :=
  ∀ c ∈ filled, f c ≤ τ

/-- A basin-free model has basin rate 0. -/
theorem basinFree_rate_zero {N : ℕ} (f : Cell N → ℝ) (τ : ℝ)
    (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)]
    (hfree : basinFree f τ filled) :
    basinRate f τ filled = 0 := by
  unfold basinRate
  split
  · rfl
  · suffices basinCells f τ filled = ∅ by simp [this]
    unfold basinCells
    rw [Finset.filter_eq_empty]
    intro c hc
    simp [discreteSuperlevel]
    exact hfree c hc

/-- Conversely, if every filled cell exceeds τ, the basin rate is 1. -/
theorem allAbove_rate_one {N : ℕ} (f : Cell N → ℝ) (τ : ℝ)
    (filled : Finset (Cell N))
    [DecidablePred (· ∈ discreteSuperlevel f τ)]
    (hne : filled.Nonempty)
    (hall : ∀ c ∈ filled, τ < f c) :
    basinRate f τ filled = 1 := by
  unfold basinRate
  split
  · exfalso; exact Finset.Nonempty.ne_empty hne (Finset.card_eq_zero.mp ‹_›)
  · suffices basinCells f τ filled = filled by simp [this]; field_simp
    unfold basinCells
    rw [Finset.filter_eq_self]
    intro c hc
    exact hall c hc

end
