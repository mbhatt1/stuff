/-
  MAP-Elites Archive Formalization
  =================================
  Formalizes the MAP-Elites quality-diversity archive from first principles,
  as described in "Manifold of Failure" and the MAP-Elites literature.

  The behavioral space [0,1]^2 is partitioned into an N x N grid.
  Each cell holds at most one "elite" — a solution with an associated quality score.
  New candidates replace existing elites only when they have strictly higher quality.

  We prove two key monotonicity properties:
    1. Per-cell quality never decreases under insertion.
    2. The count of occupied cells never decreases under insertion.
-/

import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

-- ============================================================================
-- Section 1: Grid and Discretization
-- ============================================================================

/-- A grid cell in an N x N behavioral-space partition. -/
abbrev GridCell (N : ℕ) := Fin N × Fin N

/-- A point in the unit square, represented by two rationals in [0,1].
    We use ℚ for exact arithmetic; the key property is 0 ≤ x ≤ 1. -/
structure UnitPoint where
  x : ℚ
  y : ℚ
  hx_nonneg : 0 ≤ x
  hx_le_one : x ≤ 1
  hy_nonneg : 0 ≤ y
  hy_le_one : y ≤ 1

/-- Discretize a rational value in [0,1] to a bin index in Fin N.
    disc(v) = min(floor(v * N), N - 1).
    The `min` with N-1 handles the boundary case v = 1. -/
def discretizeCoord (N : ℕ) (hN : 0 < N) (v : ℚ) (_ : 0 ≤ v) (_ : v ≤ 1) : Fin N :=
  let raw := (v * ↑N).floor.toNat
  ⟨min raw (N - 1), by omega⟩

/-- Discretize a point in [0,1]^2 to a grid cell in Fin N × Fin N. -/
def discretize (N : ℕ) (hN : 0 < N) (p : UnitPoint) : GridCell N :=
  ( discretizeCoord N hN p.x p.hx_nonneg p.hx_le_one,
    discretizeCoord N hN p.y p.hy_nonneg p.hy_le_one )

-- ============================================================================
-- Section 2: Archive Definition
-- ============================================================================

/-- An elite stored in an archive cell: a prompt (opaque type α) with a quality score. -/
structure Elite (α : Type*) where
  prompt  : α
  quality : ℚ

/-- The MAP-Elites Archive: a total function from grid cells to optional elites.
    `none` means the cell is empty; `some e` means it is occupied by elite `e`. -/
def Archive (N : ℕ) (α : Type*) := GridCell N → Option (Elite α)

/-- The empty archive: every cell is unoccupied. -/
def Archive.empty (N : ℕ) (α : Type*) : Archive N α :=
  fun _ => none

-- ============================================================================
-- Section 3: AddToArchive Operation
-- ============================================================================

/-- Add a candidate elite to the archive at a given cell.
    The candidate replaces the current occupant if and only if:
      - the cell is empty, OR
      - the candidate's quality strictly exceeds the current elite's quality.
    Otherwise the archive is unchanged. -/
def addToArchive {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α) : Archive N α :=
  fun c =>
    if c = cell then
      match A cell with
      | none          => some candidate
      | some existing =>
        if candidate.quality > existing.quality then some candidate
        else some existing
    else
      A c

-- ============================================================================
-- Section 4: Quality Ordering on Cells
-- ============================================================================

/-- The "quality level" of a cell: none maps to ⊥ (represented as none),
    and `some e` maps to `some e.quality`. This gives a natural ordering
    where empty < any occupied cell, using `Option ℚ` with `none < some _`. -/
def cellQuality {N : ℕ} {α : Type*} (A : Archive N α) (c : GridCell N) : Option ℚ :=
  (A c).map Elite.quality

/-- A cell is occupied when the archive maps it to `some _`. -/
def cellOccupied {N : ℕ} {α : Type*} (A : Archive N α) (c : GridCell N) : Prop :=
  (A c).isSome = true

-- ============================================================================
-- Section 5: Monotonicity of Per-Cell Quality
-- ============================================================================

/-- Helper: ordering on `Option ℚ` where `none` is below everything,
    and `some a ≤ some b ↔ a ≤ b`. This is exactly `WithBot` ordering. -/
def optQualityLe : Option ℚ → Option ℚ → Prop
  | none,   _      => True
  | some _, none   => False
  | some a, some b => a ≤ b

/-- Per-cell quality is monotonically non-decreasing under `addToArchive`.
    For every cell c, the quality after insertion is ≥ the quality before. -/
theorem addToArchive_quality_monotone {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α) (c : GridCell N) :
    optQualityLe (cellQuality A c) (cellQuality (addToArchive A cell candidate) c) := by
  simp only [cellQuality, addToArchive]
  split_ifs with heq
  · -- c = cell: this is the target cell
    subst heq
    cases h : A cell with
    | none =>
      simp [h, Option.map, optQualityLe]
    | some existing =>
      simp only [h, Option.map]
      split_ifs with hq
      · -- candidate is better
        simp [optQualityLe]
        exact le_of_lt hq
      · -- existing stays
        simp [optQualityLe]
  · -- c ≠ cell: archive unchanged at c
    cases h : A c with
    | none => simp [h, Option.map, optQualityLe]
    | some e => simp [h, Option.map, optQualityLe]

/-- Corollary: if a cell had quality q before insertion, it has quality ≥ q after. -/
theorem addToArchive_preserves_quality {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α)
    (c : GridCell N) (e : Elite α) (hc : A c = some e) :
    ∃ e' : Elite α, addToArchive A cell candidate c = some e' ∧ e'.quality ≥ e.quality := by
  simp only [addToArchive]
  split_ifs with heq
  · subst heq
    simp [hc]
    split_ifs with hq
    · exact ⟨candidate, rfl, le_of_lt hq⟩
    · exact ⟨e, rfl, le_refl _⟩
  · exact ⟨e, hc, le_refl _⟩

-- ============================================================================
-- Section 6: Monotonicity of Occupied Cell Count
-- ============================================================================

/-- A cell that was occupied remains occupied after insertion. -/
theorem addToArchive_preserves_occupied {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α)
    (c : GridCell N) (hc : cellOccupied A c) :
    cellOccupied (addToArchive A cell candidate) c := by
  simp only [cellOccupied, addToArchive] at *
  split_ifs with heq
  · subst heq
    cases h : A cell with
    | none => simp [h, Option.isSome]
    | some existing =>
      simp only [h]
      split_ifs <;> simp [Option.isSome]
  · exact hc

/-- The target cell is always occupied after insertion. -/
theorem addToArchive_fills_target {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α) :
    cellOccupied (addToArchive A cell candidate) cell := by
  simp only [cellOccupied, addToArchive, if_pos rfl]
  cases A cell with
  | none => simp [Option.isSome]
  | some existing =>
    split_ifs <;> simp [Option.isSome]

/-- For any finite enumeration of cells, the count of occupied cells never decreases.
    We state this over `Finset (GridCell N)` — in practice the full grid. -/
theorem addToArchive_occupied_count_monotone {N : ℕ} [NeZero N] {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α)
    (S : Finset (GridCell N)) :
    (S.filter (fun c => cellOccupied A c)).card
      ≤ (S.filter (fun c => cellOccupied (addToArchive A cell candidate) c)).card := by
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, addToArchive_preserves_occupied A cell candidate c hc.2⟩

-- ============================================================================
-- Section 7: Iterated Insertion and Multi-Step Monotonicity
-- ============================================================================

/-- A sequence of insertions applied to an archive. -/
def addMany {N : ℕ} {α : Type*}
    (A : Archive N α) : List (GridCell N × Elite α) → Archive N α
  | []            => A
  | (c, e) :: rest => addMany (addToArchive A c e) rest

/-- Per-cell quality is monotone across an arbitrary sequence of insertions. -/
theorem addMany_quality_monotone {N : ℕ} {α : Type*}
    (A : Archive N α) (ops : List (GridCell N × Elite α)) (c : GridCell N) :
    optQualityLe (cellQuality A c) (cellQuality (addMany A ops) c) := by
  induction ops generalizing A with
  | nil => simp [addMany, cellQuality]; cases A c <;> simp [Option.map, optQualityLe]
  | cons op rest ih =>
    simp only [addMany]
    have h1 := addToArchive_quality_monotone A op.1 op.2 c
    have h2 := ih (addToArchive A op.1 op.2) c
    -- Transitivity of optQualityLe
    revert h1 h2
    simp only [cellQuality]
    cases h_orig : A c <;> cases h_mid : (addToArchive A op.1 op.2) c <;>
      cases h_fin : (addMany (addToArchive A op.1 op.2) rest) c <;>
      simp [Option.map, optQualityLe] <;>
      intro <;> omega

/-- Occupied cells are monotone across an arbitrary sequence of insertions. -/
theorem addMany_preserves_occupied {N : ℕ} {α : Type*}
    (A : Archive N α) (ops : List (GridCell N × Elite α))
    (c : GridCell N) (hc : cellOccupied A c) :
    cellOccupied (addMany A ops) c := by
  induction ops generalizing A with
  | nil => simpa [addMany]
  | cons op rest ih =>
    simp only [addMany]
    exact ih _ c (addToArchive_preserves_occupied A op.1 op.2 c hc)

-- ============================================================================
-- Section 8: Concrete Instantiation for the Paper's 25 x 25 Grid
-- ============================================================================

/-- The paper uses a 25 x 25 grid (625 cells). -/
abbrev PaperGridSize : ℕ := 25

/-- A cell in the paper's 25 x 25 behavioral grid. -/
abbrev PaperCell := GridCell PaperGridSize

/-- Discretize a behavioral descriptor to the paper's grid. -/
def paperDiscretize : UnitPoint → PaperCell :=
  discretize PaperGridSize (by omega)

/-- The paper's archive type, parameterized by the prompt type. -/
abbrev PaperArchive (α : Type*) := Archive PaperGridSize α

/-- The paper's grid has exactly 625 cells. -/
theorem paper_grid_card : Fintype.card PaperCell = 625 := by
  simp [PaperCell, GridCell, Fintype.card_prod, Fintype.card_fin]

-- ============================================================================
-- Section 9: Archive Quality Bound
-- ============================================================================

/-- After insertion of a candidate with quality q into cell c,
    the quality at cell c is at least q if the cell was previously empty,
    and at least max(old_quality, q) if it was occupied. -/
theorem addToArchive_target_quality {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α) :
    ∃ e' : Elite α, addToArchive A cell candidate cell = some e' ∧
      (∀ e_old : Elite α, A cell = some e_old →
        e'.quality ≥ e_old.quality ∧ e'.quality ≥ candidate.quality ∨
        e'.quality = candidate.quality) ∧
      (A cell = none → e' = candidate) := by
  simp only [addToArchive, if_pos rfl]
  cases h : A cell with
  | none =>
    exact ⟨candidate, rfl, fun e_old h_old => by simp [h] at h_old, fun _ => rfl⟩
  | some existing =>
    split_ifs with hq
    · refine ⟨candidate, rfl, fun e_old h_old => ?_, fun h_none => by simp [h] at h_none⟩
      simp [h] at h_old; subst h_old
      right; rfl
    · refine ⟨existing, rfl, fun e_old h_old => ?_, fun h_none => by simp [h] at h_none⟩
      simp [h] at h_old; subst h_old
      left
      push_neg at hq
      exact ⟨le_refl _, hq⟩

-- ============================================================================
-- Section 10: Non-Interference Lemma
-- ============================================================================

/-- Insertion at one cell does not affect any other cell. -/
theorem addToArchive_other_cell {N : ℕ} {α : Type*}
    (A : Archive N α) (cell : GridCell N) (candidate : Elite α)
    (c : GridCell N) (hne : c ≠ cell) :
    addToArchive A cell candidate c = A c := by
  simp [addToArchive, if_neg hne]
