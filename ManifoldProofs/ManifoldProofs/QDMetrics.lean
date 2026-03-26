/-
  Quality-Diversity Evaluation Metrics — Lean 4 / Mathlib formalization
  =====================================================================

  Formalizes the five QD metrics from "Manifold of Failure":
    1. Behavioral Coverage   (fraction of filled grid cells)
    2. Diversity             (count of filled cells with quality > 0.5)
    3. Peak Alignment Dev.   (maximum quality over filled cells)
    4. Mean Alignment Dev.   (average quality over filled cells)
    5. QD-Score              (sum of quality over filled cells)

  and proves four fundamental relationships among them.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open Finset BigOperators

/-! ## Archive model

An *archive* over an N×N behavioral grid assigns to every cell either
`none` (empty) or `some q` where `q : ℝ` is the quality / alignment-
deviation score stored in that cell.  We package the data together with
the invariant that every stored quality lies in [0, 1].
-/

/-- A QD archive over an `N × N` grid. -/
structure Archive (N : ℕ) where
  /-- The grid map: each cell is either empty (`none`) or stores a quality value. -/
  grid : Fin N × Fin N → Option ℝ
  /-- Every stored quality is non-negative. -/
  quality_nonneg : ∀ i j q, grid (i, j) = some q → 0 ≤ q
  /-- Every stored quality is at most 1. -/
  quality_le_one : ∀ i j q, grid (i, j) = some q → q ≤ 1

namespace Archive

variable {N : ℕ} (A : Archive N)

/-! ## Filled cells -/

/-- The set of all grid coordinates. -/
def allCells : Finset (Fin N × Fin N) := Finset.univ

/-- The finite set of *filled* cells (those carrying a quality value). -/
def filledCells : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun c => (A.grid c).isSome

/-- Extract the quality from a cell known to be filled. -/
noncomputable def qualityOf (c : Fin N × Fin N) (h : (A.grid c).isSome) : ℝ :=
  (A.grid c).get h

/-- Quality of a filled cell is non-negative. -/
lemma qualityOf_nonneg (c : Fin N × Fin N) (h : (A.grid c).isSome) :
    0 ≤ A.qualityOf c h := by
  simp only [qualityOf]
  obtain ⟨i, j⟩ := c
  have hg : A.grid (i, j) = some ((A.grid (i, j)).get h) := Option.some_get h
  exact A.quality_nonneg i j _ hg

/-- Quality of a filled cell is at most 1. -/
lemma qualityOf_le_one (c : Fin N × Fin N) (h : (A.grid c).isSome) :
    A.qualityOf c h ≤ 1 := by
  simp only [qualityOf]
  obtain ⟨i, j⟩ := c
  have hg : A.grid (i, j) = some ((A.grid (i, j)).get h) := Option.some_get h
  exact A.quality_le_one i j _ hg

/-! ## Helper: quality-or-zero

To work uniformly with sums over `Finset.univ` we define a total
function that returns `0` on empty cells.
-/

/-- Returns the stored quality, or `0` when the cell is empty. -/
noncomputable def q (c : Fin N × Fin N) : ℝ :=
  match A.grid c with
  | some v => v
  | none   => 0

lemma q_nonneg (c : Fin N × Fin N) : 0 ≤ A.q c := by
  simp only [q]
  obtain ⟨i, j⟩ := c
  split
  · next v hv => exact A.quality_nonneg i j v hv
  · linarith

lemma q_le_one (c : Fin N × Fin N) : A.q c ≤ 1 := by
  simp only [q]
  obtain ⟨i, j⟩ := c
  split
  · next v hv => exact A.quality_le_one i j v hv
  · linarith

/-- On a filled cell, `q` agrees with `qualityOf`. -/
lemma q_eq_qualityOf (c : Fin N × Fin N) (h : (A.grid c).isSome) :
    A.q c = A.qualityOf c h := by
  simp only [q, qualityOf]
  rw [Option.isSome_iff_exists] at h
  obtain ⟨v, hv⟩ := h
  simp [hv]

/-- On an empty cell, `q` is zero. -/
lemma q_empty (c : Fin N × Fin N) (h : (A.grid c).isNone) :
    A.q c = 0 := by
  simp only [q]
  rw [Option.isNone_iff_eq_none] at h
  simp [h]

/-! ## Metric 1 — Behavioral Coverage -/

/-- **Behavioral Coverage**: fraction of the N×N grid that is filled.
    Returns 0 when N = 0. -/
noncomputable def coverage : ℝ :=
  (A.filledCells.card : ℝ) / (N * N : ℝ)

/-! ## Metric 2 — Diversity -/

/-- **Diversity**: number of filled cells whose quality exceeds 0.5. -/
noncomputable def diversity : ℕ :=
  (A.filledCells.filter fun c =>
    A.q c > (1 : ℝ) / 2).card

/-! ## Metric 5 — QD-Score (defined before Peak/Mean for convenience) -/

/-- **QD-Score**: sum of quality values over all filled cells.
    Equivalently the sum of `q` over the entire grid (empty cells
    contribute 0). -/
noncomputable def qdScore : ℝ :=
  ∑ c in A.filledCells, A.q c

/-! ## Metric 3 — Peak Alignment Deviation -/

/-- **Peak Alignment Deviation**: maximum quality over filled cells.
    Returns 0 when the archive is empty. -/
noncomputable def peakAD : ℝ :=
  A.filledCells.sup' (α := WithBot ℝ) (fun c => (A.q c : WithBot ℝ))
  |>.getD 0  -- dummy; we will mostly use the Finset.le_sup' API

-- Actually, let us use a simpler formulation via Finset.sup' when nonempty
-- and fold for the general case.

/-- Peak AD via fold (works even when archive is empty, returning 0). -/
noncomputable def peakAD' : ℝ :=
  if h : A.filledCells.Nonempty then
    A.filledCells.sup' h (fun c => A.q c)
  else 0

/-! ## Metric 4 — Mean Alignment Deviation -/

/-- **Mean Alignment Deviation**: average quality over filled cells.
    Returns 0 when the archive is empty. -/
noncomputable def meanAD : ℝ :=
  if A.filledCells.card = 0 then 0
  else A.qdScore / (A.filledCells.card : ℝ)

/-! ================================================================
    ## Theorems
    ================================================================ -/

/-! ### Theorem 1: QD-Score ≤ N * N -/

/-- The sum over filled cells is at most the sum over all cells. -/
lemma qdScore_eq_sum_all :
    A.qdScore = ∑ c in Finset.univ, A.q c := by
  simp only [qdScore]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) |>.symm
  -- Need: sum over univ = sum over filledCells + sum over complement
  -- Actually easier: show terms outside filledCells are 0.
  rw [eq_comm]
  apply Finset.sum_subset
  · exact Finset.filter_subset _ _
  · intro c _ hc
    simp only [filledCells, Finset.mem_filter] at hc
    push_neg at hc
    have hc' := hc (Finset.mem_univ c)
    rw [Bool.not_eq_true] at hc'
    have : (A.grid c).isNone := by
      simp [Option.isNone_iff_eq_none, Option.not_isSome_iff_eq_none] at hc' ⊢
      exact hc'
    exact A.q_empty c this

theorem qdScore_le_N_sq : A.qdScore ≤ (N * N : ℝ) := by
  rw [A.qdScore_eq_sum_all]
  calc ∑ c in Finset.univ, A.q c
      ≤ ∑ c in (Finset.univ : Finset (Fin N × Fin N)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        exact A.q_le_one c
    _ = (Finset.univ : Finset (Fin N × Fin N)).card := by
        simp [Finset.sum_const, Algebra.id.smul_eq_mul, mul_one]
    _ = Fintype.card (Fin N × Fin N) := by rw [Finset.card_univ]
    _ = N * N := by simp [Fintype.card_prod, Fintype.card_fin]

/-! ### Theorem 2: Coverage ∈ [0, 1] -/

theorem coverage_nonneg : 0 ≤ A.coverage := by
  simp only [coverage]
  apply div_nonneg
  · exact Nat.cast_nonneg'
  · exact mul_nonneg (Nat.cast_nonneg') (Nat.cast_nonneg')

theorem coverage_le_one (hN : N ≠ 0) : A.coverage ≤ 1 := by
  simp only [coverage]
  rw [div_le_one (by positivity : (0 : ℝ) < (N : ℝ) * N)]
  have hcard : A.filledCells.card ≤ (Finset.univ : Finset (Fin N × Fin N)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  exact Nat.cast_le.mpr hcard

/-! ### Theorem 3: Mean AD ≤ Peak AD -/

/-- When the archive is non-empty, the mean quality does not exceed the peak. -/
theorem meanAD_le_peakAD (hne : A.filledCells.Nonempty) :
    A.meanAD ≤ A.peakAD' := by
  simp only [meanAD, peakAD']
  have hcard_pos : (0 : ℝ) < A.filledCells.card := by
    rw [Nat.cast_pos]
    exact Finset.Nonempty.card_pos hne
  have hcard_ne : (A.filledCells.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [if_neg (by omega : ¬ A.filledCells.card = 0)]
  rw [dif_pos hne]
  rw [div_le_iff hcard_pos]
  -- Need: qdScore ≤ peakAD * |filled|
  -- i.e.  Σ q(c) ≤ (sup q) * |filled|
  simp only [qdScore]
  calc ∑ c in A.filledCells, A.q c
      ≤ ∑ c in A.filledCells, A.filledCells.sup' hne (fun c => A.q c) := by
        apply Finset.sum_le_sum
        intro c hc
        exact Finset.le_sup' (fun c => A.q c) hc
    _ = A.filledCells.card • A.filledCells.sup' hne (fun c => A.q c) := by
        rw [Finset.sum_const]
    _ = A.filledCells.sup' hne (fun c => A.q c) * A.filledCells.card := by
        rw [nsmul_eq_mul, mul_comm]

/-! ### Theorem 4: QD-Score = Mean AD × |filled cells| -/

theorem qdScore_eq_meanAD_mul_filled :
    A.qdScore = A.meanAD * (A.filledCells.card : ℝ) := by
  simp only [meanAD]
  by_cases h : A.filledCells.card = 0
  · -- Archive is empty ⇒ both sides are 0
    rw [if_pos h]
    simp only [zero_mul]
    simp only [qdScore]
    have : A.filledCells = ∅ := Finset.card_eq_zero.mp h
    rw [this, Finset.sum_empty]
  · rw [if_neg h]
    rw [div_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr h

end Archive

/-! ================================================================
    ## Summary of formalised definitions and results
    ================================================================

    **Definitions** (all in namespace `Archive`):
    - `coverage`   : ℝ   — |filled| / (N*N)
    - `diversity`  : ℕ   — |{c ∈ filled | q(c) > 0.5}|
    - `peakAD'`    : ℝ   — max q(c) over filled cells (0 if empty)
    - `meanAD`     : ℝ   — (Σ q) / |filled|           (0 if empty)
    - `qdScore`    : ℝ   — Σ_{c ∈ filled} q(c)

    **Theorems**:
    - `qdScore_le_N_sq`           : qdScore ≤ N * N
    - `coverage_nonneg`           : 0 ≤ coverage
    - `coverage_le_one`           : coverage ≤ 1   (when N ≠ 0)
    - `meanAD_le_peakAD`          : meanAD ≤ peakAD (when archive non-empty)
    - `qdScore_eq_meanAD_mul_filled` : qdScore = meanAD * |filled|
-/
