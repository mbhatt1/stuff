import Mathlib

/-!
# Manifold of Failure — Part 7: Authority Monotonicity (N-Dimensional)

**Core theorem: Authority escalation monotonically increases vulnerability.**

We work with `f : Y → ℝ → ℝ` where `Y` is an arbitrary type representing all
non-authority axes (e.g. `Y = ℝ^n` for an n-dimensional indirection space) and
the `ℝ` argument is the authority axis. The authority axis remains `ℝ` because
several theorems (critical threshold, monotone boundary) rely on the
intermediate value theorem, which requires a connected ordered topological space.

## Main results

1. `authority_escalation` — vulnerability is upward-closed in authority.
2. `safe_downward_closed` — safety is downward-closed in authority.
3. `vulnerability_superlevel_upward` — the superlevel set is upward-closed.
4. `safe_sublevel_downward` — the sublevel set is downward-closed.
5. `critical_threshold_exists` — IVT gives a critical authority threshold.
6. `monotone_boundary` — higher indirection lowers the authority needed to breach.
7. `monotone_boundary_from_origin` — specialisation where the safe base-case is
   at zero authority.
8. `monotone_boundary_self` — reflexivity: if indirection stays the same, the
   boundary is unchanged.
-/

noncomputable section

open Set Topology

namespace MoF

/-! ## Definitions -/

/-- `f` is monotone (non-decreasing) in the authority axis for every `y : Y`. -/
def MonotoneInAuthority {Y : Type*} (f : Y → ℝ → ℝ) : Prop :=
  ∀ y, Monotone (f y)

/-- The point `(y, x)` is vulnerable: the attack deviation exceeds threshold `τ`. -/
def VulnerableAt {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y) (x : ℝ) : Prop :=
  f y x > τ

/-- The point `(y, x)` is safe: the attack deviation is at most `τ`. -/
def SafeAt {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y) (x : ℝ) : Prop :=
  f y x ≤ τ

/-! ## 1. Authority Escalation -/

/--
If `f` is monotone in authority and `(y, x)` is vulnerable, then every
`x' ≥ x` is also vulnerable.  Proof: `f y x' ≥ f y x > τ`.
-/
theorem authority_escalation
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y) (x x' : ℝ)
    (hm : MonotoneInAuthority f)
    (hv : VulnerableAt f τ y x)
    (h : x ≤ x') :
    VulnerableAt f τ y x' := by
  unfold VulnerableAt at *
  exact lt_of_lt_of_le hv (hm y h)

/-! ## 2. Safe Downward Closed -/

/--
If `f` is monotone in authority and `(y, x)` is safe, then every
`x' ≤ x` is also safe.  Proof: `f y x' ≤ f y x ≤ τ`.
-/
theorem safe_downward_closed
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y) (x x' : ℝ)
    (hm : MonotoneInAuthority f)
    (hs : SafeAt f τ y x)
    (h : x' ≤ x) :
    SafeAt f τ y x' := by
  unfold SafeAt at *
  exact le_trans (hm y h) hs

/-! ## 3. Vulnerability Superlevel Set Is Upward-Closed -/

/--
For fixed `y`, the superlevel set `{x | f y x > τ}` is upward-closed
under `MonotoneInAuthority`.
-/
theorem vulnerability_superlevel_upward
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y)
    (hm : MonotoneInAuthority f) :
    ∀ x x', x ∈ {a | f y a > τ} → x ≤ x' → x' ∈ {a | f y a > τ} := by
  intro x x' hx hle
  simp only [mem_setOf_eq] at *
  exact lt_of_lt_of_le hx (hm y hle)

/-! ## 4. Safe Sublevel Set Is Downward-Closed -/

/--
For fixed `y`, the sublevel set `{x | f y x ≤ τ}` is downward-closed
under `MonotoneInAuthority`.
-/
theorem safe_sublevel_downward
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y)
    (hm : MonotoneInAuthority f) :
    ∀ x x', x ∈ {a | f y a ≤ τ} → x' ≤ x → x' ∈ {a | f y a ≤ τ} := by
  intro x x' hx hle
  simp only [mem_setOf_eq] at *
  exact le_trans (hm y hle) hx

/-! ## 5. Critical Threshold Exists (IVT on 1-D Slice) -/

/--
If `f y ·` is continuous and there exist a safe point and a vulnerable point,
then the intermediate value theorem gives a critical authority level `x⋆`
where `f y x⋆ = τ`.
-/
theorem critical_threshold_exists
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y)
    (hc : Continuous (f y))
    (x_lo : ℝ) (h_lo : f y x_lo ≤ τ)
    (x_hi : ℝ) (h_hi : f y x_hi > τ) :
    ∃ x_star : ℝ, f y x_star = τ := by
  by_cases h : f y x_lo = τ
  · exact ⟨x_lo, h⟩
  · have hlt : f y x_lo < τ := lt_of_le_of_ne h_lo h
    have h_conn : IsPreconnected (Set.uIcc x_lo x_hi) := isPreconnected_uIcc
    have hlo_mem : x_lo ∈ Set.uIcc x_lo x_hi := Set.left_mem_uIcc
    have hhi_mem : x_hi ∈ Set.uIcc x_lo x_hi := Set.right_mem_uIcc
    obtain ⟨c, _, hc⟩ := h_conn.intermediate_value₂ hlo_mem hhi_mem
      hc.continuousOn continuous_const.continuousOn (le_of_lt hlt) (le_of_lt h_hi)
    exact ⟨c, hc⟩

/-! ## 6. Monotone Boundary -/

/--
`MonotoneInIndirection f` means for each `y₁ ≤ y₂` (under a preorder on `Y`)
and each authority level `x`, we have `f y₁ x ≤ f y₂ x`.
-/
def MonotoneInIndirection {Y : Type*} [Preorder Y] (f : Y → ℝ → ℝ) : Prop :=
  ∀ x, Monotone (f · x)

/--
Under monotonicity in both axes, if `f y x⋆ = τ` and `y ≤ y'` and
`f y' ·` is continuous, there exists `x⋆' ≤ x⋆` with `f y' x⋆' = τ`.

Intuition: higher indirection makes it easier to attack, so the critical
authority threshold drops — you need less authority to breach.

**Why the `x_lo` / `h_lo` hypothesis is necessary.**  `MonotoneInIndirection`
tells us `y ≤ y' → f y x ≤ f y' x`, so increasing indirection *raises*
attack deviation.  A safe point at the *original* indirection level `y` does
**not** transfer to the higher level `y'`.  Without an explicit witness that
`f y'` still dips to (or below) `τ` somewhere, the IVT cannot be applied and
the boundary-drop conclusion is vacuously blocked.  The corollary
`monotone_boundary_from_origin` packages the common case where the model is
safe at zero authority for the new indirection level (`f y' 0 ≤ τ`).
-/
theorem monotone_boundary
    {Y : Type*} [Preorder Y]
    (f : Y → ℝ → ℝ) (τ : ℝ) (y y' : Y) (x_star : ℝ)
    (hm_auth : MonotoneInAuthority f)
    (hm_ind : MonotoneInIndirection f)
    (hcont : Continuous (f y'))
    (h_eq : f y x_star = τ)
    (h_le : y ≤ y')
    (x_lo : ℝ) (h_lo : f y' x_lo ≤ τ) :
    ∃ x_star' : ℝ, x_star' ≤ x_star ∧ f y' x_star' = τ := by
  have h_hi : f y' x_star ≥ τ := by
    rw [← h_eq]
    exact hm_ind x_star h_le
  by_cases heq : f y' x_star = τ
  · exact ⟨x_star, le_refl _, heq⟩
  · have h_gt : f y' x_star > τ := lt_of_le_of_ne h_hi (Ne.symm heq)
    by_cases hlo_eq : f y' x_lo = τ
    · exact ⟨x_lo, by
        by_contra h_not_le
        push_neg at h_not_le
        have := hm_auth y' (le_of_lt h_not_le)
        linarith, hlo_eq⟩
    · have hlt_lo : f y' x_lo < τ := lt_of_le_of_ne h_lo hlo_eq
      have hle_lo_star : x_lo ≤ x_star := by
        by_contra h_not_le
        push_neg at h_not_le
        have := hm_auth y' (le_of_lt h_not_le)
        linarith
      have h_ivt : ∃ c ∈ Set.Icc x_lo x_star, f y' c = τ := by
        have h_conn : IsPreconnected (Set.Icc x_lo x_star) := isPreconnected_Icc
        have hlo_mem : x_lo ∈ Set.Icc x_lo x_star := ⟨le_refl _, hle_lo_star⟩
        have hhi_mem : x_star ∈ Set.Icc x_lo x_star := ⟨hle_lo_star, le_refl _⟩
        obtain ⟨c, hc_mem, hc_eq⟩ := h_conn.intermediate_value₂ hlo_mem hhi_mem
          hcont.continuousOn continuous_const.continuousOn (le_of_lt hlt_lo) (le_of_lt h_gt)
        exact ⟨c, hc_mem, hc_eq⟩
      obtain ⟨c, hc_mem, hc_eq⟩ := h_ivt
      exact ⟨c, hc_mem.2, hc_eq⟩

/-! ## 7. Monotone Boundary — Zero-Authority Specialisation -/

/--
Common special case of `monotone_boundary`: assume the model is safe at zero
authority for the higher indirection level (`f y' 0 ≤ τ`).  This is a natural
base-case — at zero authority the attacker has no leverage.
-/
theorem monotone_boundary_from_origin
    {Y : Type*} [Preorder Y]
    (f : Y → ℝ → ℝ) (τ : ℝ) (y y' : Y) (x_star : ℝ)
    (hm_auth : MonotoneInAuthority f)
    (hm_ind : MonotoneInIndirection f)
    (hcont : Continuous (f y'))
    (h_eq : f y x_star = τ)
    (h_le : y ≤ y')
    (h_origin : f y' 0 ≤ τ) :
    ∃ x_star' : ℝ, x_star' ≤ x_star ∧ f y' x_star' = τ :=
  monotone_boundary f τ y y' x_star hm_auth hm_ind hcont h_eq h_le 0 h_origin

/-! ## 8. Monotone Boundary — Reflexivity -/

/--
When the indirection level does not change (`y' = y`), the boundary stays
exactly where it was.  This is the reflexivity / identity case.
-/
theorem monotone_boundary_self
    {Y : Type*} (f : Y → ℝ → ℝ) (τ : ℝ) (y : Y) (x_star : ℝ)
    (h_eq : f y x_star = τ) :
    ∃ x_star' : ℝ, x_star' ≤ x_star ∧ f y x_star' = τ :=
  ⟨x_star, le_refl _, h_eq⟩

end MoF
