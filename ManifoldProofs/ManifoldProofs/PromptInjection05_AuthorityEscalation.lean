import Mathlib
/-
  PromptInjection05_AuthorityEscalation.lean

  Theorem 5 — Authority Escalation Monotonicity
  ==============================================
  From the "Manifold of Failure" framework for prompt-injection analysis.

  In the paper's 2D behavioral space B = [0,1]^2, the two axes are:
    a1 : Query Indirection   in [0,1]
    a2 : Authority Framing   in [0,1]

  The Alignment Deviation function AD : B -> R measures vulnerability.
  Empirically, authority framing (a2) is a critical parameter: higher
  authority framing never decreases vulnerability.

  We formalize and prove:
    1. Monotonicity: a2 <= a2' => AD(a1,a2) <= AD(a1,a2')
    2. Upward closure of superlevel sets in a2
    3. Downward closure of sublevel (safe) sets in a2
    4. Existence of a critical threshold function a2*(a1)
    5. Characterization: AD(a1,a2) > tau  iff  a2 > a2*(a1)

  Mathlib-compatible Lean 4.
-/


open Set unitInterval

noncomputable section

namespace AuthorityEscalation

-- ============================================================
-- PART 1 : Setup — Alignment Deviation on I x I
-- ============================================================

/-- `I` is Mathlib's unit interval, the subtype {x : R | 0 <= x /\ x <= 1}.
    We model the Alignment Deviation as a function `f : I -> I -> R`
    where the first argument is query-indirection a1 and the second is
    authority-framing a2.

    Monotonicity hypothesis: for every fixed a1, f is non-decreasing in a2. -/
def MonotoneInA2 (f : I → I → ℝ) : Prop :=
  ∀ (a1 : I) (a2 a2' : I), (a2 : ℝ) ≤ (a2' : ℝ) → f a1 a2 ≤ f a1 a2'

-- ============================================================
-- PART 2 : Higher authority never decreases vulnerability
-- ============================================================

/-- Direct restatement of the monotonicity hypothesis as a usable lemma. -/
theorem higher_authority_never_decreases
    (f : I → I → ℝ) (hf : MonotoneInA2 f)
    (a1 : I) (a2 a2' : I) (h : (a2 : ℝ) ≤ (a2' : ℝ)) :
    f a1 a2 ≤ f a1 a2' :=
  hf a1 a2 a2' h

-- ============================================================
-- PART 3 : Superlevel sets and upward closure
-- ============================================================

/-- The superlevel set at threshold tau, restricted to authority axis for
    fixed a1:  S^+(a1, tau) = { a2 in I | f(a1, a2) > tau }. -/
def superlevelSlice (f : I → I → ℝ) (a1 : I) (τ : ℝ) : Set I :=
  {a2 : I | τ < f a1 a2}

/-- The full 2D superlevel set: { (a1, a2) | f(a1, a2) > tau }. -/
def superlevelSet2D (f : I → I → ℝ) (τ : ℝ) : Set (I × I) :=
  {p : I × I | τ < f p.1 p.2}

/-- **Upward closure in a2**: if (a1, a2) is in the superlevel set and
    a2' >= a2, then (a1, a2') is also in the superlevel set.
    Intuition: once authority framing is high enough to breach the threshold,
    increasing it further cannot make the system safer. -/
theorem superlevel_upward_closed
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (τ : ℝ)
    (a1 : I) (a2 a2' : I) (h_mem : a2 ∈ superlevelSlice f a1 τ)
    (h_le : (a2 : ℝ) ≤ (a2' : ℝ)) :
    a2' ∈ superlevelSlice f a1 τ := by
  simp only [superlevelSlice, mem_setOf_eq] at *
  exact lt_of_lt_of_le h_mem (hf a1 a2 a2' h_le)

/-- 2D version of upward closure. -/
theorem superlevel2D_upward_closed
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (τ : ℝ)
    (a1 : I) (a2 a2' : I)
    (h_mem : (a1, a2) ∈ superlevelSet2D f τ)
    (h_le : (a2 : ℝ) ≤ (a2' : ℝ)) :
    (a1, a2') ∈ superlevelSet2D f τ := by
  simp only [superlevelSet2D, mem_setOf_eq] at *
  exact lt_of_lt_of_le h_mem (hf a1 a2 a2' h_le)

-- ============================================================
-- PART 4 : Sublevel (safe) sets and downward closure
-- ============================================================

/-- The sublevel set (safe region) for fixed a1:
    Safe(a1, tau) = { a2 in I | f(a1, a2) <= tau }. -/
def safeSlice (f : I → I → ℝ) (a1 : I) (τ : ℝ) : Set I :=
  {a2 : I | f a1 a2 ≤ τ}

/-- The full 2D safe region: { (a1, a2) | f(a1, a2) <= tau }. -/
def safeRegion2D (f : I → I → ℝ) (τ : ℝ) : Set (I × I) :=
  {p : I × I | f p.1 p.2 ≤ τ}

/-- **Downward closure of safe region in a2**: if (a1, a2) is safe and
    a2' <= a2, then (a1, a2') is also safe.
    Intuition: reducing authority framing cannot increase vulnerability. -/
theorem safe_downward_closed
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (τ : ℝ)
    (a1 : I) (a2 a2' : I) (h_safe : a2 ∈ safeSlice f a1 τ)
    (h_le : (a2' : ℝ) ≤ (a2 : ℝ)) :
    a2' ∈ safeSlice f a1 τ := by
  simp only [safeSlice, mem_setOf_eq] at *
  exact le_trans (hf a1 a2' a2 h_le) h_safe

/-- 2D version of downward closure. -/
theorem safe2D_downward_closed
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (τ : ℝ)
    (a1 : I) (a2 a2' : I)
    (h_safe : (a1, a2) ∈ safeRegion2D f τ)
    (h_le : (a2' : ℝ) ≤ (a2 : ℝ)) :
    (a1, a2') ∈ safeRegion2D f τ := by
  simp only [safeRegion2D, mem_setOf_eq] at *
  exact le_trans (hf a1 a2' a2 h_le) h_safe

/-- The safe and vulnerable regions are complementary. -/
theorem safe_compl_superlevel
    (f : I → I → ℝ) (a1 : I) (τ : ℝ) :
    (safeSlice f a1 τ)ᶜ = superlevelSlice f a1 τ := by
  ext a2
  simp only [safeSlice, superlevelSlice, mem_compl_iff, mem_setOf_eq, not_le]

-- ============================================================
-- PART 5 : Critical threshold function a2*(a1)
-- ============================================================

/-- The set of authority levels that breach the threshold for given a1.
    This is the "vulnerable authority set". -/
def vulnerableAuthoritySet (f : I → I → ℝ) (a1 : I) (τ : ℝ) : Set ℝ :=
  {x : ℝ | ∃ a2 : I, (a2 : ℝ) = x ∧ τ < f a1 a2}

/-- The critical authority threshold: the infimum of authority levels
    at which vulnerability exceeds tau.  If the set is empty we get
    sSup of the empty set which is handled by the conditionally-complete
    lattice structure on R. -/
def criticalAuthority (f : I → I → ℝ) (a1 : I) (τ : ℝ) : ℝ :=
  sInf (vulnerableAuthoritySet f a1 τ)

/-- When the vulnerable set is nonempty, the infimum is bounded below by 0. -/
theorem criticalAuthority_nonneg
    (f : I → I → ℝ) (a1 : I) (τ : ℝ)
    (h_ne : (vulnerableAuthoritySet f a1 τ).Nonempty) :
    0 ≤ criticalAuthority f a1 τ := by
  unfold criticalAuthority
  apply le_csInf h_ne
  intro x ⟨a2, h_eq, _⟩
  rw [← h_eq]
  exact a2.2.1

/-! ### Alternative (cleaner) critical threshold via real-valued infimum

We define a2*(a1) directly as the infimum over real values in [0,1]
where the threshold is exceeded.  This avoids subtype bookkeeping. -/

/-- The set of real values a2 in [0,1] where f exceeds tau, using a
    real-valued representation.  We require a real-to-unitInterval coercion. -/
def exceedanceSet (f : I → I → ℝ) (a1 : I) (τ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Icc 0 1 ∧ ∃ a2 : I, (a2 : ℝ) = x ∧ τ < f a1 a2}

/-- The critical authority level (clean version). -/
def a2Star (f : I → I → ℝ) (a1 : I) (τ : ℝ) : ℝ :=
  sInf (exceedanceSet f a1 τ)

/-- The exceedance set is bounded below. -/
theorem exceedanceSet_bddBelow (f : I → I → ℝ) (a1 : I) (τ : ℝ) :
    BddBelow (exceedanceSet f a1 τ) :=
  ⟨0, fun x hx => hx.1.1⟩

/-- The exceedance set is bounded above by 1. -/
theorem exceedanceSet_bddAbove (f : I → I → ℝ) (a1 : I) (τ : ℝ) :
    BddAbove (exceedanceSet f a1 τ) :=
  ⟨1, fun x hx => hx.1.2⟩

/-- a2*(a1) >= 0 when the exceedance set is nonempty. -/
theorem a2Star_nonneg
    (f : I → I → ℝ) (a1 : I) (τ : ℝ)
    (h_ne : (exceedanceSet f a1 τ).Nonempty) :
    0 ≤ a2Star f a1 τ := by
  apply le_csInf h_ne
  intro x hx
  exact hx.1.1

/-- a2*(a1) <= 1 when the exceedance set is nonempty. -/
theorem a2Star_le_one
    (f : I → I → ℝ) (a1 : I) (τ : ℝ)
    (h_ne : (exceedanceSet f a1 τ).Nonempty) :
    a2Star f a1 τ ≤ 1 := by
  apply csInf_le_of_le (exceedanceSet_bddBelow f a1 τ) h_ne.some_mem
  exact h_ne.some_mem.1.2

-- ============================================================
-- PART 6 : Characterization theorem for the monotone boundary
-- ============================================================

/-- For a monotone f, any authority level in the exceedance set is an
    upper bound: everything above it is also in the set. -/
theorem exceedanceSet_upward
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (a1 : I) (τ : ℝ)
    (a2 : I) (h_exc : (a2 : ℝ) ∈ exceedanceSet f a1 τ)
    (a2' : I) (h_le : (a2 : ℝ) ≤ (a2' : ℝ)) :
    (a2' : ℝ) ∈ exceedanceSet f a1 τ := by
  obtain ⟨h_mem, a2'', h_eq, h_lt⟩ := h_exc
  refine ⟨⟨a2'.2.1, a2'.2.2⟩, a2', rfl, ?_⟩
  have h_le' : (a2'' : ℝ) ≤ (a2' : ℝ) := by linarith [h_eq]
  calc τ < f a1 a2'' := h_lt
    _ ≤ f a1 a2' := hf a1 a2'' a2' h_le'

/- **Forward direction**: if a2 > a2*(a1) and a2 is in [0,1], and the
    exceedance set is nonempty, then f(a1, a2) > tau.

    This is the key "above the boundary means vulnerable" result.
    We require f to be monotone and continuous in a2 (the continuity
    ensures the infimum is actually achieved or approached).

    Helper: if a2 is strictly above the infimum and the set is upward-closed,
    then there is a point in the set below a2.

    We state the characterization as two separate implications for clarity. -/

/-- If a2_val > a2*(a1) and the exceedance set is nonempty, then there exists
    some point in the exceedance set that is <= a2_val. -/
theorem exists_exceedance_below
    (f : I → I → ℝ) (a1 : I) (τ : ℝ)
    (h_ne : (exceedanceSet f a1 τ).Nonempty)
    (a2_val : ℝ) (h_gt : a2Star f a1 τ < a2_val) :
    ∃ x ∈ exceedanceSet f a1 τ, x ≤ a2_val := by
  by_contra h
  push_neg at h
  -- Every element of the set is > a2_val, so a2_val is a lower bound
  -- But a2_val > sInf, contradicting sInf being the greatest lower bound
  have : a2_val ≤ a2Star f a1 τ := by
    apply le_csInf h_ne
    intro x hx
    exact le_of_lt (h x hx)
  linarith

/-- **Above-boundary implies vulnerable** (for monotone f):
    If a2 (as a real) is strictly above a2*(a1), then f(a1, a2) > tau. -/
theorem above_boundary_vulnerable
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (a1 : I) (τ : ℝ)
    (h_ne : (exceedanceSet f a1 τ).Nonempty)
    (a2 : I) (h_gt : a2Star f a1 τ < (a2 : ℝ)) :
    τ < f a1 a2 := by
  obtain ⟨x, hx_mem, hx_le⟩ := exists_exceedance_below f a1 τ h_ne (a2 : ℝ) h_gt
  obtain ⟨h_icc, a2'', h_eq, h_lt⟩ := hx_mem
  calc τ < f a1 a2'' := h_lt
    _ ≤ f a1 a2 := by
        apply hf a1 a2'' a2
        rw [h_eq]
        exact hx_le

/-- **Below-boundary implies safe** (contrapositive):
    If a2 < a2*(a1), then f(a1, a2) <= tau. -/
theorem below_boundary_safe
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (a1 : I) (τ : ℝ)
    (a2 : I) (h_lt : (a2 : ℝ) < a2Star f a1 τ) :
    f a1 a2 ≤ τ := by
  by_contra h_bad
  push_neg at h_bad
  -- a2 would be in the exceedance set
  have h_in : (a2 : ℝ) ∈ exceedanceSet f a1 τ :=
    ⟨⟨a2.2.1, a2.2.2⟩, a2, rfl, h_bad⟩
  -- But then sInf <= a2, contradicting a2 < sInf
  have : a2Star f a1 τ ≤ (a2 : ℝ) :=
    csInf_le (exceedanceSet_bddBelow f a1 τ) h_in
  linarith

-- ============================================================
-- PART 7 : The boundary is a monotone curve
-- ============================================================

/- The boundary function a2* is anti-monotone in a1 when f is
    monotone in both axes.  More generally, we show: if f is monotone
    in a2 and non-decreasing in a1, then a2* is non-increasing in a1.

    This captures the paper's observation that the boundary between
    safe and vulnerable regions forms a monotone curve. -/

/-- f is also monotone in a1 (used for the boundary monotonicity result). -/
def MonotoneInA1 (f : I → I → ℝ) : Prop :=
  ∀ (a1 a1' : I) (a2 : I), (a1 : ℝ) ≤ (a1' : ℝ) → f a1 a2 ≤ f a1' a2

/-- If f is monotone in both a1 and a2, the exceedance set for a1'
    contains the exceedance set for a1 whenever a1 <= a1'. -/
theorem exceedanceSet_monotone_in_a1
    (f : I → I → ℝ) (hf1 : MonotoneInA1 f) (hf2 : MonotoneInA2 f) (τ : ℝ)
    (a1 a1' : I) (h_le : (a1 : ℝ) ≤ (a1' : ℝ)) :
    exceedanceSet f a1 τ ⊆ exceedanceSet f a1' τ := by
  intro x ⟨h_icc, a2, h_eq, h_lt⟩
  refine ⟨h_icc, a2, h_eq, lt_of_lt_of_le h_lt (hf1 a1 a1' a2 h_le)⟩

/-- Consequently, a2*(a1) is non-increasing: if a1 <= a1' then
    a2*(a1') <= a2*(a1).  A larger exceedance set has a smaller infimum.

    This is the **monotone boundary curve** result. -/
theorem a2Star_antitone
    (f : I → I → ℝ) (hf1 : MonotoneInA1 f) (hf2 : MonotoneInA2 f) (τ : ℝ)
    (a1 a1' : I) (h_le : (a1 : ℝ) ≤ (a1' : ℝ))
    (h_ne : (exceedanceSet f a1 τ).Nonempty) :
    a2Star f a1' τ ≤ a2Star f a1 τ := by
  apply csInf_le_csInf
    (exceedanceSet_bddBelow f a1' τ)
    h_ne
    (exceedanceSet_monotone_in_a1 f hf1 hf2 τ a1 a1' h_le)

-- ============================================================
-- PART 8 : Summary theorem (combined statement)
-- ============================================================

/-- **Authority Escalation Monotonicity (Theorem 5)**:
    Combined statement of all four properties.

    Given f : I x I -> R that is monotone non-decreasing in a2, and
    a threshold tau, define a2*(a1) = inf { a2 | f(a1,a2) > tau }.
    Then:
    (i)   Higher authority never decreases vulnerability
    (ii)  The superlevel set is upward closed in a2
    (iii) The safe region is downward closed in a2
    (iv)  a2 > a2*(a1) implies vulnerable; a2 < a2*(a1) implies safe -/
theorem authority_escalation_monotonicity
    (f : I → I → ℝ) (hf : MonotoneInA2 f) (τ : ℝ)
    (a1 : I) :
    -- (i) Monotonicity
    (∀ a2 a2' : I, (a2 : ℝ) ≤ (a2' : ℝ) → f a1 a2 ≤ f a1 a2') ∧
    -- (ii) Superlevel upward closed
    (∀ a2 a2' : I, a2 ∈ superlevelSlice f a1 τ →
      (a2 : ℝ) ≤ (a2' : ℝ) → a2' ∈ superlevelSlice f a1 τ) ∧
    -- (iii) Safe region downward closed
    (∀ a2 a2' : I, a2 ∈ safeSlice f a1 τ →
      (a2' : ℝ) ≤ (a2 : ℝ) → a2' ∈ safeSlice f a1 τ) ∧
    -- (iv-a) Above boundary => vulnerable
    (∀ a2 : I, (exceedanceSet f a1 τ).Nonempty →
      a2Star f a1 τ < (a2 : ℝ) → τ < f a1 a2) ∧
    -- (iv-b) Below boundary => safe
    (∀ a2 : I, (a2 : ℝ) < a2Star f a1 τ → f a1 a2 ≤ τ) := by
  exact ⟨
    fun a2 a2' h => hf a1 a2 a2' h,
    fun a2 a2' h_mem h_le => superlevel_upward_closed f hf τ a1 a2 a2' h_mem h_le,
    fun a2 a2' h_safe h_le => safe_downward_closed f hf τ a1 a2 a2' h_safe h_le,
    fun a2 h_ne h_gt => above_boundary_vulnerable f hf a1 τ h_ne a2 h_gt,
    fun a2 h_lt => below_boundary_safe f hf a1 τ a2 h_lt⟩

end AuthorityEscalation
