import Mathlib

/-!
# Manifold of Failure — Part 10: Gradient-Based Attacks

We formalize properties of gradient-based adversarial attacks on the failure
manifold. The key results are:

- Norm-squared properties: nonnegativity, zero-iff-zero, positivity for nonzero
- Real inner product self-pairing equals norm squared
- Inner product self-pairing is nonneg (derived from norm squared)
- Gradient-derivative connection via the Riesz representation
- Critical point characterization via the Fréchet derivative
- Discrete ascent: a positive derivative guarantees local improvement
- Existence of an ascent step size
- Multivariate ascent: nonzero derivative implies improvability

These are the mathematical foundations for understanding why gradient-based
attacks (e.g., PGD, FGSM) reliably find failure modes on the manifold.

## Main results

- `norm_sq_nonneg` — ‖x‖² ≥ 0
- `norm_sq_eq_zero` — ‖x‖² = 0 ↔ x = 0
- `norm_sq_pos_of_ne_zero` — x ≠ 0 → 0 < ‖x‖²
- `real_inner_self_eq_norm_sq'` — ⟪v, v⟫_ℝ = ‖v‖²
- `real_inner_self_nonneg'` — 0 ≤ ⟪v, v⟫_ℝ (from norm squared)
- `fderiv_apply_eq_inner_gradient` — HasGradientAt f g x → fderiv ℝ f x v = ⟪g, v⟫_ℝ
- `critical_point_iff_fderiv_eq_zero` — ‖f'‖ = 0 ↔ f' = 0
- `discrete_ascent_improvement` — positive derivative ⟹ eventual local improvement
- `ascent_direction_exists` — ∃ ε > 0, ∀ h ∈ (0,ε), f(x+h) > f(x)
- `multivariate_ascent_direction` — f' ≠ 0 → ∃ v ε > 0, f(x + ε • v) > f(x)
-/

open Set Filter Topology InnerProductSpace

noncomputable section

namespace MoF

/-! ## 1. Norm-Squared Properties -/

/-- The square of a norm is nonneg. -/
theorem norm_sq_nonneg {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    0 ≤ ‖x‖ ^ 2 :=
  sq_nonneg ‖x‖

/-- The square of a norm is zero iff the vector is zero. -/
theorem norm_sq_eq_zero {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ ^ 2 = 0 ↔ x = 0 := by
  rw [sq, mul_self_eq_zero, norm_eq_zero]

/-- If a vector is nonzero, its norm squared is positive. -/
theorem norm_sq_pos_of_ne_zero {E : Type*} [NormedAddCommGroup E] {x : E}
    (hx : x ≠ 0) : 0 < ‖x‖ ^ 2 := by
  rw [sq]
  exact mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hx)

/-! ## 2. Real Inner Product Properties

These theorems use actual inner products, connecting `⟪v, v⟫_ℝ` to `‖v‖²`
and deriving nonnegativity from this identity. -/

/-- In a real inner product space, `⟪v, v⟫_ℝ = ‖v‖²`. This is the real-valued
    version of the fundamental identity connecting inner products and norms. -/
theorem real_inner_self_eq_norm_sq' {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (v : F) : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 :=
  real_inner_self_eq_norm_sq v

/-- In a real inner product space, `0 ≤ ⟪v, v⟫_ℝ`. This follows directly
    from the identity `⟪v, v⟫_ℝ = ‖v‖²` and nonnegativity of squares. -/
theorem real_inner_self_nonneg' {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (v : F) : 0 ≤ ⟪v, v⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq']
  exact sq_nonneg ‖v‖

/-! ## 3. Gradient-Derivative Connection

The gradient connects the Fréchet derivative to the inner product via the
Riesz representation: if `HasGradientAt f g x`, then `fderiv ℝ f x v = ⟪g, v⟫_ℝ`.
-/

/-- If `f` has gradient `g` at `x`, then the Fréchet derivative applied to any
    direction `v` equals the inner product `⟪g, v⟫_ℝ`. This is the Riesz
    representation theorem in action. -/
theorem fderiv_apply_eq_inner_gradient {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {g : F} {x : F}
    (hf : HasGradientAt f g x) (v : F) :
    fderiv ℝ f x v = ⟪g, v⟫_ℝ := by
  have h1 : HasFDerivAt f (toDual ℝ F g) x := hf.hasFDerivAt
  rw [h1.fderiv]
  simp [InnerProductSpace.toDual_apply_apply]

/-! ## 4. Critical Point Characterization -/

/-- A continuous linear map has zero operator norm iff it is the zero map.
    This characterizes critical points: `f' = 0` iff the derivative acts
    trivially in all directions. -/
theorem critical_point_iff_fderiv_eq_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f' : E →L[ℝ] F) : ‖f'‖ = 0 ↔ f' = 0 := by
  constructor
  · intro h
    ext v
    have hle : ‖f' v‖ ≤ ‖f'‖ * ‖v‖ := f'.le_opNorm v
    rw [h, zero_mul] at hle
    exact norm_le_zero_iff.mp hle
  · intro h
    simp [h]

/-- A gradient (or any vector) is zero iff its norm is zero.
    This characterizes critical points of differentiable functions. -/
theorem gradient_zero_iff_critical {E : Type*} [NormedAddCommGroup E]
    (v : E) : ‖v‖ = 0 ↔ v = 0 :=
  norm_eq_zero

/-! ## 5. Discrete Ascent Improvement

The core theorem: if f has a positive derivative at x, then there exists
a positive step size that improves f. This is the mathematical justification
for gradient-based attacks succeeding in practice. -/

/-- If f : ℝ → ℝ has a strictly positive derivative at x, then eventually
    for positive h near 0, f(x+h) > f(x). -/
theorem discrete_ascent_improvement {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : 0 < d) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), f (x + h) > f x := by
  -- The derivative being d > 0 means h⁻¹ * (f(x+h) - f(x)) → d as h → 0⁺
  have slope_tends : Tendsto (fun t => t⁻¹ * (f (x + t) - f x)) (𝓝[>] 0) (𝓝 d) := by
    have := hf.tendsto_slope_zero_right
    simp only [smul_eq_mul] at this
    exact this
  -- Since d > 0, eventually the slope quotient is > d/2 > 0
  have h_event : ∀ᶠ t in 𝓝[>] (0 : ℝ), d / 2 < t⁻¹ * (f (x + t) - f x) := by
    apply (slope_tends.eventually (Ioi_mem_nhds (by linarith : d / 2 < d))).mono
    intro t ht
    exact ht
  -- For t in 𝓝[>] 0, we have t > 0
  have h_pos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t :=
    eventually_nhdsWithin_of_forall fun t ht => ht
  -- Combine: for t > 0 with positive slope quotient, f(x+t) > f(x)
  filter_upwards [h_event, h_pos] with t h_slope ht_pos
  have h_inv_pos : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht_pos
  have h_diff_pos : 0 < f (x + t) - f x := by
    by_contra h_neg
    push_neg at h_neg
    have : t⁻¹ * (f (x + t) - f x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_inv_pos) h_neg
    linarith
  linarith

/-- If f : ℝ → ℝ has a strictly positive derivative at x, there exists
    ε > 0 such that for all h ∈ (0, ε), f(x + h) > f(x).

    This is the constructive version that yields an explicit step-size
    interval, justifying the convergence of gradient ascent. -/
theorem ascent_direction_exists {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (hd : 0 < d) :
    ∃ ε > 0, ∀ h, h ∈ Ioo 0 ε → f (x + h) > f x := by
  -- From the eventually result, extract a concrete ε
  have ev := discrete_ascent_improvement hf hd
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at ev
  obtain ⟨u, hu_pos, hu_sub⟩ := ev
  exact ⟨u, hu_pos, fun h hh => hu_sub hh⟩

/-! ## 6. Multivariate Ascent Direction

The n-dimensional generalization: if the Fréchet derivative is nonzero,
there exists a direction and step size giving strict improvement. -/

/-- Helper: restricting a function to a line through x in direction v gives
    a function whose derivative at 0 is f' v. -/
theorem hasFDerivAt_line_restrict {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x v : E}
    (hf : HasFDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (f' v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h_smul : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const v
    simp only [one_smul] at h_smul
    have h_const : HasDerivAt (fun _ : ℝ => x) 0 0 := hasDerivAt_const 0 x
    have := h_const.add h_smul
    simp only [zero_add] at this
    exact this
  have hx_eq : x + (0 : ℝ) • v = x := by simp
  have h2 := (hx_eq ▸ hf).comp_hasDerivAt (0 : ℝ) h1
  simp at h2
  exact h2

/-- If `f : E → ℝ` has Fréchet derivative `f'` at `x` and `f' ≠ 0`, then
    there exists a direction `v` and step size `ε > 0` such that
    `f(x + ε • v) > f(x)`.

    This is the multivariate foundation for gradient-based attacks:
    a nonzero derivative always provides an ascent direction. -/
theorem multivariate_ascent_direction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hf' : f' ≠ 0) :
    ∃ v : E, ∃ ε : ℝ, ε > 0 ∧ f (x + ε • v) > f x := by
  -- Since f' ≠ 0, there exists v with f' v ≠ 0
  have ⟨v, hv⟩ : ∃ v, f' v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf' (ContinuousLinearMap.ext h)
  -- Pick the right direction: if f' v > 0 use v, if f' v < 0 use -v
  set w := if 0 < f' v then v else -v with hw_def
  have hd : 0 < f' w := by
    simp only [hw_def]
    split_ifs with h
    · exact h
    · push_neg at h
      simp [map_neg]
      exact lt_of_le_of_ne h (fun h_eq => hv h_eq)
  have hline := hasFDerivAt_line_restrict (v := w) hf
  -- Use the eventually filter to extract a concrete witness
  have ev := discrete_ascent_improvement hline hd
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset] at ev
  obtain ⟨ε, hε_mem, hε_sub⟩ := ev
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hmem : ε / 2 ∈ Ioo (0 : ℝ) ε := ⟨by linarith, by linarith⟩
  have hstep := hε_sub hmem
  -- hstep : f (x + (0 + ε / 2) • w) > f (x + 0 • w), simplify
  simp only [zero_add, zero_smul, add_zero] at hstep
  refine ⟨w, ε / 2, ?_, hstep⟩
  linarith

end MoF
