# Four More Predictions from Existing Theorems

---

## 11. Random red-teaming has a computable query budget — and it's small

**From:** `hit_probability_tends_to_one` (MoF_Cost_03) + `basin_measure_ge_ball_pos` (MoF_Cost_02) + `lipschitz_basin_ball` (MoF_04).

**Chain:** If the unsafe region has positive measure μ(U_τ) = p > 0 under any measure positive on open sets, then random uniform sampling hits U_τ with probability 1 − (1−p)^n after n queries. By `hit_probability_tends_to_one`, this → 1. Expected probes to first hit: 1/p.

The Lipschitz basin ball theorem gives a *lower bound* on p: if any point has f(x₀) > τ, then the ball B(x₀, (f(x₀)−τ)/L) ⊆ U_τ. So p ≥ μ(B(x₀, r))/μ(X) where r = (f(x₀)−τ)/L. On the 2D grid from the empirical study, Llama has basin rate 93.9%, so p ≈ 0.94 — expected 1.06 queries. Even GPT-OSS at 64.3% needs only ~1.6 queries.

**Prediction:** For any model with basin rate q on a behavioral grid, a random attacker finds a jailbreak in expected ⌈1/q⌉ queries. This is **dimension-independent** (from `attack_cost_upper_bound`). The defender has no comparable shortcut — defense cost is N^d. This predicts that even naive random fuzzing is a credible attack strategy against models with non-trivial basin rates, and the attacker advantage ratio q · N^d → ∞ with dimension.

**Testable:** Sample random points in a model's prompt space. Measure queries-to-first-jailbreak. Compare to 1/(empirical basin rate). They should match within a factor of 2.

---

## 12. Safety patches have a quantitative blast radius that causes capability regression

**From:** `patching_nonlocal` (MoF_Adv_03) + `boundary_shift_bound` (MoF_Adv_03) + `basin_hausdorff_distance_bound` (MoF_Adv_03).

**Chain:** Suppose a safety patch changes the alignment surface from f to g with ‖f − g‖∞ ≤ ε. By `basin_hausdorff_distance_bound`, the symmetric difference of the unsafe basins — inputs that change classification — is contained in {x : |f(x) − τ| ≤ ε}. This is the **ε-band**: points within ε of the boundary.

By `boundary_shift_bound`, every boundary point of g has |f(z) − τ| ≤ ε — the boundary moves by at most ε. But critically, by `patching_nonlocal`, there exist perturbations where a point far from the original boundary (f(z) = τ, g(z) > τ) is affected. The blast radius of each patch is at least (f(x) − τ)/L around the patched point x (from the Lipschitz basin ball, applied in reverse: shrinking the basin at x requires changing f within this ball).

**Prediction:** When a model is fine-tuned to patch k jailbreaks, the behavioral change extends to a ball of radius r_i = (f(x_i) − τ)/L around each patched prompt x_i. These balls may overlap. The total affected volume ≤ Σ μ(B(x_i, r_i)) but can be much larger if patches are clustered. Deeper jailbreaks (higher AD) have larger blast radii. This is the mechanism of "capability regression" after safety patches: fixing deep vulnerabilities necessarily changes behavior on a large region of prompt space, including benign prompts near the boundary.

**Testable:** After a safety patch, measure performance on benign tasks at varying semantic distances from the patched jailbreaks. Performance degradation should decay with distance, with decay rate proportional to 1/L.

---

## 13. On a convex embedding space, all jailbreaks are reachable from any single jailbreak by interpolation

**From:** `basin_connected_of_convex_domain` (MoF_Adv_01) + `convex_basin_path_connected` (MoF_Adv_05).

**Chain:** If the alignment deviation f is quasiconcave on a convex embedding space (e.g., the model's internal representation space), then by `concave_superlevel_convex` / `quasiconcave_superlevel_convex`, the superlevel set {f > τ} is convex. A convex set is connected (`convex_basin_connected`), and in a normed space, path-connected (`convex_basin_path_connected`). This means: given any two jailbreak prompts x₁, x₂ ∈ U_τ, the straight line α·x₁ + (1−α)·x₂ for α ∈ [0,1] stays entirely in U_τ.

No moat. No isolated vulnerability islands. The entire unsafe region is a single connected blob in embedding space.

**Prediction:** If a model's alignment surface is quasiconcave in embedding space, then:
- Linear interpolation between any two known jailbreaks produces a continuous family of jailbreaks.
- There are no "isolated" jailbreak families that require discrete jumps to reach.
- A single jailbreak, combined with gradient information, can generate an entire connected manifold of jailbreaks via interpolation and local search.

When quasiconcavity fails (adversarially-trained or very rough surfaces), the basin fragments into disconnected components — but each component is still individually connected.

**Testable:** Take two known jailbreaks. Embed them. Interpolate in embedding space at α = 0, 0.1, ..., 1.0. Decode each interpolant and test for jailbreak success. Under quasiconcavity, all 11 points should jailbreak. Under fragmentation, expect a gap (some α values are safe).

---

## 14. There is a Pareto frontier of (safety threshold, unsafe volume) — and wrapper defenses cannot cross it

**From:** `basin_measure_monotone_threshold` (MoF_Adv_10) + `defense_incompleteness` (MoF_08) + `markov_real_basin` (MoF_Adv_10).

**Chain:** `basin_measure_monotone_threshold` proves: τ₁ ≤ τ₂ ⟹ μ({f > τ₂}) ≤ μ({f > τ₁}). Raising the threshold shrinks the unsafe region monotonically. The `markov_real_basin` bound gives μ({f ≥ ε}) ≤ (1/ε) · ∫f dμ — a Markov-type upper bound on the unsafe volume in terms of the mean AD.

But `defense_incompleteness` says: for any τ where both S_τ and U_τ are nonempty, the trilemma holds. So the defender can choose τ to minimize μ(U_τ), but cannot reach μ(U_τ) = 0 without either making U_τ empty (the GPT-5-Mini escape: push the entire surface below τ) or violating one of the three conditions.

The Pareto frontier is the function τ ↦ μ({f > τ}). It is monotone decreasing (proved), bounded below by 0, and reaches 0 only if f(x) < τ for all x. The wrapper defense can choose where on this curve to operate (by choosing τ), but cannot move below it.

**Prediction:** For any fixed model:
- Plot τ vs. (jailbreak rate at threshold τ). The curve is monotone decreasing and convex (from Markov).
- A wrapper defense operating at threshold τ has jailbreak rate ≥ μ({f > τ}) / μ(X). No wrapper can beat this curve.
- Lowering τ (stricter safety) reduces jailbreaks but increases false positive rate (blocking safe prompts near the boundary). The optimal τ depends on the cost ratio of false positives to jailbreaks.
- The only way to shift the entire Pareto curve down is to change the model itself (training-time intervention), not the wrapper.

**Testable:** Sweep τ from 0 to 1 on a fixed model's behavioral grid. Measure (false positive rate, jailbreak rate) at each τ. Fit the Pareto curve. Apply a wrapper defense and verify that the (FP, jailbreak) operating point lies on or above the curve, never below it.
