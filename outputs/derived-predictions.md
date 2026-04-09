# Derived Predictions: What the Defense Trilemma Implies About LLMs

Each prediction below follows from theorems already proved in the Lean artifact. No new mathematics — only instantiation of existing results to specific LLM scenarios.

---

## 1. Safety fine-tuning has diminishing marginal returns

**From:** Interior Stability (Thm A.7, `MoF_Adv_03`):
If ‖f − g‖∞ ≤ ε, then f(x) > τ + ε ⟹ g(x) > τ.

**Derivation:** A round of safety fine-tuning (RLHF, DPO) shifts the alignment surface by some ε₁. This clears the shell {τ < f(x) ≤ τ + ε₁} but leaves {f(x) > τ + ε₁} unsafe. A second round shifts by ε₂, clearing {τ + ε₁ < f(x) ≤ τ + ε₁ + ε₂}. Each round peels one shell. The deep basin (f(x) ≫ τ) survives all rounds with total shift < f(x) − τ.

**Prediction:** Plot jailbreak success rate vs. number of safety fine-tuning rounds. The curve should be concave — steep initial drop, then flattening. The residual rate converges to the fraction of prompts with f(x) − τ exceeding the cumulative shift budget. Models with deeper basins (higher peak AD) require proportionally more rounds to reach the same residual rate.

**Test:** Compare Llama-3-8B (peak AD 0.93) and GPT-OSS-20B (peak AD 0.73) after 1, 2, 3 rounds of DPO. Llama should show slower convergence to safety.

---

## 2. Longer contexts make defense exponentially harder

**From:** Cost Asymmetry (Thm A.10, `MoF_Cost`):
Defense cost = N^d (exponential in dimension d). Attack cost ≤ 1/δ (dimension-independent).

**Derivation:** The effective dimension d of the prompt space scales with usable context length. A 128K-token context window has exponentially more degrees of freedom than a 4K window. The defense must cover N^d grid cells; the attacker searches a 1D path. The cost ratio δ · N^d grows exponentially with context length.

**Prediction:** Holding model capability constant, jailbreak success rate increases with context length. Specifically: if attacks succeed at rate p on context length L₁, they succeed at rate ≥ p on context length L₂ > L₁ (the defense cannot improve by expanding the input space). Long-context models are disproportionately vulnerable to prompt injection via context stuffing.

**Test:** Measure jailbreak success on the same model at context lengths 4K, 16K, 64K, 128K. Control for the attack prompt itself being fixed-length — vary only the amount of padding/distraction context.

---

## 3. Agentic tool-use systems degrade defense exponentially with depth

**From:** Pipeline Lipschitz Degradation (Thm 8.3, `MoF_15`):
n stages each K-Lipschitz → pipeline is K^n-Lipschitz. ε-band scales as L · K^n · δ.

**Derivation:** Each tool call in an agentic system (web search, code execution, API call) is a nonlinear transformation with Lipschitz constant K ≥ 1. A 5-tool pipeline has effective constant K^5. The ε-robust band — the region where the defense provably cannot push outputs far below threshold — widens by factor K^5 relative to a single-call system.

**Prediction:** Agentic systems with n sequential tool calls have jailbreak rates that grow with n, even if each individual stage is defended. The growth is at least polynomial and potentially exponential in the number of tool calls. Indirect prompt injection through tool outputs (e.g., injecting instructions via web search results) exploits this: each tool call amplifies the attacker's reach.

**Test:** Build an agent with 1, 2, 3, 5, 10 tool-call stages. Measure the fraction of adversarial inputs that produce unsafe final outputs at each depth. Expect monotone increase.

---

## 4. Temperature sampling must sometimes produce unsafe outputs at boundary prompts

**From:** Stochastic Defense Impossibility (Thm 8.2, `MoF_13`) + stochastic dichotomy remark:
If g(x) = E[f(D(x))] is continuous with g = f on safe inputs, then g(z) = τ at boundary points. Either f(D(z)) = τ a.s. (deterministic), or P(f(D(z)) > τ) > 0.

**Derivation:** Temperature sampling at generation time is a stochastic perturbation. Model it as a stochastic defense: D(x) samples from a distribution centered on the deterministic output. At boundary prompts (f(z) = τ), the expected alignment deviation is τ. If the sampling is genuinely stochastic (temperature > 0), the output is not deterministic, so by the dichotomy, P(f(D(z)) > τ) > 0.

**Prediction:** For any prompt near the safety boundary, there exists a temperature setting at which repeated sampling produces unsafe outputs with positive probability. Lower temperature reduces but does not eliminate this probability (unless temperature = 0, which is deterministic). Boundary prompts are identifiable as those with high variance in safety classification across samples.

**Test:** Identify boundary prompts (those that sometimes refuse and sometimes comply). Sample 1000 completions at temperatures 0.1, 0.3, 0.7, 1.0. Plot the fraction of unsafe completions vs. temperature. Expect: monotonically increasing, positive for all T > 0, converging to 0 only as T → 0.

---

## 5. Quantization preserves deep vulnerabilities, shifts shallow ones

**From:** Interior Stability (Thm A.7) + Crossing Preservation (Thm A.8, `MoF_Adv_03`):
‖f − g‖∞ ≤ ε and f(x) > τ + ε ⟹ g(x) > τ. If f crosses τ with margin > ε, g also crosses τ.

**Derivation:** Quantization (INT8, INT4, GPTQ, AWQ) introduces a perturbation g = f + noise with ‖f − g‖∞ ≤ ε_quant. INT8 has small ε_quant; INT4 has larger. Any vulnerability where f(x) > τ + ε_quant survives quantization. Boundary crossings with margin > ε_quant are preserved — the boundary shifts but doesn't disappear.

**Prediction:** 
- INT8 quantization preserves virtually all jailbreaks (ε_quant is small relative to typical AD values).
- INT4 quantization may eliminate shallow-margin jailbreaks but preserves deep-basin ones.
- No quantization level eliminates vulnerabilities with f(x) − τ exceeding ε_quant.
- The attack transfer rate from FP16 to quantized versions should be monotone in (peak AD − ε_quant).

**Test:** Take a model with known jailbreaks at various AD levels. Quantize to INT8, INT4, INT3. Measure which jailbreaks survive at each level. Expect survival rate to be a step function of original AD value.

---

## 6. Model merging preserves the deeper parent's vulnerabilities

**From:** Interior Stability applied to convex combinations:
If g = αf₁ + (1−α)f₂, then ‖g − f₁‖∞ ≤ (1−α)‖f₁ − f₂‖∞.

**Derivation:** Model merging (SLERP, TIES, DARE) produces an alignment surface that is approximately a convex combination of the parents. If model A has a deep vulnerability (f_A(x) ≫ τ) and model B is safe at x (f_B(x) < τ), the merged model has g(x) ≈ α·f_A(x) + (1−α)·f_B(x). For the vulnerability to survive: g(x) > τ, which holds when α·f_A(x) > τ − (1−α)·f_B(x). Deep basins in A survive unless the merge ratio α is very small.

**Prediction:** Merging a vulnerable model with a safe model does NOT reliably eliminate the vulnerable model's jailbreaks. The merge ratio α must satisfy α < (τ − f_B(x)) / (f_A(x) − f_B(x)) to eliminate a specific vulnerability — which approaches 0 for deep basins. Merging at 50/50 preserves all vulnerabilities where f_A(x) > 2τ − f_B(x).

**Test:** Merge Llama-3-8B (highly vulnerable) with a safety-tuned variant at ratios 0.7/0.3, 0.5/0.5, 0.3/0.7. Test known jailbreaks at each ratio. Expect: high-AD jailbreaks survive even at 0.3/0.7.

---

## 7. Adversarial training fragments vulnerabilities but may not reduce total vulnerable volume

**From:** Basin Fragment Size (Thm A.2, `MoF_04`):
Connected component diameter ≥ 2(f(p) − τ)/L. Smoother surfaces → larger basins; rougher → smaller fragments.

**Derivation:** Adversarial training makes the alignment surface rougher (higher local Lipschitz constant L) around previously-discovered vulnerabilities. The fragment size bound 2(f(p)−τ)/L shows that increasing L shrinks individual basins. But rougher surfaces can have MORE fragments (the vulnerability splits rather than disappears). Total vulnerable volume μ(U_τ) is not constrained to decrease — only the maximum fragment size decreases.

**Prediction:** After adversarial training:
- Individual jailbreak "families" become smaller (harder to find by local search).
- The NUMBER of distinct jailbreak families increases.
- Total jailbreak success rate (with sufficient search budget) does not decrease proportionally to the per-family size reduction.
- This is the "whack-a-mole" phenomenon: patching known jailbreaks creates new, smaller ones.

**Test:** Red-team a model before and after adversarial training. Measure: (a) success rate of known attacks (should decrease), (b) number of distinct attack clusters found by diverse search (should increase), (c) total success rate with 10× search budget (should decrease less than (a) suggests).

---

## 8. Defense-in-depth for wrapper defenses is counterproductive past a threshold

**From:** Pipeline Impossibility (Thm 8.4, `MoF_15`):
Composed pipeline P = D_n ∘ ... ∘ D_1 with each D_i being K_i-Lipschitz has effective constant ∏K_i. The ε-band scales as L · (∏K_i) · δ.

**Derivation:** Each wrapper defense layer D_i has Lipschitz constant K_i ≥ 1 (non-contractive — it must preserve safe inputs, so it can't shrink everything). Composing n wrappers gives effective K = ∏K_i ≥ 1. The ε-robust band width L·K·δ GROWS with each additional layer. The boundary fixed point still exists (pipeline impossibility), and the region where the defense provably cannot push below τ gets WIDER.

**Prediction:** Stacking multiple input-sanitization layers (e.g., perplexity filter → constitutional rewriter → intent classifier) eventually makes the defense WORSE, not better. There exists an optimal number of layers n* beyond which additional layers increase the failure band. The optimal n* decreases with the per-layer Lipschitz constant.

**Test:** Build a defense pipeline with 1, 2, 3, 5 wrapper layers. Measure the ε-band width (fraction of prompts where the defense output is within ε of threshold). Expect non-monotone: initially decreasing (defense helps), then increasing (Lipschitz amplification dominates).

---

## 9. Jailbreak transferability is asymmetric: deep → shallow, not reverse

**From:** Transferability (Thm A.5, `MoF_06`):
‖f − g‖∞ ≤ δ ⟹ {f > τ + δ} ⊆ {g > τ}.

**Derivation:** Let f be the alignment surface of model A (deeply vulnerable, high AD) and g be model B (less vulnerable, lower AD). If ‖f−g‖∞ ≤ δ, then every point where f(x) > τ + δ also has g(x) > τ. Model A's deep-basin jailbreaks (high f(x)) transfer to B. But B's shallow-basin jailbreaks (g(x) barely above τ) satisfy g(x) < τ + δ, which does NOT guarantee f(x) > τ. Transfer is one-directional: from the model with deeper basins to the model with shallower basins.

**Prediction:** Jailbreaks discovered on more vulnerable models transfer to less vulnerable models at higher rates than the reverse. The transfer rate from A→B is approximately μ({f > τ + δ}) / μ({f > τ}), which is higher when A has deep basins. The paper already observes this (Llama .93 → GPT-OSS .73 → Mini .47), but the asymmetry prediction is sharper: the transfer matrix should be approximately upper-triangular when models are sorted by mean AD.

**Test:** Build a 5×5 transfer matrix across models of varying vulnerability. Sort by mean AD. The matrix should be approximately upper-triangular: high transfer rates above the diagonal, low rates below.

---

## 10. The "alignment tax" on expressiveness is proportional to unsafe volume

**From:** Discrete Defense Dilemma (Thm 7.4, `MoF_12`):
A complete utility-preserving defense must be non-injective: ∃ x ≠ y with D(x) = D(y).

**Derivation:** For every unsafe input u, the defense maps D(u) to some safe input s. Since D(s) = s (utility preservation) and D(u) = s with u ≠ s, the defense collapses the pair {u, s} to {s}. The downstream model cannot distinguish u from s. Information is lost. The total information loss ≥ log₂(|U_τ|) bits — one bit per unsafe input that must be collapsed into a safe equivalent.

**Prediction:** Models with larger unsafe regions (higher basin rate) suffer greater expressiveness loss under complete wrapper defense. This manifests as:
- Higher perplexity on benign tasks after defense is applied.
- Reduced performance on tasks that require inputs near the safety boundary (e.g., medical advice, security research, historical violence discussion).
- The performance gap between defended and undefended models is proportional to μ(U_τ) / μ(X), the fraction of the input space that is unsafe.

**Test:** Apply a complete input-sanitization defense to models with varying basin rates. Measure benign-task performance (MMLU, HumanEval, etc.) before and after. Plot the performance drop vs. basin rate. Expect positive correlation.

---

## Summary Table

| # | Prediction | Supporting Theorem | Testable? |
|---|---|---|---|
| 1 | Safety fine-tuning has diminishing returns | Interior Stability | Yes — multi-round DPO comparison |
| 2 | Longer contexts → exponentially harder defense | Cost Asymmetry | Yes — context-length sweep |
| 3 | Agentic tool-use degrades defense exponentially | Pipeline Lipschitz | Yes — tool-call depth sweep |
| 4 | Temperature sampling produces unsafe outputs at boundary | Stochastic Impossibility | Yes — multi-sample at boundary prompts |
| 5 | Quantization preserves deep vulnerabilities | Interior Stability | Yes — quantization level sweep |
| 6 | Model merging preserves deeper parent's vulnerabilities | Interior Stability (convex) | Yes — merge ratio sweep |
| 7 | Adversarial training fragments but doesn't eliminate volume | Fragment Size | Yes — before/after cluster analysis |
| 8 | Wrapper defense-in-depth is counterproductive past threshold | Pipeline Impossibility | Yes — layer count sweep |
| 9 | Jailbreak transfer is asymmetric (deep → shallow) | Transferability | Yes — transfer matrix |
| 10 | Alignment tax proportional to unsafe volume | Discrete Dilemma | Yes — performance vs. basin rate |

All predictions are falsifiable. None require new theorems — they are instantiations of existing results to specific LLM engineering scenarios.
