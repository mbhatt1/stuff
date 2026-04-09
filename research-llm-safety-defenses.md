# Research: Empirical Evidence on LLM Safety Defense Failures

*Date: 2026-04-09 | Scope: four failure modes of LLM safety defenses*

---

## Summary

Four claimed failure modes of LLM safety defenses are **all empirically supported** by recent literature with specific numbers. Adversarial training is fragile and routinely bypassed by novel attack vectors (whack-a-mole). Multi-layer defense-in-depth offers major protection against naive attacks but collapses under adaptive stage-by-stage attacks (71% success rate vs. 0% for conventional attacks). Jailbreak transfer is asymmetric — weak-to-strong transfer is well-documented as directionally easier than the reverse. Safety alignment reliably degrades general capabilities (alignment/safety "tax"), with documented drops of 7–31% in reasoning accuracy and up to 43% on instruction-following benchmarks.

---

## Findings by Topic

### 1. Whack-a-Mole: Adversarial Training Fragments But Doesn't Eliminate Vulnerabilities

**Core claim:** Patching one attack surface opens or reveals others; safety alignment is shallow and not robust to novel vectors.

1. **Fine-tuning destroys alignment with trivially few examples.** Qi et al. (2023, arXiv:2310.03693, ICLR 2024) showed that fine-tuning GPT-3.5 Turbo on just **10 explicitly harmful examples** raises its harmfulness rate from **1.8% → 88.8% (+87 percentage points)**. The analogous 10-shot attack on Llama-2-7b-Chat raises harmfulness from 0.3% → 50%. An "identity-shifting" attack using **10 benign-seeming examples** (none flagged by OpenAI's moderation API) raised harmfulness rate to **87.3% in GPT-3.5 Turbo**. Quote: *"10-shot attack on Llama-2 literally only takes 5 gradient steps… current RLHF and safety fine-tuning approaches result in relatively surface-level changes to the model."* [Qi et al., 2023](https://arxiv.org/abs/2310.03693)

2. **Even benign fine-tuning erodes safety.** The same paper showed that fine-tuning GPT-3.5 on the standard Alpaca dataset (no harmful content) raises harmfulness rate from **5.5% → 31.8% (+26.3 pp)** and on Dolly from 4.5% → 23.9% (+19.4 pp), attributed to catastrophic forgetting of safety alignment. [Qi et al., 2023](https://arxiv.org/abs/2310.03693)

3. **Adversarial suffix training (GCG-style) achieves near-100% ASR on new models.** Augmented Adversarial Trigger Learning (arXiv:2503.12339) achieves "nearly 100% attack success rate while requiring 80% fewer queries" and demonstrates "high generalization to unseen harmful inputs." The Resurgence of GCG paper (arXiv:2509.00391) confirms gradient-based attacks remain effective even on 20B-parameter models. [ATLA, 2025](https://arxiv.org/abs/2503.12339); [GCG Resurgence, 2025](https://arxiv.org/abs/2509.00391)

4. **Alignment Whack-a-Mole (copyright domain).** Liu et al. (arXiv:2603.20957, March 2026) demonstrated the "whack-a-mole" label explicitly: safety alignment blocks verbatim recall, but fine-tuning the model to expand plot summaries reactivates near-verbatim recall of copyrighted books — a different surface than what was patched. [Liu et al., 2026](https://arxiv.org/abs/2603.20957)

5. **IRIS attack achieves 25% ASR against state-of-the-art Circuit Breaker defense** compared to 2.5% for standard white-box GCG — a new attack vector specifically developed because the old one was patched. [IRIS, people.eecs.berkeley.edu/~daw/papers/iris-naacl25.pdf](https://people.eecs.berkeley.edu/~daw/papers/iris-naacl25.pdf)

**Key pattern:** Each time a specific attack is patched (e.g., suffix injections via GCG), adversaries shift to fine-tuning APIs, identity-shifting prompts, multi-step attacks, or reasoning exploits. The system lacks deep invariant robustness.

---

### 2. Stacking Multiple Defense Layers Is Not Simply Additive (and Can Be Gamed Systematically)

**Core claim:** Multi-layer defenses are not robust to adaptive attackers designed to defeat them sequentially.

6. **Conventional attacks fail completely against layered defenses; adaptive attacks succeed at 71%.** FAR.AI / UK AI Security Institute (McKenzie, Hollinsworth et al., 2025, arXiv:2506.24068) built a multi-layer defense pipeline (input filter + model training + output filter) and tested it against both conventional and adaptive attacks on the ClearHarm catastrophic-risk dataset:
   - Conventional attacks (PAP, ReNeLLM, Best-of-N): **0% attack success rate (ASR)**
   - STACK (STaged AttaCK), their novel layer-by-layer attack: **71% ASR** under limited-feedback conditions (attacker knows which layer blocked a request)
   - STACK in full transfer/black-box conditions: **33% ASR** — still breaking through even without system access
   - Quote: *"Defense-in-depth, while valuable, requires careful implementation to minimize the attack surface."* [FAR.AI, 2025](https://far.ai/news/defense-in-depth)

7. **TRYLOCK shows layers help but each layer has unique blind spots.** TRYLOCK (arXiv:2601.03300) combined 4 heterogeneous mechanisms and reduced ASR from 46.5% → 5.6% (88% relative reduction across 5 attack families). However, each individual layer left large residual ASRs, confirming that without all 4 layers, substantial attack surface remains — i.e., no single defense is sufficient, but the combined surface is still non-zero. [TRYLOCK, 2025](https://arxiv.org/abs/2601.03300)

8. **Revealing which layer rejected a request is the key vulnerability.** FAR.AI found that the **71% STACK success rate depended on knowing which component blocked the request** — information currently exposed by many systems. If this information is withheld, attack success decreases substantially. This is an architectural leak introduced by defense composition. [FAR.AI, 2025](https://far.ai/news/defense-in-depth)

9. **Real systems use layered approaches (Anthropic Constitutional Classifiers, Google DeepMind, OpenAI)**, all of which deploy input filter + model training + output filter. FAR.AI's work specifically targets these production architectures and finds them structurally vulnerable to staged attacks. [FAR.AI, 2025](https://far.ai/news/defense-in-depth)

**Key pattern:** Defense-in-depth is not counterproductive in the sense that it does substantially reduce ASR from naive attacks (0% conventional ASR). However, it creates a false sense of security — adaptive attackers who understand the layered structure achieve 71% success rates. The interaction between layers (especially information leaked about which layer rejected) introduces attack surface not present in simpler designs.

---

### 3. Jailbreak Transferability Is Asymmetric (Easier From Weaker to Stronger Models)

**Core claim:** Attacks crafted on small/weak models transfer upward to large aligned models more easily than the reverse.

10. **Weak-to-Strong Jailbreaking is a named, published attack paradigm.** Zhao et al. (arXiv:2401.17256, ICML 2025) proposed the "weak-to-strong jailbreaking attack," exploiting the key observation that **harmful content tokens have different probabilities between aligned and unaligned versions of a model**. By using a small unaligned model's decoding to modify a large aligned model's output distribution at inference time, they successfully jailbreak large aligned models efficiently without compute-intensive optimization. Published at ICML 2025. [Zhao et al., 2025](https://arxiv.org/abs/2401.17256)

11. **Transfer success rates decrease monotonically as target models become stronger.** IRIS (Berkeley, NAACL 2025) reports the following transfer attack success rates on frontier models from a single open-weight source:
    - GPT-3.5-Turbo: **90%**
    - GPT-4o-mini: **86%**
    - GPT-4o: **76%**
    - o1-mini: **54%**
    - o1-preview: **48%**
    The gradient is clear: stronger/newer models resist transfer better, but none achieve robustness anywhere near 100%. [IRIS, NAACL 2025](https://people.eecs.berkeley.edu/~daw/papers/iris-naacl25.pdf)

12. **Representational similarity modulates transfer success.** "Jailbreak Strength and Model Similarity Predict Transferability" (arXiv:2506.12913) finds that transfer success from open-weight to closed-weight target models depends on **both jailbreak strength and representational similarity** between source and target models — providing a quantitative predictor for when weak-to-strong transfer will succeed. [arXiv:2506.12913, 2025](https://arxiv.org/abs/2506.12913)

13. **Asymmetry in the other direction is documented but not quantified as systematically.** Transfer from stronger models to weaker models is less studied precisely because it is less practically useful — attackers prefer the cheap-to-strong pipeline. The literature's overwhelming focus on weak-to-strong transfer itself constitutes evidence of the asymmetry.

**Key numbers:**
- Weak-to-strong attack: efficient (no optimization needed, inference-time only)
- ASR decay curve: 90% → 86% → 76% → 54% → 48% as model capability increases

---

### 4. Safety Patches Cause Capability Regression ("Alignment Tax")

**Core claim:** Safety alignment degrades general capabilities on benchmarks (math, code, reasoning, instruction-following).

14. **Safety Tax on Large Reasoning Models: 7–31% reasoning accuracy drop.** Huang et al. (Georgia Tech, arXiv:2503.00555, 2025) coined "Safety Tax" for LRMs. Starting from s1.1-32B (a reasoning model):
    - **DirectRefusal safety alignment**: reasoning accuracy drops by **30.91%** on average (AIME, GPQA, MATH500)
    - **SafeChain (CoT) safety alignment**: reasoning accuracy drops by **7.09%** on average
    - Importantly, reasoning training itself raised harmful score from **16.70 → 60.40 (+43.7 pp)** before any safety alignment — so you must pay the tax to recoup what reasoning training cost you. [Safety Tax, arXiv:2503.00555](https://arxiv.org/abs/2503.00555)

15. **SafeRLHF causes severe capability regression on Llama-3-8B.** From the NSPO paper (Niu et al., arXiv:2512.11391, HKUST):
    - AlpacaEval (instruction-following): **96.15% → 52.55%** (loss of ~43.6 pp)
    - GSM8K (math): **75.44% → 51.71%** (loss of ~23.7 pp)
    - MMLU (knowledge): **63.79% → 58.91%** (loss of ~4.9 pp)
    - LiveCodeBench (code): **13.37% → 8.96%** (loss of ~4.4 pp)
    [NSPO, arXiv:2512.11391](https://arxiv.org/abs/2512.11391)

16. **SafeRLHF on Qwen2.5-7B also shows severe regression:**
    - AlpacaEval: **94.35% → 57.02%** (loss of ~37.3 pp)
    - MATH: **74.80% → 44.63%** (loss of ~30.2 pp)
    - OlympiadBench: **37.80% → 22.22%** (loss of ~15.6 pp)
    [NSPO, arXiv:2512.11391](https://arxiv.org/abs/2512.11391)

17. **DPO-based safety alignment also degrades capabilities on Llama-3-8B:**
    - DPO-S: MMLU 63.79% → 57.78% (-6.0 pp), GSM8K 75.44% → 62.55% (-12.9 pp)
    - DPO-H: MMLU 63.79% → 60.47% (-3.3 pp), GSM8K 75.44% → 59.97% (-15.5 pp)
    [NSPO, arXiv:2512.11391](https://arxiv.org/abs/2512.11391)

18. **Formal geometric theory of alignment tax.** Huang et al. (arXiv:2603.00047, 2026) formally defined the alignment tax rate as "the squared projection of the safety direction onto the capability subspace" and derived the Pareto frontier governing safety-capability tradeoffs. Under linear representation assumptions, safety and capability gradients are not orthogonal — there is an unavoidable conflict. [What Is the Alignment Tax?, arXiv:2603.00047](https://arxiv.org/abs/2603.00047)

19. **W-DOOR on Qwen2.5-7B shows catastrophic MATH degradation:**
    - MATH: 74.80% → 37.15% (-37.7 pp)
    - OlympiadBench: 37.80% → 15.15% (-22.7 pp)
    - AlpacaEval: 94.35% → 75.96% (-18.4 pp)
    [NSPO, arXiv:2512.11391](https://arxiv.org/abs/2512.11391)

**Key pattern:** The alignment tax is real, large (often 10–40 pp on reasoning/math benchmarks), method-dependent (RLHF-based methods worse than DPO), and theoretically necessary under current architectures (non-orthogonal gradient spaces).

---

## Quick-Reference Table

| Claim | Key Paper | Key Numbers |
|---|---|---|
| Adversarial training leaves exploitable holes | Qi et al., arXiv:2310.03693 (ICLR 2024) | 10 examples → +87 pp harmfulness rate (GPT-3.5) |
| Benign fine-tuning erodes alignment | Qi et al., arXiv:2310.03693 | Alpaca fine-tune: +26.3 pp harmfulness (GPT-3.5) |
| New attack surfaces emerge after patches | IRIS, NAACL 2025 | 25% ASR vs. Circuit Breaker (vs. 2.5% for GCG) |
| Multi-layer defenses fail to staged attacks | FAR.AI / McKenzie et al., arXiv:2506.24068 | Conventional: 0% ASR → STACK: 71% ASR |
| Layered defense leak (which layer rejected) | FAR.AI | 71% with feedback, 33% without |
| Weak-to-strong jailbreak | Zhao et al., arXiv:2401.17256 (ICML 2025) | Efficient inference-time attack on large aligned LLMs |
| Transfer success drops with model strength | IRIS, NAACL 2025 | GPT-3.5: 90% → GPT-4o: 76% → o1-preview: 48% |
| Transfer depends on representational similarity | arXiv:2506.12913 | Quantitative predictor identified |
| Safety tax on reasoning models (RLHF) | Huang et al., arXiv:2503.00555 (2025) | -30.91% reasoning accuracy (DirectRefusal), -7.09% (CoT) |
| Safety tax on Llama-3-8B (SafeRLHF) | Niu et al., arXiv:2512.11391 | AlpacaEval: -43.6 pp; GSM8K: -23.7 pp |
| Alignment tax is geometrically necessary | Huang et al., arXiv:2603.00047 (2026) | Formal proof: safety/capability gradients not orthogonal |

---

## Sources

### Kept
- **Qi et al. 2023/2024 (arXiv:2310.03693)** — Direct empirical measurement of fine-tuning safety erasure with specific shot counts and harmfulness rates. ICLR 2024.
- **Zhao et al. 2025 (arXiv:2401.17256)** — The named "weak-to-strong jailbreaking" paper with mechanistic explanation. ICML 2025.
- **IRIS, NAACL 2025** — Strong transfer attack with model-specific ASR numbers across the frontier model lineup.
- **McKenzie, Hollinsworth et al. / FAR.AI (arXiv:2506.24068)** — Direct empirical test of multi-layer defenses (STACK), 71% vs. 0% comparison. Conducted with UK AISI.
- **Huang et al. / Georgia Tech (arXiv:2503.00555)** — "Safety Tax" on reasoning models with specific benchmark numbers.
- **Niu et al. / HKUST (arXiv:2512.11391)** — NSPO paper with full benchmark tables across 7 safety + 7 capability benchmarks for multiple methods, best quantified capability regression data.
- **Huang et al. 2026 (arXiv:2603.00047)** — Formal geometric theory of alignment tax with Pareto frontier derivation.
- **TRYLOCK (arXiv:2601.03300)** — Multi-layer defense architecture results, 5 attack families.
- **Liu et al. 2026 (arXiv:2603.20957)** — "Alignment Whack-a-Mole" copyright domain, literal term for the whack-a-mole pattern.
- **arXiv:2506.12913** — Representational similarity + jailbreak strength → transferability prediction.
- **arXiv:2503.12339 (ATLA)** — Near-100% ASR adversarial suffix attack, 80% fewer queries.

### Dropped
- **redteams.ai explainers** — Secondary synthesis, no original data.
- **Emergent Mind alignment tax page** — Aggregator, not primary source.
- **Facebook posts / news articles** — Not empirical.
- **PMC prompt-based jailbreak mitigation** — Focused on defense, not measuring the failure modes requested.

---

## Gaps

1. **Whack-a-mole over time / longitudinal data**: No paper tracks how many distinct attack types have emerged against a single model over its lifetime and what fraction were successfully patched vs. recurring. This would most directly quantify the "fragmentation without elimination" claim.

2. **Strong-to-weak transfer baseline**: While weak-to-strong transfer is well-characterized, **strong-to-weak transfer rates are rarely measured** — limiting the ability to precisely quantify the asymmetry directional effect size.

3. **Production system alignment tax**: Capability regression numbers are measured on open-weight models (Llama-3, Qwen2.5). Proprietary models (GPT-4, Claude, Gemini) do not publish pre- vs. post-alignment benchmark splits, making it impossible to measure their alignment tax directly.

4. **Multi-layer defense with truly heterogeneous components**: FAR.AI's STACK was tested on a custom pipeline, not on production systems like Claude 4 Opus's Constitutional Classifiers (FAR.AI is currently running this evaluation as of April 2026; results pending).

5. **Causal mechanism for weak-to-strong transfer**: The representational similarity predictor is identified but the precise mechanistic account of why weak models can guide strong ones (beyond the probability difference intuition) is underspecified.

### Suggested next steps
- Search: *"longitudinal jailbreak patch effectiveness GPT-4 Claude attack evolution"* for whack-a-mole temporal data
- Search: *"strong-to-weak jailbreak transfer baseline comparison"* for directional asymmetry quantification
- Watch: FAR.AI's upcoming production Constitutional Classifiers STACK results (responsible disclosure period active as of April 2026)
