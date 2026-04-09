# Research: LLM Safety Vulnerabilities — Temperature Sampling, Quantization, and Model Merging

*Compiled: 2026-04-09 | All three topics covered with empirical numbers and paper citations.*

---

## Summary

Empirical evidence firmly establishes three distinct attack surfaces in deployed LLMs: (1) temperature sampling above T=0 destabilises safety refusals on borderline prompts, with 18–28% of harmful prompts flipping between refusal and compliance across configurations; (2) standard post-training quantization has mixed and method-dependent safety effects — aggressive 2-bit quantization broadly degrades safety, while 4/8-bit effects are model-and-method-specific — and adversarial quantization attacks (GGUF exploitation, fault injection) can achieve >80% attack success rates; (3) merging an aligned model with even one misaligned model propagates unsafe behaviour across all standard merging algorithms, and adversarially crafted TrojanMerge attacks raise harmful response rates from ~2% baseline to 71.9–85.4%.

---

## Findings

### Topic 1 — Temperature Sampling and Unsafe Outputs at Boundary Prompts

1. **18–28% of harmful prompts exhibit safety decision flips under different sampling configurations.** Larsen et al. (2025) tested four instruction-tuned models (Llama 3.1 8B, Qwen 2.5 7B, Qwen 3 8B, Gemma 3 12B) on 876 harmful prompts across 20 sampling configurations (4 temperatures × 5 seeds). Depending on the model, 18–28% of prompts that were refused in some configurations were complied with in others. [The Instability of Safety, arXiv:2512.12066](https://arxiv.org/abs/2512.12066)

2. **Higher temperature significantly reduces safety stability (Friedman χ²=396.81, p<0.001), with mean Safety Stability Index (SSI) dropping from 0.977 at T=0.0 to 0.942 at T=1.0.** The SSI measures within-configuration consistency; the drop is statistically significant across all model families. Single-shot evaluation agrees with multi-sample ground truth in only 92.4% of cases pooled across temperatures (94.2–97.7% at a fixed temperature setting). [ibid.]

3. **Borderline prompts — those with higher base compliance rates — exhibit disproportionately lower stability (Spearman ρ = −0.47 to −0.70, all p<0.001).** Models "waver" most precisely on the ambiguous prompts where safety decisions matter most. This means temperature amplifies risk specifically for prompts that are already at the decision boundary. [ibid.]

4. **Repeated sampling dramatically surfaces latent failure modes that single-shot evaluation misses.** The Accelerated Prompt Stress Testing (APST) framework (Liu et al., 2026) demonstrates that models with identical benchmark-aligned safety scores can exhibit substantially different empirical failure rates under repeated sampling, particularly as temperature increases. This suggests that pass/fail safety ratings from single-shot evals are unreliable. [Evaluating LLM Safety Under Repeated Inference via APST, arXiv:2602.11786](https://arxiv.org/abs/2602.11786)

5. **A statistical framework — "time-to-unsafe-sampling" — now exists for quantifying this risk formally.** Davidov et al. (ICLR 2026) model how long it takes for repeated sampling under controlled temperatures to surface a harmful output, providing calibrated lower bounds via survival analysis and conformal prediction. [Calibrated Predictive Lower Bounds on Time-to-Unsafe-Sampling in LLMs, ICLR 2026](https://openreview.net/forum?id=qDW1vtMIDr)

---

### Topic 2 — Quantization Preserving (or Amplifying) Jailbreaks

6. **2-bit quantization significantly increases jailbreak vulnerability across all tested Llama models; 4-bit and 8-bit have variable, method-dependent effects.** Kumar et al. (Enkrypt AI, 2024) evaluated quantized Llama models (2-bit, 4-bit, 8-bit) using the Tree-of-Attacks-with-Pruning (TAP) algorithm on 50 AdvBench harmful prompts. 2-bit aggressively degrades safety, while 4-bit and 8-bit models "in some cases offer improved protection compared to the original" — suggesting safety alignment is not destroyed but is redistributed by moderate quantization. [Fine-Tuning, Quantization, and LLMs: Navigating Unintended Outcomes, arXiv:2404.04392](https://arxiv.org/abs/2404.04392)

7. **On the OpenSafetyMini benchmark, QUIP# int4 Mistral drops 11.48 percentage points in safety vs FP16; Mistral QUIP# int2 drops 15.57 points.** Kharinaev et al. (Skoltech, 2025) ran 24 evaluation settings across LLaMA 3.1 8B and Mistral 7B v0.2 using AWQ, QUIK, AQLM, QUIP# at 4-bit and 2-bit, with human evaluations and LLM-as-a-judge (92% human agreement):
   - LLaMA FP16 safety ratio: **93.06%** (OpenSafetyMini)
   - LLaMA AWQ int4: **89.50%** (−3.94pp)
   - LLaMA QUIP# int4: **84.44%** (−8.62pp)
   - LLaMA QUIP# int2: **84.25%** (−9.61pp)
   - LLaMA abliterated (refusal-direction removed): **63.26%** (−24.08pp, the "least safe" reference)
   - Mistral FP16: **84.82%**
   - Mistral AWQ int4: **83.13%** (−1.69pp)
   - Mistral QUIK int4: **76.38%** (−8.44pp)
   - Mistral QUIP# int2: **70.10%** (−14.72pp)
   - Key finding: QUIK preserves LLaMA safety well but degrades Mistral; AWQ is safest for Mistral — **quantization safety effects are strongly model-architecture-specific.**
   [Investigating the Impact of Quantization on LLM Safety, arXiv:2502.15799](https://arxiv.org/abs/2502.15799)

8. **An adversarial GGUF quantization attack (ICML 2025) achieves Δ=85.0% content injection by exploiting quantization error as an attack vector.** Egashira et al. (ETH Zurich SRI Lab, 2025) demonstrate that the quantization error — the numerical gap between a full-precision weight and its GGUF-quantized counterpart — can be weaponised. Attackers plant malicious behaviours in the full-precision model that are hidden until quantization, or vice versa: models appear benign in full precision but activate malicious behaviours post-quantization. This is the first published attack specifically targeting GGUF (used by llama.cpp and Ollama), with content injection ASR of Δ=85.0% and benign-instruction-refusal also achieved. [Mind the Gap: A Practical Attack on GGUF Quantization, ICML 2025](https://www.sri.inf.ethz.ch/publications/egashira2025mind)

9. **Fault injection (bit-flip) attacks show quantization precision interacts sharply with jailbreak ASR.** Evaluated across Llama-3.2-3B, Phi-4-mini, and Llama-3-8B: FP16 baseline achieves >80% ASR within 25 bit-flip perturbations; FP8 drops to <20% ASR and INT8 to <50% ASR within the same budget. At 150 bit-flips, FP8 maintains ASR below 65%. The observation that lower precision (quantized) models are *harder* to jailbreak via fault injection reflects quantization's compression of the weight space — but this is attack-method-specific; standard jailbreaks are preserved or slightly modified, not blocked. [On Jailbreaking Quantized LLMs Through Fault Injection Attacks, arXiv:2507.03236](https://arxiv.org/abs/2507.03236)

---

### Topic 3 — Model Merging Preserving Vulnerabilities from the More Vulnerable Parent

10. **"One bad model spoils the bunch" — merging a misaligned model with aligned models propagates misalignment, even across majority-aligned merges.** Hammoud et al. (EMNLP 2024 Findings) systematically evaluate TIES, DARE, SLERP, and weighted-averaging merging. They find that existing merging methods treat safety alignment as just another "skill" vector that gets diluted and overridden rather than preserved when a misaligned source is present. Their proposed fix requires explicitly injecting synthetic safety data into the merging optimisation to treat alignment as a protected property. [Model Merging and Safety Alignment: One Bad Model Spoils the Bunch, arXiv:2406.14563](https://arxiv.org/abs/2406.14563)

11. **Standard merging of clean models yields 1.9–24.0% harmful response rates (AdvBench); adversarially crafted TrojanMerge raises this to 71.9–85.4% while individual source models look safe.** Yuan et al. (HUST, 2025) present TrojanMerge, tested on 9 LLMs from Llama 2, Llama 3, and Mistral families across four merging algorithms (Task Arithmetic, DARE, TIES-Merging, KnOTS):

   | Configuration | Llama 2 HS% | Llama 3 HS% | Mistral HS% |
   |---|---|---|---|
   | M1 (clean source) | 3.1 | 1.0 | 25.0 |
   | M2 (clean source) | 8.1 | 1.9 | 21.9 |
   | M1+M2 (clean merge) | 1.9 | 3.1 | 24.0 |
   | M1′ (trojanised) | 26.3 | 23.3 | 23.1 |
   | M2′ (trojanised) | 29.0 | 3.1 | 26.2 |
   | **M1′+M2′ (merged trojan)** | **71.9** | **81.0** | **85.4** |

   Average HS across merging algorithms: Task Arithmetic 79.4%, DARE 77.1%, TIES 79.1%, KnOTS 73.6%. Critically, individual trojanised models pass individual safety checks because the attack only manifests post-merge. [When Safe Models Merge into Danger: Exploiting Latent Vulnerabilities in LLM Fusion, arXiv:2604.00627](https://arxiv.org/abs/2604.00627)

12. **TIES-Merging's Top-K magnitude pruning does not mitigate latent attack propagation.** Increasing Top-K from 10 to 50 actually increases attack HS (Llama 3: 56.0% → 88.1%), as larger magnitude attack components survive the trim step. DARE shows moderate sensitivity (Llama 3 collapses at high pruning rate p=0.8, but Mistral maintains >63.1% HS across all DARE pruning rates). [ibid.]

13. **Merge Hijacking (arXiv:2505.23561, May 2025) confirms that backdoor vectors injected into source LLMs via weight-space manipulation propagate reliably through merging and activate via lexical triggers in the merged model.** This is a complementary attack requiring triggers but not requiring latent optimization; both approaches demonstrate the same fundamental conclusion that merge operations do not sanitise adversarial weight perturbations.

---

## Sources

| Source | Status | Reason |
|---|---|---|
| [arXiv:2512.12066 — Instability of Safety](https://arxiv.org/abs/2512.12066) | **Kept** | Primary empirical study on temperature/seed instability with specific numbers |
| [arXiv:2602.11786 — APST](https://arxiv.org/abs/2602.11786) | **Kept** | Repeated-inference safety testing framework, complements instability findings |
| [ICLR 2026 — Time-to-Unsafe-Sampling](https://openreview.net/forum?id=qDW1vtMIDr) | **Kept** | Formal statistical framework for quantifying temperature risk |
| [arXiv:2404.04392 — Enkrypt AI Quantization](https://arxiv.org/abs/2404.04392) | **Kept** | Direct empirical study with ASR tables for quantized Llama/Mistral/Qwen |
| [arXiv:2502.15799 — Skoltech Quantization Safety](https://arxiv.org/abs/2502.15799) | **Kept** | Most rigorous quantization safety study (24 settings, human evals, LLaMA+Mistral) |
| [ICML 2025 — Mind the Gap / GGUF Attack](https://www.sri.inf.ethz.ch/publications/egashira2025mind) | **Kept** | First adversarial GGUF attack with Δ=85.0% injection rate |
| [arXiv:2507.03236 — Fault Injection Jailbreak](https://arxiv.org/abs/2507.03236) | **Kept** | ASR data across FP16/FP8/INT8/INT4 with specific percentages |
| [arXiv:2406.14563 — One Bad Model Spoils the Bunch](https://arxiv.org/abs/2406.14563) | **Kept** | Canonical paper on safety alignment degradation in standard model merging |
| [arXiv:2604.00627 — TrojanMerge](https://arxiv.org/abs/2604.00627) | **Kept** | Full attack framework with HS% tables for 9 LLMs × 4 merging algorithms |
| [arXiv:2505.23561 — Merge Hijacking](https://arxiv.org/abs/2505.23561) | **Kept** | Corroborating backdoor propagation through merging |
| [redteams.ai model merging article](https://redteams.ai/topics/training-pipeline/model-merge-safety-implications) | **Dropped** | Editorial/framework article, no original empirical data |
| [ACL Anthology EMNLP 2024 findings-emnlp.762 PDF](https://aclanthology.org/2024.findings-emnlp.762.pdf) | Attempted fetch failed | Full paper available via arXiv:2406.14563 |

---

## Gaps

### What remains incompletely answered:

1. **Non-adversarial merging with a genuinely weaker (not deliberately poisoned) parent**: The TrojanMerge paper shows adversarial scenarios; the Hammoud et al. paper shows the principle but does not publish quantitative HS% tables for specific merge ratios between aligned and naturally misaligned models. The exact "inheritance ratio" — how much of the weaker model's vulnerability bleeds into the merged model as a function of its weight coefficient — is not pinned down with precise numbers for standard SLERP/DARE/TIES.

2. **SLERP specifically**: Most empirical work focuses on Task Arithmetic, DARE, and TIES. SLERP (used heavily in the open-source merging community via MergeKit) lacks dedicated safety-impact numbers in the literature reviewed; it is mentioned in Hammoud et al. but specific HS% rates for SLERP merging are not in any paper found.

3. **Standard jailbreak preservation through quantization (not adversarial)**: The Enkrypt AI paper uses TAP on AdvBench and finds 2-bit degrades alignment broadly, but does not report which *specific jailbreak types* survive 4-bit vs 8-bit. Whether structured attacks like DAN, many-shot jailbreaks, or suffix attacks are differentially preserved vs. destroyed at each quantization level is not characterised in the papers found.

4. **Interaction effects**: No paper examines the combination of all three (merging + quantizing + high-temperature sampling together), which is the realistic deployment scenario.

### Suggested next steps:
- Search for `SLERP model merging safety empirical jailbreak rate` specifically
- Check the Hammoud et al. EMNLP 2024 full paper PDF for any SLERP-specific tables
- Search for `DAN jailbreak quantization preservation INT4` for type-specific jailbreak survival studies
- Look for HarmBench results across quantized model variants (HarmBench provides a standardised ASR leaderboard that may have quantized entries)
