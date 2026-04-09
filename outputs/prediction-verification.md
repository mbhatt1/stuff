# Prediction Verification: Defense Trilemma vs. Empirical Literature

Each of 14 predictions derived from the Lean-verified theorems is checked against published empirical evidence. Status: **✅ confirmed**, **⚠️ partially confirmed**, or **❌ contradicted**.

---

## Prediction 1: Safety fine-tuning has diminishing returns
**Status: ✅ Confirmed**

- MART (Ge et al., NAACL 2024): violation rate drops 84.7% in 4 rounds, gains front-loaded in rounds 1–2.
- Equilibrate RLHF (Tan et al. 2025, arXiv:2502.11555): safety improves only +2.1pp from 20K→60K DPO examples; meanwhile BBH reasoning collapses 23pp and HumanEval drops 60%.
- Jailbreak Scaling Laws (Balashankar & Chandrasekaran 2026, arXiv:2603.11149): all attacks follow saturating exponentials — diminishing returns on both sides.
- Sleeper Agents (Hubinger et al. 2024, arXiv:2401.05566): backdoor behaviors persist through SFT + RLHF + adversarial training. Adversarial training makes the model *better at hiding* the behavior, not removing it.

**Match to theorem:** Interior Stability predicts deep-basin vulnerabilities survive bounded surface shifts. Empirically, 10 adversarial examples undo alignment entirely (Qi et al. 2024, arXiv:2310.03693), confirming the shift budget is small relative to basin depth.

---

## Prediction 2: Longer contexts make defense exponentially harder
**Status: ✅ Confirmed**

- Many-Shot Jailbreaking (Anil et al., Anthropic, NeurIPS 2024): harmful response rate scales as a power law from ~0% at 5 shots to 80%+ at 128 shots across all 5 tested models. No plateau observed through 70K tokens.
- Kim et al. (ACL 2025): *Lorem ipsum filler text* achieves comparable ASR to actual harmful demonstrations — context length, not content, is the driver.
- Fu et al. (arXiv:2602.08874, 2026): GPT-oss-120b safety drops from 93% → 37% at 64K tokens; Claude-Sonnet-4.5 from 84% → 42%.
- LongSafety benchmark (Lu et al., ACL 2025): many long-context LLMs score below 50% safe response rate.

**Match to theorem:** Cost Asymmetry predicts defense cost grows as N^d. The power-law scaling of many-shot attacks (dimension-independent attack cost, exponentially growing defense surface) is exactly this asymmetry instantiated.

---

## Prediction 3: Agentic tool-use degrades defense exponentially
**Status: ✅ Confirmed**

- InjecAgent (Zhan et al., ACL 2024): GPT-4 ReAct agent compromised 24–47% of the time via indirect prompt injection (IPI).
- Agent Security Bench (Zhang et al., arXiv:2410.02644): mixed DPI+IPI+PoT attacks achieve 84.3% ASR; best defense leaves 44.5% residual.
- Slingshot (arXiv:2602.02395): RL attacker raises ASR from 1.7% → 67%; transfers zero-shot to Gemini 2.5 Flash (56%) and DeepSeek V3.1 (57.8%).
- Scale AI data: single-turn → multi-turn attack success jumps from 13% → 92%.
- Kumar et al. (arXiv:2410.13886): refusal behaviors from RLHF don't transfer to tool-calling contexts.

**Match to theorem:** Pipeline Lipschitz Degradation predicts K^n growth in the failure band with n tool stages. The empirical finding that *refusal doesn't transfer to tool-calling* is consistent: the pipeline composition introduces new failure modes that single-turn alignment doesn't cover.

---

## Prediction 4: Temperature sampling must produce unsafe outputs at boundary
**Status: ✅ Confirmed**

- "The Instability of Safety" (arXiv:2512.12066, Dec 2025): 18–28% of harmful prompts flip between refusal and compliance depending on seed/temperature. Safety index drops 0.977 → 0.942 from T=0.0 → T=1.0 (p < 0.001).
- Spearman ρ = −0.47 to −0.70 between compliance rate and stability — models waver most on borderline prompts (exactly boundary prompts).
- Single-shot safety eval agrees with multi-sample ground truth only 92.4% of the time.

**Match to theorem:** Stochastic dichotomy predicts E[f(D(z))] = τ at boundary points, so non-deterministic sampling must sometimes exceed τ. The empirical finding that *borderline prompts have highest variance* directly confirms boundary-point instability.

---

## Prediction 5: Quantization preserves deep vulnerabilities
**Status: ✅ Confirmed**

- Skoltech (arXiv:2502.15799): LLaMA FP16 safety 93.06% → AWQ int4 89.50% (−3.6pp) → QUIP# int2 84.25% (−8.8pp). Degradation is gradual, not catastrophic — deep vulnerabilities survive, shallow ones shift.
- Enkrypt AI (arXiv:2404.04392): 2-bit significantly increases vulnerability; 4-bit and 8-bit show variable effects, sometimes *improving* robustness ("sweet spot").
- ETH "Mind the Gap" (ICML 2025): adversarial exploitation of quantization error achieves 85% content injection — quantization *creates new* attack surface while preserving old ones.

**Match to theorem:** Interior Stability + Crossing Preservation predict that perturbations bounded by ε preserve vulnerabilities with margin > ε. The gradual degradation pattern (deeper quantization = more vulnerability) matches: INT8 (small ε) preserves almost everything; INT4/INT2 (larger ε) shifts the boundary but preserves deep basins.

---

## Prediction 6: Model merging preserves deeper parent's vulnerabilities
**Status: ✅ Confirmed**

- Hammoud et al. (EMNLP 2024, arXiv:2406.14563): "One Bad Model Spoils the Bunch" — merging even one misaligned model propagates misalignment through the result across TIES, DARE, SLERP, and weighted averaging.
- TrojanMerge (arXiv:2604.00627, 2025): adversarial merge raises Llama 3 harmful score from 1.0% → 81.0%. Even standard clean merges show vulnerability inheritance. TIES Top-K pruning does *not* mitigate — HS actually rises from 56% → 88.1% as Top-K increases.

**Match to theorem:** Interior Stability for convex combinations predicts vulnerabilities survive unless the merge ratio is very small. The empirical finding that even one bad model "spoils the bunch" and that pruning-based mitigation fails directly confirms this — deep-basin vulnerabilities from the weaker parent dominate the merge.

---

## Prediction 7: Adversarial training fragments but doesn't eliminate
**Status: ✅ Confirmed**

- Liu et al. (arXiv:2603.20957, March 2026): literally titled "Alignment Whack-a-Mole" — safety alignment blocks verbatim recall but fine-tuning reactivates it on a different surface.
- IRIS (NAACL 2025): after GCG was patched by Circuit Breakers, IRIS achieved 25% ASR via a completely new attack vector.
- ATLA (arXiv:2503.12339, 2025): near-100% ASR adversarial suffix attacks with 80% fewer queries than prior methods.
- Qi et al. (2024): RLHF results in "surface-level changes" — 10 examples at $0.20 erase alignment entirely.

**Match to theorem:** Fragment Size theorem predicts rougher surfaces (higher L from adversarial training) produce smaller but more numerous basins. The whack-a-mole pattern — patching one attack family while new ones emerge — is exactly fragmentation without volume reduction.

---

## Prediction 8: Defense-in-depth for wrappers is counterproductive past threshold
**Status: ⚠️ Partially confirmed**

- FAR.AI/UK AISI STACK attack (arXiv:2506.24068, 2025): conventional attacks drop to 0% against multi-layer defenses, but adaptive STACK achieves 71% ASR by attacking layers sequentially. Multi-layer defenses create a false sense of security.
- TRYLOCK (arXiv:2601.03300): 4 heterogeneous layers reduce ASR from 46.5% → 5.6%, but each layer has unique blind spots.
- Key nuance: multi-layer defenses *do* help against non-adaptive attacks. The counterproductive effect emerges specifically against adaptive attackers who exploit the inter-layer signaling.

**Match to theorem:** Pipeline Impossibility predicts the ε-band widens with ∏K_i. The STACK result confirms that adaptive attackers exploit the compositional structure. The TRYLOCK result suggests a non-trivial optimal depth exists — consistent with the prediction of an n* threshold. **Not fully confirmed:** the pure Lipschitz amplification effect (defense getting worse with more layers even without adaptive attacks) is not directly demonstrated; the empirical counterproductivity comes from information leakage between layers, a related but distinct mechanism.

---

## Prediction 9: Jailbreak transfer is asymmetric (deep → shallow)
**Status: ✅ Confirmed**

- Zhao et al. (arXiv:2401.17256, ICML 2025): formally named "Weak-to-Strong Jailbreaking" — small unaligned model shifts large aligned model's output distribution.
- IRIS (NAACL 2025) transfer cascade: GPT-3.5 90% → GPT-4o-mini 86% → GPT-4o 76% → o1-mini 54% → o1-preview 48%. Monotonically decreasing with model capability/safety.
- arXiv:2506.12913 (2025): transfer success predicted by jailbreak strength × representational similarity — deeper jailbreaks transfer more reliably.

**Match to theorem:** Transferability theorem predicts {f > τ+δ} ⊆ {g > τ}, so deep-basin attacks transfer while shallow ones don't. The monotone decrease in transfer rate along the capability ladder (90% → 48%) matches the upper-triangular transfer matrix prediction.

---

## Prediction 10: Alignment tax proportional to unsafe volume
**Status: ✅ Confirmed**

- Huang et al. "Safety Tax" (arXiv:2503.00555, 2025): DirectRefusal alignment costs −30.91% reasoning accuracy; SafeChain costs −7.09%.
- Niu et al. NSPO (arXiv:2512.11391): SafeRLHF on Llama-3-8B: AlpacaEval −43.6pp, GSM8K −23.7pp.
- Equilibrate RLHF: BBH −23pp, HumanEval −60% from 20K→60K safety data.
- Huang et al. (arXiv:2603.00047, 2026): formally proved alignment tax = squared projection of safety gradient onto capability subspace. Safety and capability directions are non-orthogonal → Pareto tradeoff geometrically necessary.

**Match to theorem:** Discrete Dilemma predicts complete defense forces non-injectivity (information loss). The empirical alignment tax — especially the formal result that it equals the squared projection of safety onto capability — is a continuous analogue of the discrete information-loss mechanism.

---

## Prediction 11: Random red-teaming budget is O(1/q)
**Status: ⚠️ Partially confirmed**

- No paper directly measures "random probes to first jailbreak" as a function of basin rate.
- However: Slingshot reports expected attempts to first success dropping from 52.3 → 1.3 with an RL-trained attacker. IPI Competition (arXiv:2603.15714) reports 8,648 successful attacks from 272,000 attempts (~3.2% raw hit rate) on frontier models — but these are not random probes.
- The basin rates from the companion paper (93.9% for Llama, 64.3% for GPT-OSS) predict 1–2 random queries suffice, which is consistent with the empirical ease of finding jailbreaks for models with high vulnerability rates.

**Match to theorem:** hit_probability_tends_to_one gives the formula. The prediction is consistent with observed ease of jailbreaking but lacks a direct experimental test of random probing budgets.

---

## Prediction 12: Safety patches have blast radius → capability regression
**Status: ✅ Confirmed**

- All alignment tax evidence from Prediction 10 applies (regression is the blast radius manifesting).
- Slingshot: Meta-SecAlign-8B, fine-tuned against prompt injection, became *more* vulnerable to tag-along attacks than base (39.2% vs 11.5%) — patching one vector opened another.
- Sleeper Agents: adversarial training doesn't remove the behavior, makes it *better hidden* — the blast radius changes the surface topology without eliminating the basin.

**Match to theorem:** patching_nonlocal + basin_hausdorff_distance_bound predict changes within ε of the boundary propagate to a ball of radius (f(x)−τ)/L. The deeper the patched vulnerability, the larger the affected region. SecAlign's backfire (patching injection vulnerability increased tag-along vulnerability) is consistent with overlapping blast radii.

---

## Prediction 13: Jailbreaks connected by interpolation on convex embeddings
**Status: ⚠️ Partially confirmed**

- No paper directly tests embedding-space interpolation between jailbreaks.
- However: universal and transferable adversarial suffixes (Zou et al. 2023, arXiv:2307.15043) suggest a connected attack manifold — perturbations in embedding space smoothly transition between attack variants.
- GCG-style attacks explore neighborhoods in token space via gradient descent, implicitly assuming local connectivity.
- The quasiconcavity assumption is empirically untested for real LLM alignment surfaces.

**Match to theorem:** basin_connected_of_convex_domain requires quasiconcavity, which may or may not hold. The prediction is theoretically valid but empirically untested in its strong form (linear interpolation in embedding space).

---

## Prediction 14: Pareto frontier that no wrapper can cross
**Status: ✅ Confirmed**

- Huang et al. (arXiv:2603.00047, 2026): formally proved alignment tax is geometrically necessary — safety and capability gradients are non-orthogonal, creating an inherent Pareto tradeoff.
- All alignment-tax papers show the tradeoff curve: more safety = less capability, with no method escaping the frontier.
- GPT-5-Mini (peak AD 0.50, basin rate 0%) demonstrates the escape route: making U_τ empty by inherently safe design, not wrapping.

**Match to theorem:** basin_measure_monotone_threshold + defense_incompleteness predict the monotone Pareto curve. The formal alignment-tax result from Huang et al. 2026 is an independent proof of the same phenomenon from a different mathematical angle.

---

## Summary

| # | Prediction | Status | Key Evidence |
|---|---|---|---|
| 1 | Diminishing safety returns | ✅ | MART, Equilibrate, Sleeper Agents |
| 2 | Long context vulnerability | ✅ | Many-Shot (NeurIPS 2024), Kim (ACL 2025), Fu (2026) |
| 3 | Agentic tool-use degradation | ✅ | InjecAgent, ASB, Slingshot, Scale AI |
| 4 | Temperature boundary instability | ✅ | Instability of Safety (2025) |
| 5 | Quantization preserves deep vulns | ✅ | Skoltech (2025), Enkrypt AI, ETH |
| 6 | Merging preserves weaker parent | ✅ | EMNLP 2024, TrojanMerge (2025) |
| 7 | Adversarial training fragments | ✅ | "Whack-a-Mole" (2026), IRIS, ATLA |
| 8 | Defense-in-depth counterproductive | ⚠️ | STACK (2025) confirms adaptive case; pure Lipschitz effect untested |
| 9 | Asymmetric transfer | ✅ | Weak-to-Strong (ICML 2025), IRIS |
| 10 | Alignment tax ∝ unsafe volume | ✅ | Safety Tax (2025), NSPO, formal proof (2026) |
| 11 | Random probing budget O(1/q) | ⚠️ | Consistent but no direct test |
| 12 | Patch blast radius | ✅ | SecAlign backfire, Sleeper Agents |
| 13 | Interpolation connectivity | ⚠️ | Consistent (GCG locality) but untested |
| 14 | Pareto frontier | ✅ | Formal proof (2026), all tax papers |

**11 of 14 confirmed. 3 partially confirmed (consistent with evidence but lacking direct tests). 0 contradicted.**
