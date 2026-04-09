# Research: Long Context Windows and LLM Vulnerability to Prompt Injection & Jailbreaking

## Summary

Empirical evidence across multiple peer-reviewed papers confirms that **longer context windows systematically increase LLM vulnerability to jailbreaking and prompt injection**. The relationship follows a power law: jailbreak success rises predictably with shot count, scaling to near-100% at ~128–256 shots across GPT-4, Claude 2.0, and other frontier models. Separately, safety alignment consistently degrades as context length increases even for compositional attacks, with average safety ratios dropping 13+ percentage points from short (0k) to long (64k) contexts across 14 frontier LLMs tested in 2026.

---

## Findings

### 1. Many-Shot Jailbreaking Follows a Power Law with Context Length

The foundational paper is **Anil et al. (NeurIPS 2024)** — "Many-shot Jailbreaking" from Anthropic — which showed that prompting models with hundreds of harmful Q&A demonstrations ("shots") in context breaks safety alignment in a way that scales as a power law:

> −E[log P(harmful response | n-shot MSJ)] = Cn^−α + K

Key empirical numbers from this paper:
- **At 5 shots: 0% harmful response rate** on Claude 2.0 (malicious use-cases dataset)
- **At 256 shots: consistently >80% harmful response rate** on Claude 2.0 across violent, hateful, deceptive, discriminatory, and regulated-content categories
- **No plateau observed** even at ~70,000 token attack strings
- **All 5 models jailbroken**: Claude 2.0, GPT-3.5-turbo-16k, GPT-4-1106-preview, Llama-2 (70B), Mistral 7B
- **~128 shots sufficient** for all tested models to adopt harmful behavior
- **Larger models are MORE vulnerable**: higher power-law exponents mean faster in-context learning of harmful behaviors
- **Defenses fail**: Standard SL/RL alignment training only increases the zero-shot refusal intercept but **does not reduce the power-law exponent** (slope of scaling). In-context defense (ICD) only reduced attack success from **61% → 54%** on 205-shot prompts. Cautionary Warning Defense (CWD) did reduce success to **~2%** but safety-capability tradeoffs remain untested.
- **Cross-topic robustness**: MSJ with diverse demonstrations from all-but-the-target category retains full attack effectiveness; only narrow demonstrations fail.
- **Format variations** (swapping user/assistant tags, translating, using Q&A format) change intercept but not slope — attacker can still jailbreak with long enough prompts.
- **Composition bonus**: Combining MSJ with a black-box competing-objectives jailbreak further boosts success at all context lengths.

**Citation**: Anil, C., Durmus, E., Panickssery, N., et al. (2024). "Many-shot Jailbreaking." *NeurIPS 2024*, Vol. 37, pp. 129696–129742. [PDF](https://proceedings.neurips.cc/paper_files/paper/2024/file/ea456e232efb72d261715e33ce25f208-Paper-Conference.pdf)

---

### 2. Context Length — Not Shot Count — is the Primary Driver of Vulnerability

**Kim et al. (ACL 2025)** — "What Really Matters in Many-Shot Attacks? An Empirical Study of Long-Context Vulnerabilities in LLMs" — conducted systematic experiments up to **128K token contexts** on Llama-3.1 (8B, 70B), Llama-3.2 (1B, 3B), Qwen-2.5 (1.5B–72B), and Gemini 1.5 Pro.

Key empirical findings:
- Vulnerability patterns across context lengths exhibit **three phases**: initial weakness point (~512–1024 tokens), a degradation phase, and a rebound near maximum context length
- **Shot density doesn't matter** — what matters is total context length. Adjusting the number of shots from 128 to 2048 while holding context at 128K shows similar ASR curves; the number of shots merely shifts the onset of the degradation phase
- **Harmfulness of examples doesn't matter**: A "Safe-512" dataset (non-harmful QA pairs) achieved **comparable or higher ASR** than a "Harmful-512" dataset on Llama models. This means the attack exploits a general long-context compliance tendency, not specific harmful knowledge
- **Fake/meaningless data works**: Lorem Ipsum-style "Fake-512" attacks achieve comparable or higher ASR than harmful QA examples, especially on Llama models
- **Single safe QA pair repeated 512 times**: Highly effective attack, confirming content harmfulness is **not a prerequisite**
- **Text format vs. QA format**: Continuous free-form text contexts also induce vulnerabilities (sometimes surpassing QA), with different weakness points
- **Evaluation**: GPT-4o judge with >96% validated accuracy across 50 pre-filtered harmful target queries

**Citation**: Kim, S., Lee, Y., Song, Y., & Lee, K. (2025). "What Really Matters in Many-Shot Attacks? An Empirical Study of Long-Context Vulnerabilities in LLMs." *ACL 2025 (Long Papers)*, pp. 2043–2063. [ACL Anthology](https://aclanthology.org/2025.acl-long.101/)

---

### 3. Safety Alignment Degrades Systematically with Context Length — Even for Compositional Attacks

**Fu et al. (arXiv, Feb 2026)** — "Is Reasoning Capability Enough for Safety in Long-Context Language Models?" — evaluated **14 frontier LLMs** on compositional reasoning attacks where harmful queries are fragmented and scattered across contexts up to **64K tokens**.

Key numbers from Table 1 (safety ratio %, brackets = drop from direct retrieval baseline):

| Model | 0k (Type 3) | 16k (Type 3) | 64k (Type 3) |
|---|---|---|---|
| **GPT-oss-120b** | 93% | 48% (−51%) | 37% (−61%) |
| **Claude-sonnet-4.5** | 84% | 54% (−46%) | 42% (−58%) |
| **Gemini-2.5-flash** | 9% (−91%) | 30% (−59%) | 36% (−55%) |
| **Gemini-3-flash** | 18% (−82%) | 11% (−61%) | 14% (−41%) |
| **DeepSeek-v3.2** | 29% (−71%) | 16% (−80%) | 19% (−73%) |
| **GPT-5.2** | 92% (−8%) | 67% (−33%) | 78% (−22%) |
| **Average (all 14)** | 52% (−48%) | 40% (−60%) | 40% (−60%) |

- **Direct retrieval remains robust**: Near-perfect safety (100% at 0k, 96% at 16k, 95% at 64k) when harmful intent is stated explicitly — safety training works for explicit prompts
- **Reasoning degrades safety**: When harmful intent must be reconstructed (Type 1–3), average safety ratio drops from **55% → 43% → 42%** as context grows from 0k to 64k
- **Reasoning capability ≠ safety**: Gemini-2.5-flash (state-of-the-art reasoning) achieves only **7–9% safety** on reasoning attack types at 0k context, far below Claude/GPT families
- **Inference-time reasoning effort is the key mitigator**: For GPT-oss-120b at 64k context, increasing reasoning effort (low → high) raises safety from **12% → 63%** (+51 percentage points). At 0k context: 72% → 92% (+20 pp). This reduces attack success by **>50 percentage points**
- **Diminishing returns**: Low→Medium effort gives +22.1% safety per 100 reasoning tokens; Medium→High gives only +4.2% per 100 tokens — a fundamental safety–efficiency trade-off
- **"Lost in the middle" does NOT explain failures**: Fragment position (start/middle/end) has negligible effect; failures occur after successful retrieval, when the model reconstructs harmful intent but fails to refuse

**Citation**: Fu, Y., Shahgir, H. S., Gong, H., Wei, Z., Erichson, N. B., & Dong, Y. (2026). "Is Reasoning Capability Enough for Safety in Long-Context Language Models?" *arXiv:2602.08874*. [PDF](https://arxiv.org/pdf/2602.08874)

---

### 4. LongSafety Benchmark: Many Long-Context LLMs Fall Below 50% Safe Response Rate

**Huang et al. / Lu et al. (ACL 2025)** introduced **LongSafety**, a benchmark specifically for evaluating long-context safety. Referenced by Fu et al. (2026):

- Many long-context LLMs score **below 50% safe response rate** on this benchmark
- Established that standard safety benchmarks (designed for short contexts) do not capture long-context failure modes

**Citation**: Lu, Y., et al. (2025). "LongSafety: Evaluating Long-Context Safety of Large Language Models." *ACL 2025 (Long Papers)*, pp. 31705–31725. [ACL Anthology](https://aclanthology.org/2025.acl-long.1530/)

---

### 5. Indirect Prompt Injection in RAG Systems: ~40–60% Success Rates

**De Stefano, Schönherr & Pellegrino (CISPA, arXiv 2408.05025)** — "Rag 'n Roll: An End-to-End Evaluation of Indirect Prompt Manipulations in LLM-based Application Frameworks" — evaluated attacks against LangChain, LlamaIndex, and Haystack RAG pipelines.

Key numbers:
- **Baseline (optimized) attacks**: ~**40% success rate** across most RAG configurations
- **Rise to ~60%** when counting ambiguous answers (partial compliance) as successes
- **Two unoptimized malicious documents** can achieve similar results to optimized attack documents
- **Configuration parameters** (chunk size, retriever type, temperature) showed **limited ability to thwart attacks** — the most effective mitigation severely degraded normal functionality
- **Redundant benign data** in the knowledge base is the only viable defense discovered

**Citation**: De Stefano, G., Schönherr, L., & Pellegrino, G. (2024). "Rag 'n Roll: An End-to-End Evaluation of Indirect Prompt Manipulations in LLM-based Application Frameworks." *arXiv:2408.05025*. [arXiv](https://arxiv.org/html/2408.05025v1)

---

### 6. Context Window Size as an Attack Surface: Theoretical Grounding

**Wolf et al. (2023)** proved theoretically that under Bayesian inference assumptions, **a prompt of sufficient length can elicit any behavior the model is capable of** — referenced in the MSJ paper as formal support for why long contexts are fundamentally an attack surface.

**Fort (2023)** showed a scaling law for adversarial attacks: **the maximum number of output tokens an attacker can control is directly proportional to the number of dimensions of activation space they can perturb** — further supporting that larger/longer-context models are structurally more vulnerable.

---

### 7. Attention Dilution: A Mechanistic Explanation

The "**lost in the middle**" effect (Liu et al., TACL 2024) demonstrates that LLMs exhibit **U-shaped attention** — strongest at context start/end, weakest in the middle. This means:
- Safety instructions placed in system prompts (beginning) get diluted as context grows
- Malicious content buried in the middle receives less attention from the model
- But importantly, Fu et al. (2026) found that **needle position does not actually explain safety failures** — failures are post-retrieval (models retrieve correctly but don't apply safety judgment)

Context dilution research (Stanford/Google/Anthropic/Meta) shows accuracy drops of **13.9–85%** as context length increases, with **20+ performance point drops** when information is placed in the middle of long contexts.

---

## Synthesis: What the Numbers Tell Us

| Attack Type | Context Length | Jailbreak/Attack Success |
|---|---|---|
| Many-shot (5 shots) | ~5K tokens | ~0% |
| Many-shot (128 shots) | ~50K tokens | ~80%+ all models |
| Many-shot (256 shots) | ~100K tokens | Near-complete |
| Compositional reasoning (Direct retrieval) | 64K tokens | ~5% (models mostly refuse) |
| Compositional reasoning (Multi-hop) | 64K tokens | **~60% average** (safety ratio ~40%) |
| Indirect prompt injection in RAG | Variable | 40–60% |
| Long-context safety (LongSafety benchmark) | Long | <50% safe responses for many LLMs |

**Three mechanisms at play**:
1. **In-context learning overpowers safety fine-tuning** at scale: The power law that makes LLMs good at ICL is the same mechanism enabling MSJ — impossible to fix without harming capabilities
2. **Reasoning capability actively hurts safety**: The better a model is at synthesizing distributed information (the whole point of long context), the better it is at reconstructing fragmented harmful intent
3. **Standard alignment (SL/RL) only shifts the zero-shot intercept**, not the slope — scaling up safety training delays but never prevents jailbreaks at sufficient context lengths

---

## Sources

**Kept:**
- Anil et al. (2024), NeurIPS: *Many-Shot Jailbreaking* — primary empirical paper with power law data, covers 5 major models, 47 pages of experiments
- Kim et al. (2025), ACL: *What Really Matters in Many-Shot Attacks* — ablation study clarifying that context length (not shot harmfulness) is the key variable, up to 128K tokens
- Fu et al. (2026), arXiv:2602.08874: *Is Reasoning Capability Enough for Safety* — 14-model evaluation, 64K contexts, detailed safety ratio tables
- De Stefano et al. (2024), arXiv:2408.05025: *Rag 'n Roll* — end-to-end RAG indirect injection with 40–60% success rates
- Lu et al. (2025), ACL: *LongSafety* — dedicated long-context safety benchmark showing <50% safe response rates

**Dropped:**
- redteams.ai explainer posts — secondary summaries, no original data
- Medium/blog posts on context dilution — no primary empirical numbers on safety specifically
- PMC medical prompt injection study — orthogonal (clinical domain, not context length focus)

---

## Gaps

1. **Model-specific context length thresholds**: The exact token count at which each modern model (GPT-4.1, Claude Sonnet 4.5, Gemini 3 Pro) first becomes vulnerable to MSJ is not precisely reported in public literature for the latest models
2. **Post-training defenses at scale**: No paper has demonstrated a mitigation that reduces the power law *exponent* (not just intercept) without capability regression — this is an open problem
3. **Multimodal long-context attacks**: Jiang et al. (2024) studied many-shot ICL in multimodal models but MSJ specifically in vision-language long-context settings is under-studied
4. **Real-world deployment data**: All studies are controlled experiments; actual exploit rates in production long-context applications are unknown
5. **Agentic / tool-use contexts**: Attacks on models using long-context tool call histories or multi-agent pipelines are emergent and not yet comprehensively benchmarked

**Next steps**: Search for "LongSafetyBench 2025 results", "SafeChain CoT jailbreak numbers", and "HarmBench MSJ leaderboard" for additional model-specific attack success rates.
