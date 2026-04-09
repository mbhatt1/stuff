# Research: Are Agentic/Tool-Use LLM Systems Harder to Defend Than Base Chat Models?

## Summary

Yes — empirically, agentic and tool-augmented LLM systems are substantially harder to defend than base chat models, and the gap is large and well-documented. Multiple 2024–2026 benchmarks show attack success rates against agents ranging from 27% to 84% depending on attack type, while defenses designed for chat (delimiters, paraphrasing, instructional prevention) reduce agent attack success by only ~10–34 percentage points before plateauing at still-high rates. A key structural reason: refusal behaviors learned in chatbot RLHF do not reliably transfer to agentic tool-calling contexts, creating a systematic safety deficit even in safety-trained frontier models.

---

## Findings

### 1. Indirect Prompt Injection (IPI) Is a Proven, Scalable Threat Unique to Tool-Augmented Systems

IPI is the defining attack of agentic systems: malicious instructions embedded in external content (emails, tool responses, retrieved documents, webpages) hijack the agent's action sequence without the user issuing any adversarial input. A 2026 large-scale red-teaming competition (Dziemian et al., arXiv:2603.15714) evaluated 13 frontier models across 41 agent scenarios with 272,000 attack attempts by 464 participants, producing **8,648 successful attacks**. All models proved vulnerable. Attack success rates ranged from **0.5% (Claude Opus 4.5) to 8.5% (Gemini 2.5 Pro)**. Critically, the competition tested a *dual-objective* attack: succeed AND conceal — meaning successful attacks leave no visible trace in the user-facing response. Universal attack strategies transferred across **21 of 41 behaviors and multiple model families**, indicating fundamental weaknesses in instruction-following architectures rather than model-specific bugs.

*Citation:* [Dziemian et al. (2026), arXiv:2603.15714](https://arxiv.org/abs/2603.15714)

---

### 2. InjecAgent: Benchmark Shows GPT-4 Agents Compromised 24–47% of the Time

InjecAgent (Zhan et al., ACL Findings 2024) is the first systematic benchmark for IPI in tool-integrated agents. It covers **1,054 test cases, 17 user tools, and 62 attacker tools** across two attack intentions: direct harm and private data exfiltration. Key result: **ReAct-prompted GPT-4 was successfully attacked 24% of the time** under standard injection. When attacker instructions were reinforced with a "hacking prompt" enhancement, success rates **nearly doubled to ~47%**. The benchmark tested 30 different agent configurations and found universal vulnerability. This is an attack vector that does not exist at all for vanilla chat models.

*Citation:* [Zhan et al. (2024), InjecAgent, ACL Findings, arXiv:2403.02691](https://arxiv.org/abs/2403.02691)

---

### 3. Agent Security Bench (ASB): 84.30% Peak Attack Success Rate Across 13 LLMs

ASB (Zhang et al., 2024, arXiv:2410.02644) is the most comprehensive empirical study to date, covering **10 agent scenarios, 400+ tools, 27 attack/defense combinations, and 13 LLM backbones** including GPT-4o, Claude-3.5 Sonnet, LLaMA3-70B, and Gemma2-27B. Key numbers:

| Attack Type | Avg ASR | Notable High | Notable Low |
|---|---|---|---|
| **Mixed Attack** (DPI + IPI + Memory Poison) | **84.30%** | Gemma2-27B: 100%, GPT-4o: 89.25% | LLaMA3-8B: 40.75% |
| **Direct Prompt Injection (DPI)** | **72.68%** | GPT-3.5 Turbo: 98.40%, Gemma2-27B: 96.75% | LLaMA3-8B: 33.75% |
| **Indirect Prompt Injection (IPI)** | **27.55%** | GPT-4o: 62.00%, Claude-3.5 Sonnet: 56.00% | LLaMA3.1-8B: 5.50% |
| **PoT Backdoor Attack** | **42.12%** | GPT-4o: **100%**, GPT-4o-mini: 95.50% | — |
| **Memory Poisoning** | **7.92%** | LLaMA3.1-8B: 25.65% | — |

**Defenses are largely ineffective.** After applying the best-performing defense (Dynamic Prompt Rewriting), DPI average ASR only drops from 78.38% → **44.45%**. IPI defenses (Delimiter, Sandwich Prevention, Instructional Prevention) reduce IPI attack success by at most 3 percentage points. Most defenses also degrade benign task performance by 1–20%.

**Counter-intuitive capability finding:** More capable models are initially *more* vulnerable to instruction-following attacks (GPT-3.5 Turbo: 98.40% DPI ASR vs. GPT-4o: 55.50%), because larger models follow injected instructions more faithfully. Only at the highest capability levels does the refusal rate compensate (GPT-4o refusal rate: 20.05% vs. GPT-3.5 Turbo: 3.00%).

*Citation:* [Zhang et al. (2024), ASB, arXiv:2410.02644](https://arxiv.org/abs/2410.02644)

---

### 4. AgentDojo (NeurIPS 2024): Attacks Succeed in <25% of Cases But Expose Unique Agent Vulnerabilities

AgentDojo (Debenedetti et al., NeurIPS 2024, arXiv:2406.13352) is a dynamic benchmark using **realistic multi-step agent scenarios** (e-mail management, banking, travel booking). Its more conservative attack success numbers (~25% against the best agents) reflect harder, real-world task structures. However, it establishes that current LLMs **solve fewer than 66% of tasks correctly** even without any attack, showing that tool-integrated deployment compounds both capability and security failures. Defenses like secondary attack detectors reduce attack success further but come with utility costs.

*Citation:* [Debenedetti et al. (2024), AgentDojo, NeurIPS 2024, arXiv:2406.13352](https://arxiv.org/abs/2406.13352)

---

### 5. IPI in the Wild: Near-100% Retrieval Injection Across 11 Benchmarks

A 2026 study on IPI in RAG and agentic systems (arXiv:2601.07072) demonstrated **near-100% injection retrieval success across 11 benchmarks and 8 embedding models**, including both open-source and proprietary services. The paper presented the first **end-to-end IPI exploits under natural queries** in realistic external corpora, spanning both RAG and agentic systems with diverse attack objectives. This establishes IPI as a *practical*, not just theoretical, threat — retrieving an adversarial document is trivially achievable against current embedding models.

*Citation:* [arXiv:2601.07072 (2026), Indirect Prompt Injection in the Wild](https://arxiv.org/pdf/2601.07072)

---

### 6. Multi-Step Agent Jailbreaks (Tag-Along Attacks): 67% ASR on Extreme Tasks via RL

"David vs. Goliath" (arXiv:2602.02395) introduces **Tag-Along Attacks**: a peer-agent adversary that exploits the functional obligation of an agentic Operator to parse user inputs. Using a small RL-trained attacker model (Slingshot, 7B parameters, 156 A100 GPU-hours), on held-out "extreme difficulty" tasks where baseline attack success was **1.7%**:

- Slingshot achieves **67.0% ASR** on the same tasks after RL training
- Pass@10 rises from 15.0% → **80.4%**
- Refusal rate drops from 66.8% → **10.0%**
- Expected attempts to first success collapses from 52.3 → **1.3**

Zero-shot transfer results (without retraining on target model):
- Gemini 2.5 Flash: **56.0% ASR**
- DeepSeek V3.1: **57.8% ASR**
- Meta-SecAlign-8B (defense-fine-tuned model): **39.2% ASR** — *more* vulnerable than its unmerged base (Llama-3.1-8B: 11.5%)

The last result is damning: a model fine-tuned to resist prompt injection became *more* vulnerable to a peer-agent attack vector. Defenses designed for one attack type erode general robustness via an "alignment tax."

*Citation:* [David vs. Goliath (2026), arXiv:2602.02395](https://arxiv.org/abs/2602.02395)

---

### 7. Multi-Turn Attacks Invert Single-Turn Safety: 13% → 92% Attack Success Rate

For base chat models, single-turn defenses are reasonably effective. For agentic multi-step interactions, they collapse. A Scale AI study (referenced in VentureBeat, 2025) found that open-weight models **block 87% of single-turn malicious requests** but attack success rates **climb from 13% to 92%** when attackers use multi-turn probing and reframing across exchanges. A separate study (arXiv:2508.07646, *Multi-Turn Jailbreaks Are Simpler Than They Seem*) found multi-turn attacks exceed **70% ASR** against models with single-digit single-turn ASRs on HarmBench. The Crescendo multi-turn attack (USENIX Security 2025) achieves **29–61% higher performance vs. SOTA single-turn methods** on GPT-4 and **49–71% higher on Gemini-Pro**. Agents are multi-turn by design.

*Citations:* [Scale AI/VentureBeat (2025)](https://venturebeat.com/security/ai-models-block-87-of-single-attacks-but-just-8-when-attackers-persist); [arXiv:2508.07646](https://arxiv.org/pdf/2508.07646); [Crescendo, USENIX Security 2025](https://www.usenix.org/system/files/conference/usenixsecurity25/sec25cycle1-prepub-805-russinovich.pdf)

---

### 8. Tool-Call Depth and Safety Degradation: Refusal Transfer Fails in Agentic Contexts

Multiple independent lines of evidence show that **chat-trained refusals do not transfer to tool-calling agent settings**:

- Kumar et al. (2024, arXiv:2410.13886), *Refusal-Trained LLMs Are Easily Jailbroken As Browser Agents*, finds that refusal behaviors from RLHF do not generalize to autonomous browser agent tasks.
- ASB finds that agent performance is **consistently below LLM leaderboard performance** in no-attack baselines, suggesting that tool-integrated contexts are inherently harder for safety mechanisms.
- Slingshot (arXiv:2602.02395) confirms that long context windows in agents compound this effect: "many-shot" and context-overflow jailbreaking techniques dilute safety instructions at higher tool-call depths (citing Anil et al., 2024, *Many-Shot Jailbreaking*).
- ToolTweak (arXiv:2510.02554) shows that **tool selection itself is attackable**: adversarially manipulated tool names increase malicious tool selection rates from a **~20% baseline to 81%**, with strong transferability across model families.

*Citations:* [Kumar et al. (2024), arXiv:2410.13886](https://arxiv.org/abs/2410.13886); [ToolTweak (2025), arXiv:2510.02554](https://arxiv.org/html/2510.02554v1)

---

### 9. "Your Agent Is More Brittle Than You Think": Multi-Agent Pipeline Amplifies Risk

A 2026 paper (arXiv:2604.03870) focuses on the systemic vulnerabilities of LLM agents in **multi-agent architectures** using open-source frameworks (AutoGen, etc.). It shows that while single-turn benchmarks evaluate isolated agent security, real deployments with uncontrolled privilege exposure and hidden inter-system interactions have dramatically higher attack surfaces. The paper finds that open-source agentic frameworks have insufficient isolation between agent trust levels, making privilege escalation via IPI far more dangerous than single-agent evaluations suggest.

*Citation:* [arXiv:2604.03870 (2026), Your Agent Is More Brittle Than You Think](https://arxiv.org/html/2604.03870v1)

---

## Key Numbers at a Glance

| Metric | Value | Source |
|---|---|---|
| Peak agent attack success rate (mixed) | **84.30%** | ASB (Zhang et al., 2024) |
| IPI success, GPT-4 ReAct agent | **24–47%** | InjecAgent (Zhan et al., 2024) |
| IPI success, GPT-4o (ASB) | **62.00%** | ASB (Zhang et al., 2024) |
| PoT Backdoor, GPT-4o | **100%** | ASB (Zhang et al., 2024) |
| Retrieval injection success (RAG/agents) | **~100%** | arXiv:2601.07072 (2026) |
| RL-trained agent-to-agent jailbreak | **67% ASR** | Slingshot, arXiv:2602.02395 |
| Transfer to Gemini 2.5 Flash | **56.0% ASR** | Slingshot, arXiv:2602.02395 |
| Defense-tuned model regression | **39.2% ASR** (vs 11.5% base) | Slingshot, arXiv:2602.02395 |
| Single-turn→Multi-turn attack inversion | 13% → **92%** | VentureBeat/Scale AI |
| Tool selection attack success | **~20% → 81%** | ToolTweak (2025) |
| Best defense residual ASR (DPI) | **44.45%** after best defense | ASB (Zhang et al., 2024) |

---

## Sources

**Kept:**
- [InjecAgent (Zhan et al., ACL Findings 2024)](https://arxiv.org/abs/2403.02691) — Foundational IPI benchmark; direct vulnerability numbers for tool-integrated agents.
- [Agent Security Bench (Zhang et al., 2024)](https://arxiv.org/abs/2410.02644) — Most comprehensive multi-attack agent benchmark with 13 LLMs and 27 attack/defense variants; gold standard numbers.
- [AgentDojo (Debenedetti et al., NeurIPS 2024)](https://arxiv.org/abs/2406.13352) — Realistic scenario-based benchmark; real-world-calibrated attack success numbers.
- [IPI Competition (Dziemian et al., 2026)](https://arxiv.org/abs/2603.15714) — Large-scale human red-team data; concealment-aware IPI testing; 272K attacks.
- [IPI in the Wild (arXiv:2601.07072, 2026)](https://arxiv.org/pdf/2601.07072) — Retrieval injection end-to-end; near-100% success in realistic settings.
- [David vs. Goliath/Slingshot (arXiv:2602.02395)](https://arxiv.org/abs/2602.02395) — Agent-to-agent RL jailbreaking; shows alignment tax of specialized defenses.
- [Multi-Turn vs Single-Turn (VentureBeat, 2025; arXiv:2508.07646; Crescendo USENIX 2025)](https://venturebeat.com/security/ai-models-block-87-of-single-attacks-but-just-8-when-attackers-persist) — Empirical confirmation that multi-step nature of agents inverts single-turn defenses.
- [Refusal-Trained LLMs as Browser Agents (Kumar et al., 2024)](https://arxiv.org/abs/2410.13886) — Refusal transfer failure; cited widely as evidence of structural agent safety gap.
- [ToolTweak (arXiv:2510.02554)](https://arxiv.org/html/2510.02554v1) — Tool selection vulnerability; shows safety fails even before instruction is executed.
- [Your Agent Is More Brittle (arXiv:2604.03870, 2026)](https://arxiv.org/html/2604.03870v1) — Multi-agent framework amplification of IPI risk.

**Dropped:**
- AI Jailbreaking enterprise blog (witness.ai) — No original empirical data; qualitative survey.
- LinkedIn posts (CTI Labs, Adarsh Kumarappan) — Secondary commentary, no primary data.
- CallSphere Tool Guardrails blog — Product marketing content, no experimental rigor.
- redteams.ai jailbreak pipeline article — Tutorial content with no new measurements.

---

## Gaps

1. **Causal mechanism not fully isolated**: We know agents are more vulnerable, but the relative contribution of each factor — long context dilution of safety, untrusted tool output processing, multi-turn interaction, vs. the capability-safety tradeoff — has not been cleanly decomposed in a single controlled experiment.

2. **Production deployment data absent**: All numbers come from benchmarks and red-team competitions; real-world production attack rates on deployed agent systems (Copilots, Claude Code, etc.) are not publicly disclosed.

3. **Computer-use / OS agents understudied**: Most papers focus on text-tool pipelines (email, search, API calls). Computer-use agents (GUI browsing, code execution) face compounded attack surfaces; OS-Harm (Kuntz et al., 2025, arXiv:2506.14866) is an early benchmark but large-scale empirics are thin.

4. **Defense ceiling unclear**: The best-performing defenses tested (ASB) still leave 44% DPI and 25% IPI success. Whether architecturally robust defenses (e.g., formal verification of tool-call arguments, privilege separation, sandboxing) can achieve near-zero ASR at acceptable utility costs remains an open empirical question.

5. **Model-specific safety genealogy**: Slingshot's finding that vulnerability is shared not by capability but by *safety training methodology* suggests that understanding specific training pipelines (Constitutional AI, RLHF data composition) is needed to predict which models will be robust — but this data is not publicly available.

**Suggested next steps**: (1) Read Kumar et al. (arXiv:2410.13886) for the mechanistic case on refusal non-transfer. (2) Read the AgentDojo NeurIPS paper for the most carefully calibrated real-world attack success numbers. (3) Examine arXiv:2510.05244 (*Are Firewalls All You Need?*) which claims a modular defense achieving near-0% IPI ASR across ASB, AgentDojo, InjecAgent, and τ-Bench — the most promising defense result in the literature.
