---
layout: home

hero:
  name: "The Defense Trilemma"
  text: "Why prompt-injection defense wrappers fail."
  tagline: >
    A geometric impossibility theorem for continuous, utility-preserving wrapper
    defenses on connected prompt spaces — mechanized in Lean 4, validated on
    three LLMs.
  actions:
    - theme: brand
      text: Read the theorems
      link: /theorems/
    - theme: alt
      text: End-to-end proof map
      link: /proofs/
    - theme: alt
      text: Defense trilemma
      link: /trilemma

features:
  - icon: 🔺
    title: Three properties, pick two
    details: >
      Continuity + utility preservation + completeness cannot coexist on a
      connected prompt space. Every continuous wrapper that fixes safe inputs
      must leave some boundary input unremediated.
    link: /trilemma
  - icon: 📐
    title: A three-tier escalation
    details: >
      Boundary Fixation (pointwise) → ε-Robust Constraint (Lipschitz
      neighborhood) → Persistent Unsafe Region (positive-measure, under
      transversality).
    link: /theorems/
  - icon: 🧮
    title: Discrete and continuous
    details: >
      Same impossibility under both continuous topology (Tietze bridge) and
      pure counting arguments on finite sets — no topology required for the
      discrete dilemma.
    link: /proofs/discrete-to-continuous
  - icon: 🔁
    title: Multi-turn, stochastic, pipelined
    details: >
      Impossibility recurs at every turn, survives randomization in expectation,
      and amplifies multiplicatively (Kⁿ) through agent tool-calls.
    link: /theorems/pipeline
  - icon: 🧠
    title: Representation-independent
    details: >
      A single meta-theorem unifies the continuous, discrete and stochastic
      paths: utility preservation + any form of regularity ⇒ Fix(D) ⊋ S.
    link: /theorems/meta-theorem
  - icon: ✅
    title: Machine-verified
    details: >
      46 Lean 4 files, ≈360 theorems, zero `sorry`, three standard axioms
      (propext, Classical.choice, Quot.sound). <code>lake build</code> is green.
    link: /lean-artifact
---

## The one-paragraph argument

Let $X$ be a connected Hausdorff space of prompts and let $f\colon X\to\mathbb{R}$
be a continuous alignment-deviation score with threshold $\tau$. A
**wrapper defense** is a continuous map $D\colon X\to X$ that leaves every
safe prompt unchanged. Because $D$ is continuous and safe inputs are fixed,
the fixed-point set $\mathrm{Fix}(D)$ is a **closed** set containing the
**open** safe region $S_\tau = \{f<\tau\}$. In a connected space an open set
cannot simultaneously be closed unless it is all of $X$, so the closure of
$S_\tau$ must contain new points — points where $f(z)=\tau$ exactly.
Every such $z$ is fixed by $D$, so $D$ passes them through unchanged with
no remediation. The three successively stronger theorems
([T1](/theorems/boundary-fixation), [T2](/theorems/eps-robust),
[T3](/theorems/persistent)) upgrade this single fixed point first to a
Lipschitz-constrained neighborhood and finally, under transversality, to a
positive-measure region that remains strictly above $\tau$ after defense.

## End-to-end logical picture

```mermaid
flowchart TB
    classDef assumption fill:#eef3fb,stroke:#3455db,color:#1d2433;
    classDef theorem fill:#fff6e0,stroke:#c78a00,color:#1d2433;
    classDef conclusion fill:#fde3e3,stroke:#9c2424,color:#1d2433;
    classDef bridge fill:#e6f4ea,stroke:#256a3a,color:#1d2433;

    A1["X connected Hausdorff"]:::assumption
    A2["f : X → ℝ continuous<br/>S_τ, U_τ ≠ ∅"]:::assumption
    A3["D : X → X continuous<br/>D = id on S_τ"]:::assumption
    A4["f, D Lipschitz<br/>(L, K)"]:::assumption
    A5["Transversality:<br/>G > ℓ(K+1)"]:::assumption

    T1["T1 — Boundary Fixation<br/>∃ z : f(z)=τ ∧ D(z)=z"]:::theorem
    T2["T2 — ε-Robust Constraint<br/>f(D(x)) ≥ τ − LK·d(x,z)"]:::theorem
    T3["T3 — Persistent Unsafe Region<br/>μ(S) > 0 and f(D(x)) > τ on S"]:::theorem

    M["Meta-theorem:<br/>regularity ⇒ Fix(D) ⊋ S"]:::bridge
    D1["Discrete dilemma<br/>(no topology)"]:::bridge
    Tt["Tietze bridge<br/>discrete data → continuous f"]:::bridge

    C["No continuous utility-preserving<br/>wrapper defense is complete."]:::conclusion

    A1 --> T1
    A2 --> T1
    A3 --> T1
    T1 --> T2
    A4 --> T2
    T2 --> T3
    A5 --> T3

    T1 --- M
    D1 --- M
    M --> C
    T3 --> C
    Tt --> T1

    linkStyle default stroke:#4a5a7a,stroke-width:1.3px;
```

## Where to go next

| If you want to… | Start at |
|---|---|
| See the three tiers side-by-side | [Theorem index](/theorems/) |
| Follow the five-step geometric proof | [Boundary five-step proof](/proofs/boundary-five-step) |
| Understand the trilemma picture | [The Defense Trilemma](/trilemma) |
| See how discrete data connects to the continuous theorems | [Discrete → continuous](/proofs/discrete-to-continuous) |
| Understand why pipelines make it *worse* | [Pipeline Degradation](/theorems/pipeline) |
| Inspect the Lean 4 proof structure | [Lean artifact](/lean-artifact) |
| Know what the theorem does *not* say | [Limitations](/limitations) |
