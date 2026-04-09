# The Defense Trilemma

> **Continuity**, **utility preservation**, **completeness** — pick at most two.

## The statement

::: theorem
Let $X$ be a connected Hausdorff space, $f\colon X\to\mathbb{R}$ continuous
with $S_\tau,U_\tau\ne\emptyset$. No map $D\colon X\to X$ can simultaneously be

1. **continuous** — close prompts produce close rewrites,
2. **utility-preserving** — $D(x)=x$ for every $x\in S_\tau$, and
3. **complete** — $f(D(x))<\tau$ for every $x\in X$.
:::

Any two can coexist — but all three simultaneously is impossible.

## The triangle

```mermaid
flowchart TB
    C["Continuity<br/><span style='font-size:11px'>close prompts → close rewrites</span>"]
    U["Utility Preservation<br/><span style='font-size:11px'>D(x)=x on S_τ</span>"]
    K["Completeness<br/><span style='font-size:11px'>f(D(x)) &lt; τ everywhere</span>"]

    C -. "Continuous + Complete<br/>⇒ destroys utility (collapses X → S_τ)" .- U
    U -. "Utility + Complete<br/>⇒ discontinuous jump at ∂S_τ" .- K
    K -. "Continuous + Utility<br/>⇒ boundary fixation (our result)" .- C

    classDef vertex fill:#eef3fb,stroke:#3455db,color:#1d2433,stroke-width:1.5px;
    class C,U,K vertex;
    linkStyle default stroke:#9c2424,stroke-width:1.4px,stroke-dasharray:4 3;
```

Each dashed edge corresponds to the failure mode that arises if you insist
on the two endpoints of that edge.

## What each failure mode looks like

| Drop                     | Keep                      | Failure mode you get                                           |
|--------------------------|---------------------------|----------------------------------------------------------------|
| ~~Continuity~~           | Utility + Completeness    | A **discontinuous** filter: a hard rejecter at the boundary, equivalent to a blocklist — not a continuous wrapper. |
| ~~Utility preservation~~ | Continuity + Completeness | A **constant** (or generally lossy) map $D(x)=x_0$: every prompt produces the same reply. Utility is destroyed. |
| ~~Completeness~~         | Continuity + Utility      | **Our result:** some boundary points $z$ with $f(z)=\tau$ pass through unchanged. |

## Why the third edge is forced

A continuous utility-preserving complete $D$ would be a **retraction**
$X \twoheadrightarrow S_\tau$ (because $D|_{S_\tau}=\mathrm{id}$ and
$D(X)\subseteq S_\tau$). Continuous retracts of Hausdorff spaces are closed.
But $S_\tau = f^{-1}((-\infty,\tau))$ is **open**, and in a connected space
a non-empty proper subset cannot be clopen. Contradiction.

```mermaid
flowchart LR
    A["D : X → X"] --> B["Continuous + D|_{S_τ}=id"]
    B --> C["Fix(D) closed (T2)"]
    B --> D["Fix(D) ⊇ S_τ"]
    C --> E["Fix(D) ⊇ cl(S_τ)"]
    D --> E
    E --> F{"Is S_τ clopen?"}
    F -- "no (connected)" --> G["cl(S_τ) ⊋ S_τ"]
    G --> H["∃ z ∈ cl(S_τ) \\ S_τ<br/>f(z) = τ, D(z) = z"]

    classDef a fill:#eef3fb,stroke:#3455db;
    classDef b fill:#fde3e3,stroke:#9c2424;
    class A,B,C,D,E,F,G a;
    class H b;
```

::: remark
The theorem is tight: removing any single hypothesis gives a counter-example.
See [Limitations & counter-examples](/limitations).
:::

## Where it is in the artifact

| Component | Lean file |
|---|---|
| Continuous-case boundary fixation | `MoF_08_DefenseBarriers` · `defense_incompleteness` |
| Discrete-case dilemma | `MoF_12_Discrete` · `discrete_defense_boundary_fixed` |
| Unified meta-theorem | `MoF_14_MetaTheorem` · `regularity_implies_spillover` |

## Next

- [T1 · Boundary Fixation](/theorems/boundary-fixation) — the pointwise version
- [T2 · ε-Robust Constraint](/theorems/eps-robust) — the neighborhood version
- [T3 · Persistent Unsafe Region](/theorems/persistent) — the measure version
- [Meta-theorem](/theorems/meta-theorem) — why all three paths collapse to one
