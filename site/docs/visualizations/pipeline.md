# Pipeline Amplification

How Lipschitz constants multiply through an agent tool-chain, and why
this makes deeper pipelines worse to defend.

See [Pipeline Degradation](/theorems/pipeline) for the formal
statement.

## A five-stage pipeline

```mermaid
flowchart LR
    In["prompt x"] --> D["D<br/>defense<br/>K_D"]
    D --> M["M<br/>model"]
    M --> T1["T₁<br/>search tool<br/>K=2"]
    T1 --> T2["T₂<br/>python tool<br/>K=2"]
    T2 --> T3["T₃<br/>browser tool<br/>K=2"]
    T3 --> T4["T₄<br/>memory tool<br/>K=2"]
    T4 --> Out["output"]

    classDef io fill:#eef3fb,stroke:#3455db;
    classDef defense fill:#e6f4ea,stroke:#256a3a;
    classDef model fill:#fff6e0,stroke:#c78a00;
    classDef tool fill:#f6f2ff,stroke:#6b2ad1;
    class In,Out io;
    class D defense;
    class M model;
    class T1,T2,T3,T4 tool;
```

Effective Lipschitz constant:

$$
K_\mathrm{eff} \;=\; K_D \cdot 1 \cdot 2 \cdot 2 \cdot 2 \cdot 2
\;=\; 16\,K_D
$$

and the ε-robust band width grows in proportion.

## Band width vs. depth

```mermaid
flowchart LR
    d1["1 tool<br/>K_eff = 2"] --> d2["2 tools<br/>K_eff = 4"]
    d2 --> d3["3 tools<br/>K_eff = 8"]
    d3 --> d4["4 tools<br/>K_eff = 16"]
    d4 --> d5["5 tools<br/>K_eff = 32"]
    d5 --> dn["n tools<br/>K_eff = 2ⁿ"]

    classDef cold fill:#e6f4ea,stroke:#256a3a;
    classDef warm fill:#fff6e0,stroke:#c78a00;
    classDef hot fill:#fde3e3,stroke:#9c2424;
    class d1,d2 cold;
    class d3,d4 warm;
    class d5,dn hot;
```

The band width scales linearly in $K_\mathrm{eff}$, so it grows
**exponentially in the number of tools**. A single-stage defense with
a 1-unit band becomes a 32-unit band at depth 5 and a ~1024-unit
band at depth 10.

## Why naive "defense in depth" fails

```mermaid
flowchart TB
    A["Classic security intuition:<br/>stacking filters reduces failure"] --> Q{"Are the filters<br/>independent?"}
    Q -- "yes, conditional rejection" --> OK["Failure probabilities multiply<br/>(each filter fires independently)"]
    Q -- "no, all pass through continuously" --> BAD["Lipschitz constants multiply<br/>⇒ failure region grows"]

    classDef g fill:#e6f4ea,stroke:#256a3a;
    classDef bad fill:#fde3e3,stroke:#9c2424;
    class OK g;
    class BAD bad;
```

The difference between "good" defense in depth and "bad" defense in
depth is whether the stages compose by **rejection** (discontinuous)
or by **continuous pass-through**. The impossibility theorems only
cover the latter.

## How the pipeline breaks the dilemma optimum

Recall the [defense dilemma](/theorems/defense-dilemma): a
single-stage defense must pick $K$ near $K^\star=G/\ell-1$ to balance
the band and the persistent region.

```mermaid
flowchart LR
    Sub["Single-stage optimum<br/>K ≈ K*"] --> Pipe["Replace D with P = T_n ∘ ⋯ ∘ T_1 ∘ D"]
    Pipe --> Eff["Effective K becomes<br/>K_D · K₁ · K₂ · ⋯ · K_n"]
    Eff --> Bad["Optimum moves far above K*<br/>⇒ band explodes<br/>⇒ defense dominated by T2 loss"]

    classDef a fill:#eef3fb,stroke:#3455db;
    classDef bad fill:#fde3e3,stroke:#9c2424;
    class Sub,Pipe,Eff a;
    class Bad bad;
```

Once the pipeline fixes $K_\mathrm{eff}\gg K^\star$, the persistent
unsafe region might become empty, but the $\varepsilon$-robust band
becomes so wide that the defense can no longer push any point far
below $\tau$. The problem just shifts from "unsafe" to "barely safe".

## Related

- [Pipeline Degradation theorem](/theorems/pipeline)
- [Defense dilemma](/theorems/defense-dilemma)
- Lean file: `MoF_15_NonlinearAgents`.
