# Visualization Gallery

A single-page index of every mermaid diagram and theorem illustration
used across the site, in one place, for reference.

## Contents

- [Three-tier escalation](/visualizations/escalation) — the main picture
  of T1 → T2 → T3.
- [Trilemma diagram](/visualizations/trilemma) — the three-property
  triangle.
- [Pipeline amplification](/visualizations/pipeline) — how Lipschitz
  constants multiply through an agent tool-chain.
- [Steep region and cone bound](/visualizations/steep-region) — the
  geometric picture behind T3.

## A meta-view of the whole story

```mermaid
flowchart TB
    classDef data fill:#eef3fb,stroke:#3455db;
    classDef core fill:#fff6e0,stroke:#c78a00;
    classDef ext fill:#e6f4ea,stroke:#256a3a;
    classDef concl fill:#fde3e3,stroke:#9c2424;

    Data["Finite observations or a model"]:::data

    subgraph Tiers["Impossibility tiers"]
      direction LR
      T1["T1 · Boundary Fixation"]:::core
      T2["T2 · ε-Robust"]:::core
      T3["T3 · Persistent Region"]:::core
      T1 --> T2 --> T3
    end

    subgraph Escapes["Escapes that fail"]
      direction TB
      Disc["Discrete set<br/>no topology?"]:::ext
      Stoch["Randomize D?"]:::ext
      Multi["Add memory / multi-turn?"]:::ext
      Pipe["Chain tool calls?"]:::ext
    end

    Out["No continuous utility-preserving<br/>wrapper is complete"]:::concl

    Data --> T1
    Data --> Disc
    Disc --> Out
    Stoch --> Out
    Multi --> Out
    Pipe --> Out
    T3 --> Out
```

## About these diagrams

All diagrams are rendered with [Mermaid](https://mermaid.js.org/) via
[vitepress-plugin-mermaid](https://github.com/emersonbottero/vitepress-plugin-mermaid).
They are regenerated on each build, so any edit to a `.md` file
propagates immediately — there is no separate asset step.
