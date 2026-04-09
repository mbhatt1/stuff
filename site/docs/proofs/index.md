# End-to-end Proof Map

This is the "one picture" view of how every theorem in the paper feeds
into the final impossibility. Read it top-to-bottom; each box points at
the Lean module that formalizes it.

## The whole theory in one graph

```mermaid
flowchart TB
    classDef data fill:#eef3fb,stroke:#3455db,color:#1d2433;
    classDef core fill:#fff6e0,stroke:#c78a00,color:#1d2433;
    classDef ext fill:#e6f4ea,stroke:#256a3a,color:#1d2433;
    classDef meta fill:#f6f2ff,stroke:#6b2ad1,color:#1d2433;
    classDef concl fill:#fde3e3,stroke:#9c2424,color:#1d2433;

    subgraph Data["Data & assumptions"]
      direction TB
      X["Connected Hausdorff space X"]:::data
      f["Continuous f : X → ℝ<br/>S_τ, U_τ both non-empty"]:::data
      D["Continuous D : X → X<br/>D = id on S_τ"]:::data
      Lip["L-Lipschitz f, K-Lipschitz D"]:::data
      Trans["Transversality G > ℓ(K+1)"]:::data
    end

    subgraph Continuous["Continuous case"]
      direction TB
      T1["T1 · Boundary Fixation<br/>MoF_08_DefenseBarriers"]:::core
      T2["T2 · ε-Robust Constraint<br/>MoF_11_EpsilonRobust"]:::core
      T3["T3 · Persistent Unsafe Region<br/>MoF_11_EpsilonRobust"]:::core
      DD["Defense Dilemma (K*)<br/>MoF_19_OptimalDefense"]:::core
      VB["Volume bounds<br/>MoF_17, MoF_18"]:::core
    end

    subgraph Discrete["Discrete path"]
      direction TB
      DIVT["Discrete IVT<br/>MoF_12_Discrete"]:::ext
      DDil["Discrete Defense Dilemma<br/>MoF_12_Discrete"]:::ext
      DCap["Capacity Pigeonhole<br/>MoF_12_Discrete"]:::ext
    end

    subgraph Bridge["Bridge"]
      Tietze["Tietze / McShane–Whitney<br/>MoF_ContinuousRelaxation"]:::meta
    end

    subgraph Extensions["Extensions"]
      direction TB
      Multi["Multi-Turn Impossibility<br/>MoF_13_MultiTurn"]:::ext
      Stoch["Stochastic Impossibility<br/>MoF_13_MultiTurn"]:::ext
      Pipe["Pipeline Degradation<br/>MoF_15_NonlinearAgents"]:::ext
    end

    subgraph Unify["Unification"]
      Meta["Meta-theorem<br/>regularity ⇒ Fix(D) ⊋ S<br/>MoF_14_MetaTheorem"]:::meta
    end

    Concl["Impossibility of continuous utility-preserving<br/>wrapper defenses on connected spaces"]:::concl

    X --> T1
    f --> T1
    D --> T1
    T1 --> T2
    Lip --> T2
    T2 --> T3
    Trans --> T3
    T3 --> VB
    T3 --> DD

    DIVT --> DDil
    DDil --> DCap

    Tietze --> T1

    T1 --> Multi
    T1 --> Stoch
    T1 --> Pipe

    T1 -.-> Meta
    DDil -.-> Meta
    Stoch -.-> Meta

    Meta --> Concl
    T3 --> Concl
    DCap --> Concl
    Pipe --> Concl
```

Solid arrows are logical implications; dashed arrows are instantiations
of the meta-theorem.

## How to read the Lean artifact against this map

| Lean module | Role in the proof map |
|---|---|
| `MoF_08_DefenseBarriers` | Tier T1 — the five-step closure proof. |
| `MoF_11_EpsilonRobust` | Tiers T2 and T3. |
| `MoF_12_Discrete` | Discrete IVT, non-injectivity dilemma, capacity exhaustion. |
| `MoF_13_MultiTurn` | Multi-turn, stochastic, capacity parity. |
| `MoF_14_MetaTheorem` | The regularity → spillover unification. |
| `MoF_15_NonlinearAgents` | Pipeline composition and band growth. |
| `MoF_16_RelaxedUtility` | Score-preserving and ε-approximate variants. |
| `MoF_17_CoareaBound` | Ball-based coarea volume bound. |
| `MoF_18_ConeBound` | Persistent region cone bound. |
| `MoF_19_OptimalDefense` | The K* defense dilemma. |
| `MoF_21_GradientChain` | `HasFDerivAt` ⇒ steep region non-empty. |
| `MoF_ContinuousRelaxation` | Tietze bridge from finite data to continuous $f$. |
| `MoF_MasterTheorem` | Unified master statement bundling the pieces. |
| `MoF_Instantiation_Euclidean` | Instantiation to $\mathbb{R}^n$. |
| `MoF_FinalVerification` | Cross-file axiom verification. |

## Where each page lives

- [Five-step boundary proof](/proofs/boundary-five-step) — the detailed
  walk-through of T1.
- [Discrete → continuous](/proofs/discrete-to-continuous) — how finite
  data forces the continuous theory.
- [Lean dependency graph](/proofs/lean-dependency-graph) — a zoomed-in
  graph of which Lean files import which.
