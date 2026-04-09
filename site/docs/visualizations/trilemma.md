# Trilemma Diagram

See [The Defense Trilemma](/trilemma) for the full discussion — this
page is the visualization-only companion.

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

## The failure modes

```mermaid
flowchart LR
    In["Choose your pair"] -->|"Cont + Util"| A["Boundary fixation<br/>(T1 fires)"]
    In -->|"Util + Complete"| B["Discontinuity<br/>(e.g. hard blocklist)"]
    In -->|"Cont + Complete"| C["Utility destruction<br/>(constant map)"]

    classDef bad fill:#fde3e3,stroke:#9c2424;
    classDef note fill:#eef3fb,stroke:#3455db;
    class A bad;
    class B,C note;
```

## As a decision flow for designers

```mermaid
flowchart TB
    Q1{"Do you need a continuous<br/>wrapper?"} -- "no" --> D1["Use a discontinuous filter,<br/>rejection, or adaptive threshold.<br/>Theorem does not apply."]
    Q1 -- "yes" --> Q2{"Do you need to preserve<br/>utility on safe inputs?"}
    Q2 -- "no" --> D2["Use a constant / strongly-regularized map.<br/>You destroy utility."]
    Q2 -- "yes" --> Q3{"Need completeness?"}
    Q3 -- "no" --> D3["Live with boundary fixation;<br/>monitor, don't eliminate.<br/>See Engineering Prescription."]
    Q3 -- "yes" --> D4["Impossible."]

    classDef ok fill:#e6f4ea,stroke:#256a3a;
    classDef warn fill:#fff6e0,stroke:#c78a00;
    classDef bad fill:#fde3e3,stroke:#9c2424;
    class D1,D3 ok;
    class D2 warn;
    class D4 bad;
```

## Corresponding Lean content

- `MoF_08_DefenseBarriers.defense_incompleteness` — formal statement
  of the third edge of the trilemma.
- `MoF_16_RelaxedUtility` — weakened utility-preservation variants.
- `MoF_14_MetaTheorem` — abstract form with "regularity" replacing
  "continuity".
