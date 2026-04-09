# Three-Tier Escalation

Each tier adds one hypothesis and one stronger conclusion. The
picture below is the single diagram to remember for the whole paper.

## The tiers side-by-side

```mermaid
flowchart TB
    classDef t1 fill:#e6f4ea,stroke:#256a3a,color:#1d2433;
    classDef t2 fill:#fff6e0,stroke:#c78a00,color:#1d2433;
    classDef t3 fill:#fde3e3,stroke:#9c2424,color:#1d2433;
    classDef hyp fill:#eef3fb,stroke:#3455db,color:#1d2433;

    H1["connected + Hausdorff"]:::hyp --> T1["T1 · Boundary Fixation<br/>∃ z : f(z)=τ, D(z)=z"]:::t1
    H2["+ L-Lipschitz f, K-Lipschitz D"]:::hyp --> T2["T2 · ε-Robust<br/>f(D(x)) ≥ τ − LK · d(x,z)"]:::t2
    T1 --> T2
    H3["+ transversality G > ℓ(K+1)"]:::hyp --> T3["T3 · Persistent Unsafe Region<br/>μ(S) &gt; 0 and f(D(x)) &gt; τ on S"]:::t3
    T2 --> T3
```

## What the three tiers look like on a 1D cross-section

```mermaid
flowchart LR
    subgraph panel1["(a) T1 — pointwise"]
      direction LR
      S1["safe: f &lt; τ"] --- z1["z : f(z)=τ<br/>D(z)=z"] --- U1["unsafe: f &gt; τ"]
    end
    subgraph panel2["(b) T2 — ε-band"]
      direction LR
      S2["safe"] --- band2["[τ − ε, τ]<br/>radius ε/(4L)"] --- U2["unsafe"]
    end
    subgraph panel3["(c) T3 — persistent region"]
      direction LR
      S3["safe"] --- cone["defense cone<br/>slope ℓ(K+1)"] --- region["region S<br/>above the cone,<br/>f(D(x)) &gt; τ"]
    end

    classDef safe fill:#e6f4ea,stroke:#256a3a;
    classDef band fill:#fff6e0,stroke:#c78a00;
    classDef z fill:#eef3fb,stroke:#3455db;
    classDef unsafe fill:#fde3e3,stroke:#9c2424;
    class S1,S2,S3 safe;
    class z1 z;
    class band2,cone band;
    class U1,U2,region unsafe;
```

## The tier-by-tier comparison

| Tier | Assumption added | Strength of conclusion | Lean file |
|---|---|---|---|
| [T1](/theorems/boundary-fixation) | — | one boundary fixed point | `MoF_08` |
| [T2](/theorems/eps-robust) | Lipschitz $(L,K)$ | neighborhood of slack | `MoF_11` |
| [T3](/theorems/persistent) | transversality $G>\ell(K+1)$ | positive-measure unsafe region | `MoF_11` |

## Tier escalation as a dependency graph

```mermaid
flowchart LR
    BF["Boundary Fixation<br/>(closure of S_τ)"] --> LIP["Lipschitz control<br/>|f(D(x)) − τ| ≤ LK d(x,z)"]
    LIP --> CONE["Defense budget cone<br/>τ + ℓ(K+1) d(x,z)"]
    CONE --> STEEP["Steep region S"]
    STEEP --> POS["Positive-measure<br/>unsafe set"]

    classDef step fill:#eef3fb,stroke:#3455db;
    class BF,LIP,CONE,STEEP,POS step;
```

This is the actual logical order the Lean proofs follow, inside
`MoF_11_EpsilonRobust`:

1. From [T1](/theorems/boundary-fixation): $D(z)=z$ and $f(z)=\tau$.
2. From the triangle inequality: $d(D(x),z)\le K\,d(x,z)$.
3. Apply $L$-Lipschitz of $f$: $|f(D(x))-\tau|\le LK\,d(x,z)$.
4. Bound $f$'s growth along the defense's motion by $\ell$.
5. Define the steep region as the set where $f$ exceeds the budget
   cone; show it is open and, under transversality, non-empty.

## Next

- [Boundary Fixation](/theorems/boundary-fixation) for T1.
- [ε-Robust Constraint](/theorems/eps-robust) for T2.
- [Persistent Unsafe Region](/theorems/persistent) for T3.
