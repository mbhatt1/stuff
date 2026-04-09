# Steep Region and Cone Bound

The geometric picture behind [Tier T3 — Persistent Unsafe
Region](/theorems/persistent). The steep region is where the
alignment surface outruns the defense's Lipschitz budget.

## The defense budget cone

Fix the boundary point $z$ and draw a cone of slope $\ell(K+1)$
rooted at $(z,\tau)$.

```mermaid
flowchart LR
    subgraph Profile["1D profile of f, near z"]
        direction LR
        Safe["f &lt; τ (safe)"] --- Z["z : f(z)=τ, D(z)=z"] --- Cone["cone<br/>τ + ℓ(K+1)·d(x,z)"] --- Curve["actual f(x) rising<br/>with slope G &gt; ℓ(K+1)"]
    end
    Curve -.-> S["Steep region S<br/>(between cone and curve)"]

    classDef safe fill:#e6f4ea,stroke:#256a3a;
    classDef bound fill:#fff6e0,stroke:#c78a00;
    classDef steep fill:#fde3e3,stroke:#9c2424;
    classDef note fill:#eef3fb,stroke:#3455db;
    class Safe safe;
    class Z note;
    class Cone bound;
    class Curve note;
    class S steep;
```

- The cone marks the **maximum** reduction the defense can achieve at
  distance $d(x,z)$ from $z$.
- The actual alignment surface $f(x)$ rises with directional slope $G$
  at $z$.
- Wherever $G>\ell(K+1)$, the curve punches **through** the cone into
  the steep region — and inside that region the defense cannot bring
  $f(D(x))$ below $\tau$.

## When the steep region is non-empty

```mermaid
flowchart TB
    A["Frechet derivative f'(z) exists"] --> B{"‖f'(z)‖ &gt; ℓ(K+1) ?"}
    B -- "no (isotropic)" --> C["Steep region empty<br/>(paper remark — T3 vacuous)"]
    B -- "yes (anisotropic)" --> D["∃ unit vector v with<br/>f'(z)·v &gt; ℓ(K+1)"]
    D --> E["z + tv ∈ S for small t &gt; 0"]
    E --> F["S is open, non-empty,<br/>positive measure"]

    classDef a fill:#eef3fb,stroke:#3455db;
    classDef b fill:#e6f4ea,stroke:#256a3a;
    classDef c fill:#fde3e3,stroke:#9c2424;
    class A,B a;
    class C,D,E b;
    class F c;
```

This is exactly
`gradient_norm_implies_steep_nonempty` in `MoF_21_GradientChain`.

## The cone bound in action

The cone bound (`MoF_18_ConeBound`) gives an **explicit**
lower bound on the persistent region when $f$ is linear in a
neighborhood of $z$:

```mermaid
flowchart LR
    A["f(x) ≥ τ + c·(x−z)<br/>on (z, z+δ₀)"] --> B["c &gt; ℓ(K+1)"]
    B --> C["∀ x ∈ (z, z+δ₀):<br/>f(x) above the cone"]
    C --> D["x ∈ S, f(D(x)) &gt; τ"]
    D --> E["μ{ f(D) &gt; τ } ≥ δ₀"]

    classDef a fill:#eef3fb,stroke:#3455db;
    classDef b fill:#fff6e0,stroke:#c78a00;
    classDef c fill:#fde3e3,stroke:#9c2424;
    class A,B a;
    class C,D b;
    class E c;
```

The bound is tight: $\ge\delta_0$, with equality when the cone
condition fails exactly at the endpoint.

## Relation to isotropy

```mermaid
flowchart LR
    Iso["Isotropic surface<br/>ℓ = L"] -->|"⇒ K* ≤ 0"| Vac["Steep region empty<br/>for all K ≥ 0"]
    Aniso["Anisotropic surface<br/>ℓ &lt; L"] -->|"⇒ K* &gt; 0"| Sharp["Dilemma sharp"]

    classDef a fill:#eef3fb,stroke:#3455db;
    classDef b fill:#fff6e0,stroke:#c78a00;
    class Iso,Aniso a;
    class Vac,Sharp b;
```

In isotropic settings tier T3 is vacuous and the defense only has to
worry about the $\varepsilon$-band. In anisotropic settings —
empirically observed in the two LLMs with non-empty unsafe region in
the paper's experiments — the steep region is where the impossibility
has teeth.

## Related

- [Persistent Unsafe Region](/theorems/persistent) — the full theorem.
- [Defense dilemma (K*)](/theorems/defense-dilemma) — the designer's
  trade-off.
- [Volume bounds](/theorems/volume-bounds) — the coarea and cone
  bounds.
