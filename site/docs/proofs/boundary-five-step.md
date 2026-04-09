# The Five-Step Boundary Proof

A closer look at the proof of [T1 · Boundary
Fixation](/theorems/boundary-fixation). Each step is a single,
elementary fact; the power comes from composing them in the right
order.

## The shape of the argument

```mermaid
flowchart LR
    classDef step fill:#eef3fb,stroke:#3455db;
    classDef concl fill:#fde3e3,stroke:#9c2424;

    S1["Step 1<br/>Fix(D) is closed"]:::step
    S2["Step 2<br/>S_τ ⊆ Fix(D)"]:::step
    S3["Step 3<br/>cl(S_τ) ⊆ Fix(D)"]:::step
    S4["Step 4<br/>cl(S_τ) ⊋ S_τ"]:::step
    S5["Step 5<br/>pick z ∈ cl(S_τ) \\ S_τ"]:::step
    C["∃ z : f(z)=τ ∧ D(z)=z"]:::concl

    S1 --> S3
    S2 --> S3
    S3 --> S5
    S4 --> S5
    S5 --> C
```

Steps 1–2 are the setup; step 3 is the direct consequence; step 4 is
the topological fact that makes the argument actually produce new
points; step 5 reads off the conclusion.

## Step 1 — Fix(D) is closed

```mermaid
flowchart LR
    A["X Hausdorff<br/>⇒ diagonal Δ ⊂ X×X closed"] --> B["x ↦ (D(x), x)<br/>continuous"]
    B --> C["Fix(D) = preimage of Δ<br/>= { x | D(x) = x }"]
    C --> D["Fix(D) is closed"]
    classDef step fill:#eef3fb,stroke:#3455db;
    class A,B,C,D step;
```

In Lean: `defense_fixes_closure`.

::: details What "Hausdorff" is doing
Hausdorff-ness is exactly the statement that the diagonal is closed.
Without it, the set of fixed points might fail to be closed and the
entire argument collapses. This is why the T1 hypothesis includes T2
(Hausdorff), not merely continuity.
:::

## Step 2 — S_τ is inside Fix(D)

```mermaid
flowchart LR
    A["Utility preservation<br/>D(x) = x for x ∈ S_τ"] --> B["S_τ ⊆ Fix(D)<br/>(pointwise inclusion)"]
    classDef step fill:#eef3fb,stroke:#3455db;
    class A,B step;
```

In Lean: `safe_subset_fixedPoints`. This step is a direct rewrite, not
a topological fact.

## Step 3 — cl(S_τ) is inside Fix(D)

```mermaid
flowchart LR
    A["Fix(D) is closed · Step 1"] --> C["cl(S_τ) ⊆ Fix(D)"]
    B["S_τ ⊆ Fix(D) · Step 2"] --> C
    classDef step fill:#eef3fb,stroke:#3455db;
    class A,B,C step;
```

A closed set that contains a subset $A$ also contains $\mathrm{cl}(A)$.
This is the key lemma: it transfers the identity relation from
the **open** safe region to its topological closure, which contains
genuine boundary points.

In Lean: `closure_safe_subset_fixedPoints`.

## Step 4 — cl(S_τ) strictly contains S_τ

```mermaid
flowchart LR
    A["S_τ is open<br/>(preimage of (−∞, τ))"] --> B["Suppose S_τ were closed.<br/>Then S_τ is clopen."]
    B --> C["X is connected<br/>⇒ only clopen are ∅ and X"]
    C --> D{"S_τ = ∅?"}
    D -- "no, safe point exists" --> E{"S_τ = X?"}
    E -- "no, unsafe point exists" --> F["Contradiction — S_τ not clopen"]
    F --> G["S_τ not closed ⇒ cl(S_τ) ⊋ S_τ"]

    classDef step fill:#eef3fb,stroke:#3455db;
    classDef bad fill:#fff6e0,stroke:#c78a00;
    class A,B,C,D,E,G step;
    class F bad;
```

This is the topological heart of the whole paper: **an open, proper,
non-empty subset of a connected space is not closed**. Without
connectedness the argument can be broken — the trivial counterexample
is two disjoint "islands", safe and unsafe, living in a disconnected
$X$ and the defense can retract one to the other discontinuously.

In Lean: `boundary_in_closure_of_safe`.

## Step 5 — Read off the conclusion

```mermaid
flowchart LR
    A["Pick z ∈ cl(S_τ) \\ S_τ"] --> B["z ∈ cl(S_τ) ⊆ Fix(D)<br/>⇒ D(z) = z · Step 3"]
    A --> C["f is continuous, f(y)&lt;τ on S_τ<br/>⇒ f(z) ≤ τ"]
    A --> D["z ∉ S_τ ⇒ f(z) ≥ τ"]
    C --> E["f(z) = τ"]
    D --> E
    B --> F["z is the fixed boundary point"]
    E --> F

    classDef step fill:#eef3fb,stroke:#3455db;
    classDef concl fill:#fde3e3,stroke:#9c2424;
    class A,B,C,D,E step;
    class F concl;
```

In Lean: `defense_preserves_boundary_value` and
`defense_incompleteness`.

## Why this proof is robust

The same five steps survive every generalization in the paper:

- **Score-preserving relaxation.** Replace "$D(x)=x$" with
  "$f(D(x))=f(x)$" and apply the steps to $h=f\circ D - f$.
- **ε-approximate relaxation.** Apply the steps to the closed super-level
  set $\{h\ge -\varepsilon\}$.
- **Stochastic defense.** Apply the steps to $g=\mathbb{E}[f\circ D]$.
- **Multi-turn.** Run the same five steps at every turn.
- **Pipeline.** Apply the steps to $f\circ P$ where $P$ is the composed
  pipeline.

Every case reuses _this_ five-step skeleton, which is why a single
fact — closure of $\mathrm{Fix}(D)$ together with connectedness — can
power the entire impossibility hierarchy.
