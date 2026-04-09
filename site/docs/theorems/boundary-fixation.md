# T1 · Boundary Fixation

<span class="tier-pill t1">Tier 1</span>
Paper Theorem 4.1 · Lean module `MoF_08_DefenseBarriers`

The most fundamental result in the paper: any continuous
utility-preserving wrapper must fix at least one boundary point.

## Statement

::: theorem
Let $X$ be a connected Hausdorff space. Let $f\colon X\to\mathbb{R}$ be
continuous with $S_\tau,U_\tau\ne\emptyset$, and let $D\colon X\to X$ be
continuous with $D|_{S_\tau}=\mathrm{id}$. Then

$$
\exists\, z\in X\ \text{ with }\ f(z)=\tau\ \text{ and }\ D(z)=z.
$$

Moreover every $z\in \mathrm{cl}(S_\tau)\setminus S_\tau$ satisfies
$f(z)=\tau$ and $D(z)=z$, and this set is non-empty.
:::

## The five-step proof

```mermaid
flowchart TB
    S1["Step 1 — Fix(D) is closed<br/><span style='font-size:11px'>X Hausdorff + D continuous<br/>⇒ diagonal preimage closed</span>"]
    S2["Step 2 — S_τ ⊆ Fix(D)<br/><span style='font-size:11px'>utility preservation<br/>D(x)=x on S_τ</span>"]
    S3["Step 3 — cl(S_τ) ⊆ Fix(D)<br/><span style='font-size:11px'>closed set contains the<br/>closure of any subset</span>"]
    S4["Step 4 — cl(S_τ) ⊋ S_τ<br/><span style='font-size:11px'>S_τ is open but not clopen<br/>(connected + proper non-empty)</span>"]
    S5["Step 5 — pick z ∈ cl(S_τ) \\ S_τ<br/><span style='font-size:11px'>f(z)=τ (limit argument)<br/>D(z)=z (from Step 3)</span>"]

    S1 --> S3
    S2 --> S3
    S3 --> S5
    S4 --> S5

    classDef step fill:#eef3fb,stroke:#3455db,color:#1d2433;
    class S1,S2,S3,S4,S5 step;
```

::: details Step-by-step narrative
1. **Fix(D) is closed.** In a Hausdorff space the diagonal
   $\Delta=\{(x,x)\}\subset X\times X$ is closed. The map
   $x\mapsto(D(x),x)$ is continuous, so its preimage of $\Delta$ — which
   is exactly $\mathrm{Fix}(D)$ — is closed.
2. **Safe set is inside Fix(D).** Utility preservation literally says
   $D(x)=x$ for $x\in S_\tau$, i.e. $S_\tau\subseteq\mathrm{Fix}(D)$.
3. **Closure of safe set is inside Fix(D).** A closed set that contains
   a subset $A$ also contains $\mathrm{cl}(A)$. Combining steps 1 and 2
   gives $\mathrm{cl}(S_\tau)\subseteq\mathrm{Fix}(D)$.
4. **$S_\tau$ is not closed.** $S_\tau$ is a non-empty proper open
   subset of the connected space $X$ (because $U_\tau\ne\emptyset$, so
   $S_\tau\ne X$). Connectedness forbids non-trivial clopen subsets,
   so $S_\tau$ cannot equal its own closure. Hence
   $\mathrm{cl}(S_\tau)\setminus S_\tau\ne\emptyset$.
5. **The boundary point is fixed.** Pick any
   $z\in\mathrm{cl}(S_\tau)\setminus S_\tau$. By continuity
   $f(z)\le\tau$ (limit of values $<\tau$). Since $z\notin S_\tau$ we
   also have $f(z)\ge\tau$. Hence $f(z)=\tau$. And from step 3,
   $D(z)=z$.
:::

## The geometric picture

```mermaid
flowchart LR
    subgraph "X (connected)"
      S["S_τ · open<br/>f &lt; τ<br/>✓ fixed by D"]
      B["∂S_τ ⊆ B_τ<br/>f = τ<br/>✓ fixed by D ⟵ Step 3"]
      U["U_τ · open<br/>f &gt; τ<br/>? unremediated"]
    end

    classDef safe fill:#e6f4ea,stroke:#256a3a;
    classDef bound fill:#fff6e0,stroke:#c78a00;
    classDef unsafe fill:#fde3e3,stroke:#9c2424;
    class S safe;
    class B bound;
    class U unsafe;

    S --- B
    B --- U
```

Utility preservation forces $D$ to be the identity on the green region;
continuity + closure of the fixed-point set forces $D$ to be the identity
on the yellow boundary. This is the single point (at least) at which
the defense passes a non-safe prompt through **without remediation**.

## Relaxing utility preservation

Strict identity on $S_\tau$ is **not** necessary for the impossibility.

::: theorem
**Score-preserving defense.** If $f(D(x))=f(x)$ for every $x\in S_\tau$,
then $\exists z$ with $f(z)=\tau$ and $f(D(z))=\tau$.
:::

::: theorem
**$\varepsilon$-approximate preservation.** If
$|f(D(x))-f(x)|\le\varepsilon$ on $S_\tau$, then
$\exists z$ with $f(z)=\tau$ and $f(D(z))\ge\tau-\varepsilon$.
:::

Both follow from the same closure argument applied to the continuous map
$h=f\circ D-f$: the level set $\{h\ge -\varepsilon\}$ is closed and
contains $S_\tau$, hence $\mathrm{cl}(S_\tau)$. See the paper Thms 4.3–4.4
and Lean `MoF_16_RelaxedUtility`.

## In Lean

The Lean formalization splits the five-step proof into the following
theorems inside `MoF_08_DefenseBarriers`:

```lean
-- Step 1 · Fix(D) is closed in a T2 space
theorem defense_fixes_closure
    [TopologicalSpace X] [T2Space X]
    {D : X → X} (hD : Continuous D) :
    IsClosed {x : X | D x = x}

-- Steps 2–3 · closure of the safe set is fixed
theorem closure_safe_subset_fixedPoints
    (hD : Continuous D)
    (h_safe : ∀ x, f x < τ → D x = x) :
    closure {x : X | f x < τ} ⊆ {x : X | D x = x}

-- Steps 4–5 · the capstone
theorem defense_incompleteness
    [T2Space X] [ConnectedSpace X]
    (hf : Continuous f) (hD : Continuous D)
    (h_safe : ∀ x, f x < τ → D x = x)
    (h_nonempty_safe : ∃ x, f x < τ)
    (h_nonempty_unsafe : ∃ x, τ < f x) :
    ∃ z, f z = τ ∧ D z = z
```

The full `MoF_08_DefenseBarriers` file contains eight theorems assembling
the proof, with **zero `sorry`** and only Lean's three standard axioms.

## Where it goes next

- Upgrade to a **Lipschitz-constrained neighborhood** — [T2 ·
  ε-Robust](/theorems/eps-robust).
- Upgrade to a **positive-measure unsafe region** under transversality —
  [T3 · Persistent](/theorems/persistent).
- Abstract the same argument to the **meta-theorem** that also covers
  the discrete and stochastic cases — [here](/theorems/meta-theorem).
