# Notation & Glossary

A single-page reference for every symbol and technical term used across the
site.

## Symbols

| Symbol | Meaning |
|---|---|
| $X$ | Prompt space — a topological space; assumed connected + Hausdorff for T1. |
| $d$ | Metric on $X$ when $X$ is a metric space (used from T2 onward). |
| $f$ | Alignment deviation function $X\to\mathbb{R}$, continuous. |
| $\tau$ | Safety threshold. |
| $S_\tau$ | Safe region $\{x : f(x)<\tau\}$ — open. |
| $U_\tau$ | Unsafe region $\{x : f(x)>\tau\}$ — open. |
| $B_\tau$ | Boundary $\{x : f(x)=\tau\}$ — closed. |
| $\mathrm{cl}(A)$ | Topological closure of $A$. |
| $D$ | Defense wrapper $X\to X$, continuous. |
| $\mathrm{Fix}(D)$ | Fixed-point set $\{x : D(x)=x\}$. |
| $L$ | Lipschitz constant of $f$. |
| $K$ | Lipschitz constant of $D$. |
| $\ell$ | Defense-path Lipschitz constant, $\sup_{x\ne D(x)} \frac{|f(D(x))-f(x)|}{d(D(x),x)}$. Always $\ell\le L$. |
| $G$ | Directional slope of $f$ at the fixed boundary point $z$ (Fréchet norm $\lVert f'(z)\rVert$ in a normed space). |
| $\mathcal B_\varepsilon$ | The $\varepsilon$-band $\{x : \tau-\varepsilon\le f(x)\le\tau\}$. |
| $\mathcal S$ | Steep region $\{x : f(x)>\tau+\ell(K+1)\,d(x,z)\}$. |
| $K^\star$ | Dilemma threshold $G/\ell - 1$. |
| $V_n$ | Volume of the unit ball in $\mathbb{R}^n$. |
| $\mu$ | A measure positive on non-empty open sets (Lebesgue in Euclidean cases). |

## Glossary

**Boundary fixation.** The conclusion of tier T1: any continuous
utility-preserving wrapper has at least one fixed point $z$ with
$f(z)=\tau$. See [T1](/theorems/boundary-fixation).

**Completeness.** A defense is complete if every output is strictly safe:
$f(D(x))<\tau$ for all $x$.

**Connected space.** A topological space that cannot be split into two
disjoint non-empty open sets — equivalently, has no non-trivial clopen
subsets. Connectedness is the topological fact that makes tier T1 work.

**Defense trilemma.** The three-way impossibility: continuity, utility
preservation, completeness cannot coexist. See [here](/trilemma).

**Fixed-point set.** $\mathrm{Fix}(D) = \{x : D(x)=x\}$. Closed whenever
$D$ is continuous and $X$ is Hausdorff.

**Hausdorff (T2).** A space where distinct points have disjoint
neighborhoods; equivalently, the diagonal $\{(x,x)\}\subseteq X\times X$
is closed. Needed so that $\mathrm{Fix}(D)$ is closed.

**Lipschitz.** A map $g$ is $K$-Lipschitz if $d(g(x),g(y))\le K\,d(x,y)$
for all $x,y$. Provides the quantitative bounds needed in T2 / T3.

**Meta-theorem.** The representation-independent statement
"regularity $\Rightarrow \mathrm{Fix}(D)\supsetneq S$" that subsumes the
continuous, discrete, and stochastic proofs. See
[Meta-theorem](/theorems/meta-theorem).

**Persistence / persistent unsafe region.** The positive-measure set
$\mathcal S$ on which the defense cannot pull $f$ below $\tau$.

**Score-preserving.** A relaxation of utility preservation: $D$ preserves
$f$ on safe inputs, $f(D(x))=f(x)$ for $x\in S_\tau$. The impossibility
survives this relaxation and its $\varepsilon$-approximate version.

**Steep region.** $\mathcal S = \{x : f(x)>\tau+\ell(K+1)\,d(x,z)\}$
— where the alignment surface rises faster than the defense's
Lipschitz budget can compensate.

**Tietze extension.** Classical theorem: a continuous function on a
closed subset of a normal space extends to the whole space. In our
setting it promotes finitely many observations into a continuous model
on all of $X$, so every model consistent with the data inherits the
impossibility. See [Tietze](/theorems/tietze).

**Transversality.** The condition $G>\ell(K+1)$ at the fixed boundary
point. When it holds, the steep region $\mathcal S$ is non-empty and tier
T3 applies.

**Utility preservation.** $D(x)=x$ for every safe input $x\in S_\tau$.
A weaker "score-preserving" version also yields the impossibility.

**Wrapper defense.** An input-to-input map $D\colon X\to X$ applied
before the model sees the prompt; the object the impossibility theorems
constrain.
