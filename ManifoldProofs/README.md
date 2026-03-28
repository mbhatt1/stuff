# Manifold of Failure — Lean 4 Formalization

Machine-verified proofs for *Geometric Limits of Defense Design: Impossibility Theorems for Prompt Injection Defenses*.

## Quick start

```bash
# Requires Lean 4.28.0 + Mathlib v4.28.0 (via elan/lake)
lake build
```

The full build imports all 39 files simultaneously with zero errors.

## Structure (39 files)

| Files | Count | Content |
|-------|-------|---------|
| `MoF_01`–`MoF_10` | 10 | Core theory: foundations, basins, threshold crossing, Lipschitz robustness, convergence, transferability, authority monotonicity, defense barriers, dimensional scaling, gradient attack |
| `MoF_Cost_01`–`MoF_Cost_10` | 10 | Cost theory: ball volume, basin volume, hitting time, concentration, attack/defense cost, transfer cost, cost ratio, Lipschitz estimation, unified cost asymmetry |
| `MoF_Adv_01`–`MoF_Adv_10` | 10 | Advanced: basin connectedness, boundary dimension, fine-tuning stability, model scale, convexity, approximation, fragmentation, perturbation stability, optimization landscape, measure bounds |
| `MoF_ContinuousRelaxation` | 1 | Tietze extension bridge: discrete data → continuous theory |
| `MoF_11_EpsilonRobust` | 1 | ε-robust constraint + persistent unsafe region under transversality |
| `MoF_12_Discrete` | 1 | Discrete impossibility: IVT, defense fixation, capacity exhaustion (no topology needed) |
| `MoF_13_MultiTurn` | 1 | Multi-turn impossibility, stochastic defense, capacity parity, attacker steering |
| `MoF_14_MetaTheorem` | 1 | Representation-independent meta-theorem: regularity implies spillover |
| `MoF_15_NonlinearAgents` | 1 | Nonlinear agent pipelines: Lipschitz constants multiply, deeper = worse |
| `MoF_MasterTheorem` | 1 | Unified master theorem |
| `MoF_Instantiation_Euclidean` | 1 | Instantiation to ℝⁿ |
| `MoF_FinalVerification` | 1 | Cross-file axiom verification |

## Key results

| Theorem | File | Says |
|---------|------|------|
| **Boundary Fixation** | `MoF_08` | Continuous utility-preserving defense must fix boundary points |
| **ε-Robust Constraint** | `MoF_11` | Defense can't push near-boundary band far below τ |
| **Persistent Unsafe Region** | `MoF_11` | Under transversality, positive-measure region stays genuinely unsafe |
| **Discrete Impossibility** | `MoF_12` | Boundary crossings + capacity exhaustion on finite sets, no topology |
| **Multi-Turn** | `MoF_13` | Impossibility recurs every turn; stochastic defenses fail in expectation |
| **Meta-Theorem** | `MoF_14` | Utility preservation + bounded regularity → Fix(D) ⊋ S (representation-independent) |
| **Pipeline Degradation** | `MoF_15` | Each tool call multiplicatively degrades defense; K^n exponential in depth |
| **Cost Asymmetry** | `MoF_Cost_10` | Defense cost N^d (exponential); attack cost 1/δ (dimension-free) |

## Verification

- **Lean 4.28.0** + **Mathlib v4.28.0**
- **Zero `sorry`** statements
- **Zero custom axioms** — only Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Full `lake build` succeeds with zero errors
