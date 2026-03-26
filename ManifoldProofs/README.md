# Manifold of Failure — Lean 4 Formalization

Machine-verified proofs for the defense impossibility theorem and supporting theory from *Manifold Defense Trilemma: Impossibility of Continuous Prompt Injection Defense*.

## Structure

| Directory | Files | Content |
|-----------|-------|---------|
| `MoF_01`–`MoF_10` | 10 | Core theory: foundations, basins, threshold crossing, Lipschitz robustness, convergence, transferability, authority monotonicity, defense barriers, dimensional scaling, gradient attack |
| `MoF_Cost_01`–`MoF_Cost_10` | 10 | Cost theory: ball volume, basin volume, hitting time, concentration, attack cost, defense cost, transfer cost, cost ratio, Lipschitz estimation, unified theory |
| `MoF_Adv_01`–`MoF_Adv_10` | 10 | Advanced: basin connectedness, boundary dimension, fine-tuning, model scale, convexity, approximation, fragmentation, stability, optimization landscape, measure bounds |
| `MoF_ContinuousRelaxation` | 1 | Tietze extension bridge: discrete behavioral data → continuous theory |
| `MoF_MasterTheorem` | 1 | Unified master theorem |
| `MoF_Instantiation_Euclidean` | 1 | Concrete instantiation to R^n |
| `MoF_FinalVerification` | 1 | Cross-file verification |

## Key results

- **Defense Impossibility** (`MoF_08`): No continuous utility-preserving defense can clear the safety boundary
- **Continuous Relaxation** (`MoF_ContinuousRelaxation`): Finite discrete data always admits a continuous interpolant via Tietze extension, so the impossibility applies to real LLM behavioral data
- **Cost Asymmetry** (`MoF_Cost_10`): Defense cost grows as N^d; attack cost is dimension-independent

## Verification

- Lean 4.28.0 + Mathlib v4.28.0
- Zero `sorry` statements
- Three standard axioms: `propext`, `Classical.choice`, `Quot.sound`

## Build

```bash
lake build
```
