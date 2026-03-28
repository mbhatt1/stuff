# Geometric Limits of Defense Design: Impossibility Theorems for Prompt Injection Defenses

This repository contains the paper and machine-verified Lean 4 proofs for the defense impossibility theorems described in *Geometric Limits of Defense Design*.

## Main result

Any defense that preserves utility on safe inputs and has bounded regularity (continuity, finite capacity, or any mechanism preventing the fixed-point set from exactly equaling the safe region) must leave non-safe inputs unremediated. This holds across continuous spaces, discrete token spaces, stochastic defenses, multi-turn interactions, and nonlinear agent pipelines.

## Repository structure

```
├── paper2_defense_impossibility.tex   Paper source (16 pages)
├── paper2_defense_impossibility.pdf   Compiled paper
└── ManifoldProofs/                    Lean 4 artifact
    ├── lakefile.toml                  Lean 4.28.0 + Mathlib v4.28.0
    ├── ManifoldProofs.lean            Imports all 39 files
    └── ManifoldProofs/                Source files
```

## The three-tier impossibility

| Tier | Theorem | Assumption | Conclusion |
|------|---------|------------|------------|
| 1 | Boundary Fixation | Continuous + utility-preserving + connected | Defense must fix boundary points (f(z) = τ) |
| 2 | ε-Robust Constraint | + Lipschitz | Defense can't push near-boundary band far below τ |
| 3 | Persistent Unsafe Region | + Transversality | Positive-measure region stays genuinely unsafe |

Plus: discrete impossibility (no topology), multi-turn (recurs every turn), stochastic (randomization fails in expectation), capacity parity (utility preservation taxes the defense), nonlinear pipelines (Lipschitz constants multiply through tool calls), and a representation-independent meta-theorem unifying all paths.

## Verification

```bash
cd ManifoldProofs
lake build    # builds all 39 files, zero errors
```

- **39 Lean files**, ~300 theorems
- **Zero `sorry`** statements
- **Zero custom axioms** (only Lean's standard: `propext`, `Classical.choice`, `Quot.sound`)
- Full `lake build` succeeds

## Key files

| File | What it proves |
|------|---------------|
| `MoF_08_DefenseBarriers` | Tier 1: boundary fixation (the core 5-step proof) |
| `MoF_11_EpsilonRobust` | Tiers 2–3: ε-robust band + persistent unsafe region |
| `MoF_12_Discrete` | Discrete IVT + capacity exhaustion (no topology) |
| `MoF_13_MultiTurn` | Multi-turn, stochastic, capacity parity, attacker steering |
| `MoF_14_MetaTheorem` | Regularity implies spillover (representation-independent) |
| `MoF_15_NonlinearAgents` | Pipeline degradation: K^n exponential in tool-call depth |
| `MoF_ContinuousRelaxation` | Tietze bridge: discrete data → continuous theory |

## Citation

```bibtex
@article{bhatt2026geometric,
  title={Geometric Limits of Defense Design: Impossibility Theorems for Prompt Injection Defenses},
  author={Bhatt, Manish and Munshi, Sarthak and Narajala, Vineeth Sai and Habler, Idan and Al-Kahfah, Ammar and Huang, Ken and Gatto, Blake},
  year={2026}
}
```

## License

The Lean artifact and paper are open-sourced for the research community.
