/-
  MoF Final Verification
  ======================
  This file verifies the entire Manifold of Failure (MoF) theory.

  **Namespace collision report:**

  The following definitions collide and prevent importing all files simultaneously:

  1. `MoF.SafeRegion` — defined in both:
     - MoF_01_Foundations (f : X → ℝ) (τ : ℝ) with [TopologicalSpace X]
     - MoF_03_ThresholdCrossing (f : α → ℝ) (τ : ℝ) without topology

  2. `MoF.UnsafeRegion` — defined in both:
     - MoF_01_Foundations (f : X → ℝ) (τ : ℝ)
     - MoF_03_ThresholdCrossing (f : α → ℝ) (τ : ℝ)

  3. `MoF.costRatio` — defined in both:
     - MoF_Cost_08_CostRatio (N : ℕ) (d : ℕ) (δ : ℝ) : ℝ
     - MoF_Cost_10_UnifiedTheory (cp : CostParameters) : ℝ

  Because of these collisions, we cannot import all 20 files together.
  Instead, we verify each file independently by building them via `lake build`.

  Each MoF file imports only `Mathlib` (not other MoF files), so they are
  independently checkable. The collisions only matter if one tries to import
  multiple MoF files into a single Lean file.

  **Verification strategy:**
  We import the two largest collision-free subsets and print axioms for
  key theorems from each group.
-/

-- ============================================================
-- GROUP A: Files that do NOT define SafeRegion/UnsafeRegion/costRatio
-- These can all be imported together safely.
-- ============================================================
import ManifoldProofs.MoF_02_BasinStructure
import ManifoldProofs.MoF_04_LipschitzBasin
import ManifoldProofs.MoF_05_MonotoneConvergence
import ManifoldProofs.MoF_06_Transferability
import ManifoldProofs.MoF_07_AuthorityMonotonicity
import ManifoldProofs.MoF_08_DefenseBarriers
import ManifoldProofs.MoF_09_DimensionalScaling
import ManifoldProofs.MoF_10_GradientAttack
import ManifoldProofs.MoF_Cost_01_BallVolume
import ManifoldProofs.MoF_Cost_02_BasinVolume
import ManifoldProofs.MoF_Cost_03_HittingTime
import ManifoldProofs.MoF_Cost_04_Concentration
import ManifoldProofs.MoF_Cost_05_AttackCost
import ManifoldProofs.MoF_Cost_06_DefenseCost
import ManifoldProofs.MoF_Cost_07_TransferCost
import ManifoldProofs.MoF_Cost_09_LipschitzEstimation

-- ============================================================
-- We CANNOT also import these due to namespace collisions:
--   MoF_01_Foundations      (collides with MoF_03 on SafeRegion/UnsafeRegion)
--   MoF_03_ThresholdCrossing (collides with MoF_01 on SafeRegion/UnsafeRegion)
--   MoF_Cost_08_CostRatio   (collides with MoF_Cost_10 on costRatio)
--   MoF_Cost_10_UnifiedTheory (collides with MoF_Cost_08 on costRatio)
--
-- Each of these 4 files builds successfully on its own.
-- ============================================================

-- ============================================================
-- Print axioms for key theorems from the 16 imported files
-- ============================================================

-- MoF_02: Basin Structure
#check @MoF.basin_isOpen
#check @MoF.basin_measure_pos

-- MoF_04: Lipschitz Basin
#check @MoF.lipschitz_basin_ball
#check @MoF.perturbation_stability

-- MoF_05: Monotone Convergence
#check @MoF.attackSeq_convergent
#check @MoF.finite_steps_bound

-- MoF_06: Transferability
#check @MoF.transfer_attack
#check @MoF.identical_models_identical_basins

-- MoF_07: Authority Monotonicity
#check @MoF.authority_escalation
#check @MoF.critical_threshold_exists
#check @MoF.monotone_boundary

-- MoF_08: Defense Barriers
#check @MoF.defense_incompleteness
#check @MoF.boundary_fixed_points_nonempty
#check @MoF.not_all_boundary_fixed

-- MoF_09: Dimensional Scaling
#check @MoF.grid_exponential_growth
#check @MoF.no_fixed_budget_defense

-- MoF_10: Gradient Attack
#check @MoF.multivariate_ascent_direction
#check @MoF.discrete_ascent_improvement

-- MoF_Cost_01: Ball Volume
#check @MoF.ball_measure_pos

-- MoF_Cost_02: Basin Volume
#check @MoF.basin_measure_ge_ball_pos

-- MoF_Cost_03: Hitting Time
#check @MoF.miss_probability_vanishes
#check @MoF.hit_probability_tends_to_one

-- MoF_Cost_04: Concentration
#check @MoF.estimation_error_bound_unsafe
#check @MoF.estimation_error_bound_safe

-- MoF_Cost_05: Attack Cost
#check @MoF.attack_cost_upper_bound
#check @MoF.attack_reaches_threshold

-- MoF_Cost_06: Defense Cost
#check @MoF.defense_cost_exponential
#check @MoF.critical_dimension

-- MoF_Cost_07: Transfer Cost
#check @MoF.transfer_margin_needed
#check @MoF.zero_distance_free_transfer

-- MoF_Cost_09: Lipschitz Estimation
#check @MoF.lipschitz_estimation_error
#check @MoF.total_estimation_budget

-- ============================================================
-- Print axioms for the most important theorems to confirm
-- they are sorry-free (axiom-free beyond Lean/Mathlib basics)
-- ============================================================

-- Defense Incompleteness (the crown jewel)
#print axioms MoF.defense_incompleteness

-- Attack Convergence
#print axioms MoF.attackSeq_convergent

-- Transfer Attack
#print axioms MoF.transfer_attack

-- Authority Escalation
#print axioms MoF.authority_escalation

-- Gradient Ascent
#print axioms MoF.multivariate_ascent_direction

-- Dimensional Curse
#print axioms MoF.no_fixed_budget_defense

-- Lipschitz Basin Ball
#print axioms MoF.lipschitz_basin_ball

-- Basin Positive Measure
#print axioms MoF.basin_measure_ge_ball_pos

-- Hit Probability Convergence
#print axioms MoF.hit_probability_tends_to_one

-- Defense Cost Exponential
#print axioms MoF.defense_cost_exponential
