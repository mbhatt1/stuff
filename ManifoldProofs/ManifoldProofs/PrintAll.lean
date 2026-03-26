import ManifoldProofs.MoF_01_Foundations
import ManifoldProofs.MoF_02_BasinStructure
import ManifoldProofs.MoF_03_ThresholdCrossing
import ManifoldProofs.MoF_04_LipschitzBasin
import ManifoldProofs.MoF_05_MonotoneConvergence
import ManifoldProofs.MoF_06_Transferability
import ManifoldProofs.MoF_07_AuthorityMonotonicity
import ManifoldProofs.MoF_08_DefenseBarriers
import ManifoldProofs.MoF_09_DimensionalScaling
import ManifoldProofs.MoF_10_GradientAttack

-- MoF 01
#print axioms MoF.safeRegion_isOpen
#print axioms MoF.unsafeRegion_isOpen
#print axioms MoF.boundary_isClosed
#print axioms MoF.space_partition
#print axioms MoF.safe_unsafe_disjoint
#print axioms MoF.failureManifold_isClosed
#print axioms MoF.unsafe_subset_failure
#print axioms MoF.boundary_subset_failure

-- MoF 02
#print axioms MoF.basin_isOpen
#print axioms MoF.basin_nonempty
#print axioms MoF.basin_measure_pos

-- MoF 03
#print axioms MoF.path_crosses_threshold
#print axioms MoF.threshold_level_set_nonempty
#print axioms MoF.no_gap_theorem

-- MoF 04
#print axioms MoF.lipschitz_basin_ball
#print axioms MoF.robustnessRadius_pos
#print axioms MoF.basin_ball_subset
#print axioms MoF.robustnessRadius_monotone

-- MoF 05
#print axioms MoF.attackSeq_monotone
#print axioms MoF.attackSeq_convergent
#print axioms MoF.finite_steps_bound

-- MoF 06
#print axioms MoF.transfer_attack
#print axioms MoF.basin_containment
#print axioms MoF.identical_models_identical_basins

-- MoF 07
#print axioms MoF.authority_escalation
#print axioms MoF.critical_threshold_exists
#print axioms MoF.monotone_boundary

-- MoF 08
#print axioms MoF.defense_incompleteness

-- MoF 09
#print axioms MoF.grid_card
#print axioms MoF.coverage_fraction_vanishes
#print axioms MoF.no_fixed_budget_defense

-- MoF 10
#print axioms MoF.ascent_direction_exists
