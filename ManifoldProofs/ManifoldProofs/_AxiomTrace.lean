import ManifoldProofs.MoF_08_DefenseBarriers

-- The 5 steps
#print axioms MoF.defense_fixes_closure
#print axioms MoF.closure_safe_subset_fixedPoints
#print axioms MoF.safe_region_not_closed
#print axioms MoF.boundary_in_closure_of_safe
#print axioms MoF.defense_incompleteness

-- What do THOSE depend on in Mathlib?
#print axioms isClosed_diagonal
#print axioms IsClosed.preimage
#print axioms IsClosed.closure_subset_iff
#print axioms isClopen_iff
#print axioms closure_minimal
#print axioms isClosed_le
