import ManifoldProofs.MoF_08_DefenseBarriers

-- Step 1
#print axioms MoF.defense_fixes_closure
#check @MoF.defense_fixes_closure

-- Step 2
#print axioms MoF.closure_safe_subset_fixedPoints
#check @MoF.closure_safe_subset_fixedPoints

-- Step 3
#print axioms MoF.safe_region_not_closed
#check @MoF.safe_region_not_closed

-- Step 4
#print axioms MoF.boundary_in_closure_of_safe
#check @MoF.boundary_in_closure_of_safe

-- Step 5
#print axioms MoF.defense_incompleteness
#check @MoF.defense_incompleteness

-- What Step 1 actually uses from Mathlib
#check @isClosed_diagonal
#check @IsClosed.preimage

-- What Step 3 actually uses from Mathlib
#check @isClopen_iff

-- What Step 4 actually uses from Mathlib
#check @closure_minimal
#check @isClosed_le
