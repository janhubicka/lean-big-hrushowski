import BigHrushovski.HrushovskiEllentuckSupport
import BigHrushovski.HrushovskiEllentuckSplicing
import BigHrushovski.HrushovskiEllentuckThinning

/-!
Independent Track E audit entrypoint. The exact finite-support lemmas below
do not assume the existence of a unique C_F level lift.
-/

#print axioms BigHrushovski.Ellentuck.supportDomain_mono
#print axioms BigHrushovski.Ellentuck.supportDomain_inter
#print axioms BigHrushovski.Ellentuck.supportDomain_univ
#print axioms BigHrushovski.Ellentuck.supportDomain_empty_of_nonempty
#print axioms BigHrushovski.Ellentuck.empty_support_mem
#print axioms BigHrushovski.Ellentuck.singleton_mem_supportDomain
#print axioms BigHrushovski.Ellentuck.supportDomain_subset_iff
#print axioms BigHrushovski.Ellentuck.supportDomain_injective
#print axioms BigHrushovski.Ellentuck.supportDomain_closedUnder

#print axioms BigHrushovski.Ellentuck.splicedCore_closed
#print axioms BigHrushovski.Ellentuck.subset_splicedCore_of_closed
#print axioms BigHrushovski.Ellentuck.prefix_subset_splicedCore
#print axioms BigHrushovski.Ellentuck.closed_subset_splicedCore_subset_X

#print axioms BigHrushovski.Ellentuck.thinningCore_subset_ambient
#print axioms BigHrushovski.Ellentuck.thinningCore_closed
#print axioms BigHrushovski.Ellentuck.thinningCore_disjoint
#print axioms BigHrushovski.Ellentuck.closed_subset_thinningCore
#print axioms BigHrushovski.Ellentuck.thinningCore_rejects_dependency
