import BigHrushovski.HrushovskiEllentuckActualSupportedSpace

/-!
Track E direct library integration audit. The Ramsey-space axioms
and Tychonoff approximation-code closedness are instantiated on
actual complete C_F finite supports, reusing the pinned abstract
library rather than duplicating its proof.

These endpoints are synthetic support-domain endpoints. The
actual R/H copy-domain equivalence remains separately gated.
-/

#print axioms BigHrushovski.CFCoherentTower.supportedSingletonWitness_spec
#print axioms BigHrushovski.CFCoherentTower.actualSupportedDomain_ofPoint
#print axioms BigHrushovski.CFCoherentTower.actualSupported_le_iff_domain_subset
#print axioms BigHrushovski.CFCoherentTower.actualSupported_approx_ofPoint
#print axioms BigHrushovski.CFCoherentTower.actualSupported_ramseySpace
#print axioms BigHrushovski.CFCoherentTower.actualSupported_isTychonoffClosed
#print axioms BigHrushovski.CFCoherentTower.actualSupported_Ellentuck
#print axioms BigHrushovski.CFCoherentTower.realSupported_Ellentuck
