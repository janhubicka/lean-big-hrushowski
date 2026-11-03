import BigHrushovski.CFPartialOneLevelFunctional
import BigHrushovski.CFPartialRequestUniqueness

/-!
Track B axiom audit: source file may be extended independently
of CheckAxioms.lean when parallel tracks change concurrently.
The workflow discovers all CheckAxioms*.lean sources and
builds their imports before checking standard axioms.
-/

#print axioms BigHrushovski.CFStageCatalogue.selectedOneLevelBValue
#print axioms BigHrushovski.CFStageCatalogue.targetOneLevelBValue
#print axioms BigHrushovski.CFCoherentTower.selectedGrowthBatchMapSubtype_oneLevel
#print axioms BigHrushovski.CFStageCatalogue.transportGrowthStageRequest_partial_unique

import BigHrushovski.CFSkippedCutEquiv

#print axioms BigHrushovski.CFCoherentTower.skippedCutEquiv
#print axioms BigHrushovski.CFCoherentTower.skippedCutEquiv_val
#print axioms BigHrushovski.CFCoherentTower.skippedCutEquiv_induced
#print axioms BigHrushovski.CFCoherentTower.skippedCutEquiv_birthVertex
#print axioms BigHrushovski.CFCoherentTower.skippedCutEquiv_stageOrder_iff
