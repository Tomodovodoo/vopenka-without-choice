import ZFVP.ModelTheory.CohenRigidConsistency
import ZFVP.ModelTheory.WoodinSparseRestorationTheorem

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

/-- The positive Cohen rigid-relation consistency theorem from the original
ZF+VP consistency hypothesis, using the proved finite restoration theorem. -/
theorem consistent_zfVP_rigid_notChoice_notDC_of_zfVP (h : Consistent zfVPTheory) :
    Consistent zfVPRigidNotChoiceNotDCTheory :=
  consistent_zfVP_rigid_notChoice_notDC_of_zfcVP
    (consistent_zfcVP_of_consistent_zfVP_woodin h)

end ZFVP
