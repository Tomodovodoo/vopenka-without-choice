import ZFVP.ModelTheory.UsubaSingularCollapseConsistency
import ZFVP.ModelTheory.CohenVopenkaConsistency

/-! V13 Corollary 6.4: DC is independent of ZF + VP + not Choice,
relative to the consistency of ZF + VP. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

def zfVPNotChoiceTheory : Theory ℒₛₑₜ := insert (∼choiceFunctionSentence) zfVPTheory

theorem dependentChoice_independent_of_zfVP_notChoice (h : Consistent zfVPTheory) :
    Independent zfVPNotChoiceTheory dependentChoiceSentence := by
  classical
  constructor
  · apply unprovable_iff_consistent_adjoin.mpr
    change Consistent (insert (∼dependentChoiceSentence) zfVPNotChoiceTheory)
    have hn := consistent_zfVP_notChoice_notDC h
    simpa [zfVPNotChoiceTheory, zfVPNotChoiceNotDCTheory, Set.insert_comm] using hn
  · apply unprovable_iff_consistent_adjoin.mpr
    change Consistent (insert (∼∼dependentChoiceSentence) zfVPNotChoiceTheory)
    have hp := consistent_zfVP_DC_notChoice_of_zfVP h
    simpa [zfVPNotChoiceTheory, zfVPDCNotChoiceTheory] using hp

end ZFVP

