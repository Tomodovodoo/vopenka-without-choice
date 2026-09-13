import PalomarDCBridge.TheoremDC

namespace VopenkaWithoutChoice

theorem palomar_dependent_choice (h : PalomarBridge.HasZFVPModel) :
    PalomarDCBridge.HasZFVPDCNotChoiceModel :=
  PalomarDCBridge.independent_dependent_choice h

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_dependent_choice
