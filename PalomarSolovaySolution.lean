import PalomarSolovayBridge.TheoremSolovay

namespace VopenkaWithoutChoice

theorem palomar_solovay_reals (h : PalomarBridge.HasZFVPModel) :
    PalomarSolovayBridge.HasSolovayModel :=
  PalomarSolovayBridge.independent_solovay_reals h

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_solovay_reals
