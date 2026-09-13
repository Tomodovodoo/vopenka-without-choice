import PalomarBridge.TheoremB

namespace VopenkaWithoutChoice

/-- The paper's Theorem B, expressed in the independent membership vocabulary.
The imported bridge identifies the full ZF, choice and VP dictionaries with
the original formalization before using its equiconsistency proof. -/
theorem palomar_equiconsistency :
    PalomarBridge.HasZFCVPModel ↔ PalomarBridge.HasZFVPModel :=
  PalomarBridge.independent_theoremB

end VopenkaWithoutChoice
