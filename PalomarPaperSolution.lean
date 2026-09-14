-- Generated from the four individual Solution files.
import PalomarPreservationBridge.TheoremA
import PalomarBridge.TheoremB
import PalomarDCBridge.TheoremDC
import PalomarSolovayBridge.TheoremSolovay

namespace VopenkaWithoutChoice

theorem palomar_preservation {M : Type u} (mem : M → M → Prop) [Nonempty M]
    (hZF : PalomarBridge.IsZF mem) (hVP : PalomarBridge.Coding.Vopenka mem)
    (d : PalomarPreservationBridge.SymmetricData mem) :
    (∃ (W : Type u) (wmem : W → W → Prop),
      PalomarPreservationBridge.Presentation mem d W wmem) ∧
    ∀ (W : Type u) (wmem : W → W → Prop),
      PalomarPreservationBridge.Presentation mem d W wmem →
        PalomarPreservationBridge.IsZFVPModel wmem :=
  PalomarPreservationBridge.independent_theoremA mem hZF hVP d

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_preservation

namespace VopenkaWithoutChoice

/-- The paper's Theorem B, expressed in the independent membership vocabulary.
The imported bridge identifies the full ZF, choice and VP dictionaries with
the original formalization before using its equiconsistency proof. -/
theorem palomar_equiconsistency :
    PalomarBridge.HasZFCVPModel ↔ PalomarBridge.HasZFVPModel :=
  PalomarBridge.independent_theoremB

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_equiconsistency

namespace VopenkaWithoutChoice

theorem palomar_dependent_choice (h : PalomarBridge.HasZFVPModel) :
    PalomarDCBridge.HasZFVPDCNotChoiceModel :=
  PalomarDCBridge.independent_dependent_choice h

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_dependent_choice

namespace VopenkaWithoutChoice

theorem palomar_solovay_reals (h : PalomarBridge.HasZFVPModel) :
    PalomarSolovayBridge.HasSolovayModel :=
  PalomarSolovayBridge.independent_solovay_reals h

end VopenkaWithoutChoice

#print axioms VopenkaWithoutChoice.palomar_solovay_reals
