import PalomarPreservationBridge.TheoremA

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
