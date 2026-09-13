import PalomarPreservationBridge.Presentation
import PalomarBridge.VPDictionary
import ZFVP.ModelTheory.SymmetricVopenkaPreservation

namespace PalomarPreservationBridge
open PalomarBridge LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- Theorem A for every presentation of the specified symmetric quotient,
together with existence of that quotient. The generic is supplied; the ground
need not be externally countable, transitive, or well-founded. -/
theorem independent_theoremA {M : Type u} (mem : M → M → Prop) [Nonempty M]
    (hZF : IsZF mem) (hVP : Coding.Vopenka mem) (d : SymmetricData mem) :
    (∃ (W : Type u) (wmem : W → W → Prop), Presentation mem d W wmem) ∧
    ∀ (W : Type u) (wmem : W → W → Prop),
      Presentation mem d W wmem → IsZFVPModel wmem := by
  let : SetStructure M := ⟨fun y x => mem x y⟩
  let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := isZF_iff_models.mp hZF
  let S := toContext d
  have hground : ∀ p : SetTheorySemisentence 2, ZFVP.VopenkaInstance (V := M) p :=
    coding_vopenka_iff.mp hVP
  refine ⟨⟨S.Model, (fun x y => x ∈ y), canonical_presentation d⟩, ?_⟩
  intro W wmem hp
  obtain ⟨e, he⟩ := presentation_isomorphic d wmem hp
  let : SetStructure W := ⟨fun y x => wmem x y⟩
  let hne : Nonempty W := Nonempty.map e inferInstance
  have hW : W↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
    constructor
    intro p hp
    have hs := Theory.models S.Model 𝗭𝗙 hp
    change p.Eval ![] Empty.elim at hs
    have ht := (ZFVP.eval_membershipIso e he p ![] Empty.elim).mp hs
    have hb : e ∘ (![] : Fin 0 → S.Model) = (![] : Fin 0 → W) := Subsingleton.elim _ _
    have hf : e ∘ (Empty.elim : Empty → S.Model) = (Empty.elim : Empty → W) :=
      Subsingleton.elim _ _
    simpa only [models_iff, Semiformula.Realize, hb, hf] using ht
  let := hW
  refine ⟨hne, isZF_iff_models.mpr hW, coding_vopenka_iff.mpr ?_⟩
  intro p
  exact ZFVP.vopenkaInstance_of_membershipIso e he p (S.vopenkaInstance hground p)

end PalomarPreservationBridge

#print axioms PalomarPreservationBridge.independent_theoremA
