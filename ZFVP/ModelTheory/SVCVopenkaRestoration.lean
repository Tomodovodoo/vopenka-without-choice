import ZFVP.ModelTheory.CollapseModel
import ZFVP.ModelTheory.ForcingVopenkaPreservation
import ZFVP.ModelTheory.CodedZFVPExternal

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def zfcVPTheory : Theory ℒₛₑₜ := 𝗭𝗙𝗖 ∪ vopenkaTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem collapse_model_zfcVP {D : V} (hD : IsSVCWitness D)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {G : Set V} (hG : IsExternalForcingGeneric (collapseConditions D) (collapseOrder D) G) :
    (collapseContext D G hG).Model↓[ℒₛₑₜ] ⊧* zfcVPTheory := by
  let S := collapseContext D G hG
  have hAC : S.Model↓[ℒₛₑₜ] ⊧* 𝗔𝗖 :=
    models_ac_of_internalChoice (CollapseModel.internalChoice_of_svcWitness hG hD)
  refine ⟨?_⟩
  intro φ hφ
  rcases hφ with (hφ | hφ) | ⟨ψ, rfl⟩
  · exact Theory.models S.Model 𝗭𝗙 hφ
  · exact Theory.models S.Model 𝗔𝗖 hφ
  · exact (eval_vopenkaSentence ψ).mpr (S.vopenkaInstance (collapse_poset D) hVP ψ)

theorem svc_collapse_restores_zfcVP (hSVC : InternalSmallViolationsOfChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ) :
    ∃ D : V, ∀ G : Set V,
      ∀ hG : IsExternalForcingGeneric (collapseConditions D) (collapseOrder D) G,
        (collapseContext D G hG).Model↓[ℒₛₑₜ] ⊧* zfcVPTheory := by
  obtain ⟨D, hD⟩ := hSVC
  exact ⟨D, fun _ hG ↦ collapse_model_zfcVP hD hVP hG⟩

theorem exists_svc_zfcVP_generic_extension [Countable V]
    (hSVC : InternalSmallViolationsOfChoice V)
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ) :
    ∃ D : V, ∃ G : Set V,
      ∃ hG : IsExternalForcingGeneric (collapseConditions D) (collapseOrder D) G,
        (collapseContext D G hG).Model↓[ℒₛₑₜ] ⊧* zfcVPTheory := by
  obtain ⟨D, hD⟩ := hSVC
  obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric (collapse_poset D).1 (collapse_top D).1
  exact ⟨D, G, hG, collapse_model_zfcVP hD hVP hG⟩

end ZFVP
