import ZFVP.ModelTheory.UsubaSuccessorStageModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

/-- Under VP, stage `i` satisfies dependent choice at every ordinal below its
checked stage index. -/
theorem usubaStageDCBelow_all [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    (i : V) [IsOrdinal i] : UsubaStageDCBelow i :=
  usubaStageDCBelow_induction
    (fun k _ hbelow _ hH ↦ UsubaSuccessorStage.dependentChoiceAt_of_stageDCBelow k hH hVP hbelow) i

theorem usubaStage_dependentChoiceAt [Countable V]
    (hVP : ∀ φ : SetTheorySemisentence 2, VopenkaInstance (V := V) φ)
    {i α : V} [IsOrdinal i] (hα : α ∈ i) {G : Set V}
    (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) :
    InternalDependentChoiceAt ((usubaStageContext i hG).check α) :=
  usubaStageDCBelow_semantics (usubaStageDCBelow_all hVP i) hG _
    (((usubaStageContext i hG).check_mem_iff _ _).mpr hα)

end ZFVP
