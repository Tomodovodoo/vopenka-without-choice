import ZFVP.ModelTheory.UsubaLSSuccessorStageModel

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "T" => usubaForcingTower (V := V)

theorem usubaStageDCBelow_all_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    (i : V) [IsOrdinal i] : UsubaStageDCBelow i :=
  usubaStageDCBelow_induction
    (fun k _ hbelow _ hH ↦
      UsubaSuccessorStage.dependentChoiceAt_of_stageDCBelow_of_ls k hH hLS hbelow) i

theorem usubaStage_dependentChoiceAt_of_ls [Countable V]
    (hLS : ∀ α : V, IsOrdinal α → ∃ κ : V, α ∈ κ ∧ IsLSCardinal κ)
    {i α : V} [IsOrdinal i] (hα : α ∈ i) {G : Set V}
    (hG : IsExternalForcingGeneric ((T).P i) ((T).R i) G) :
    InternalDependentChoiceAt ((usubaStageContext i hG).check α) :=
  usubaStageDCBelow_semantics (usubaStageDCBelow_all_of_ls hLS i) hG _
    (((usubaStageContext i hG).check_mem_iff _ _).mpr hα)

end ZFVP
