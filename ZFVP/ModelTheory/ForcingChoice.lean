import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingModelChecks
import ZFVP.SetTheory.EndExtensionWellOrdering
import ZFVP.SetTheory.SmallViolationsOfChoice

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem ofName_wellOrderable_of_closure (S : ForcingContext V) (τ : ForcingName S.P)
    (hC : IsWellOrderable (S.check (nameClosure τ.val))) : IsWellOrderable (S.ofName τ) := by
  let C := nameClosure τ.val
  have hc : ∀ σ ∈ C, IsForcingName S.P σ := fun _ h ↦ forcingName_mem_closure τ.property h
  have hw : IsWellOrderable (range (S.evaluationGraph C hc)) :=
    wellOrderable_of_surjective_function hC (S.evaluationGraph_mem_function C hc) rfl
  apply wellOrderable_of_cardLE (cardLE_of_subset ?_) hw
  intro x hx
  obtain ⟨σ, p, _, hp, rfl⟩ := (S.mem_ofName_iff τ x).mp hx
  exact mem_range_of_kpair_mem ((S.pair_mem_evaluationGraph_iff C hc _ _).mpr
    ⟨σ.val, subname_mem_nameClosure hp, rfl, rfl⟩)

theorem internalChoice_of_check_sets (S : ForcingContext V)
    (h : ∀ A : V, IsWellOrderable (S.check A)) : InternalChoice S.Model := by
  apply internalChoice_of_all_wellOrderable
  intro X
  obtain ⟨τ, rfl⟩ := S.ofName_surjective X
  exact S.ofName_wellOrderable_of_closure τ (h _)

theorem internalChoice_of_ground (S : ForcingContext V) (hAC : InternalChoice V) :
    InternalChoice S.Model :=
  S.internalChoice_of_check_sets (fun A ↦
    S.checkEmbedding.map_wellOrderable (wellOrderable_of_internalChoice hAC A))

theorem internalChoice_of_svcWitness (S : ForcingContext V) {D : V}
    (hD : IsSVCWitness D) (hw : IsWellOrderable (S.check D)) : InternalChoice S.Model := by
  apply S.internalChoice_of_check_sets
  intro A
  obtain ⟨α, hα, f, hf, hr⟩ := hD A
  have : IsOrdinal α := hα
  have hmap : S.check f ∈ S.check A ^ (S.check D ×ˢ S.check α) := by
    rw [← show S.check (D ×ˢ α) = S.check D ×ˢ S.check α from S.checkEmbedding.map_prod D α]
    exact (S.check_function_iff f (D ×ˢ α) A).mpr hf
  have hrange : range (S.check f) = S.check A := by
    exact (S.checkEmbedding.map_range f).symm.trans (congrArg S.check hr)
  exact wellOrderable_of_surjective_function
    (wellOrderable_prod hw (ordinal_wellOrderable (S.check α))) hmap hrange

end ForcingContext
end ZFVP
