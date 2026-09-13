import ZFVP.ModelTheory.ForcingModelEvaluation
import ZFVP.ModelTheory.ForcingModelGeneric
import ZFVP.SetTheory.EndExtensionNameValue

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

theorem evaluationGraph_valueRecursion (A : ForcingContext V) (C : V)
    (hC : IsSubnameClosed C) (hN : ∀ σ ∈ C, IsForcingName A.P σ) :
    IsSubnameRecursion (A.check C) (nameValueStep A.genericSet) (A.evaluationGraph C hN) := by
  refine ⟨inferInstance, A.evaluationGraph_domain C hN, ?_⟩
  intro x hx
  obtain ⟨σ, hσ, rfl⟩ := (A.mem_check_iff C x).mp hx
  rw [A.evaluationGraph_value C hN σ hσ]
  have hval (ρ : V) (hρ : ρ ∈ domain σ) :
      ((A.evaluationGraph C hN) ↾ (domain (A.check σ))) ‘ (A.check ρ) =
        A.ofName ⟨ρ, hN ρ (hC σ hσ ρ hρ)⟩ := by
    have hρD : A.check ρ ∈ domain (A.evaluationGraph C hN) := by
      rw [A.evaluationGraph_domain]
      exact (A.check_mem_iff _ _).mpr (hC σ hσ ρ hρ)
    have hρσ : A.check ρ ∈ domain (A.check σ) := by
      have hd : A.check (domain σ) = domain (A.check σ) := A.checkEmbedding.map_relationDomain σ
      rw [← hd]
      exact (A.check_mem_iff _ _).mpr hρ
    rw [value_restrict hρD hρσ, A.evaluationGraph_value C hN ρ (hC σ hσ ρ hρ)]
  apply mem_ext
  intro z
  rw [mem_nameValueStep_iff]
  constructor
  · intro hz
    obtain ⟨ν, p, hp, hνp, he⟩ := (A.mem_ofName_iff ⟨σ, hN σ hσ⟩ z).mp hz
    refine ⟨A.check ν.val, A.check p, (A.check_mem_genericSet_iff p).mpr hp, ?_, ?_⟩
    · rw [← A.check_kpair, A.check_mem_iff]
      exact hνp
    · rw [hval ν.val (mem_domain_of_kpair_mem hνp)]
      exact he
  · rintro ⟨ν, p, hp, hνp, he⟩
    obtain ⟨ρ, q, hρq, rfl, rfl⟩ := (A.checkEmbedding.pair_mem_image_iff σ ν p).mp hνp
    change z = ((A.evaluationGraph C hN) ↾ (domain (A.check σ))) ‘ (A.check ρ) at he
    rw [hval ρ (mem_domain_of_kpair_mem hρq)] at he
    exact (A.mem_ofName_iff ⟨σ, hN σ hσ⟩ z).mpr
      ⟨⟨ρ, hN ρ (hC σ hσ ρ (mem_domain_of_kpair_mem hρq))⟩, q,
        (A.check_mem_genericSet_iff q).mp hp, hρq, he⟩

theorem nameValue_genericSet_check (A : ForcingContext V) (τ : ForcingName A.P) :
    nameValue A.genericSet (A.check τ.val) = A.ofName τ := by
  let hN : ∀ σ ∈ nameClosure τ.val, IsForcingName A.P σ :=
    fun _ hσ ↦ forcingName_mem_closure τ.property hσ
  have hf := A.evaluationGraph_valueRecursion (nameClosure τ.val) (nameClosure_closed τ.val) hN
  have he := subnameRecursion_coherent
    (A.checkEmbedding.map_subnameClosed (nameClosure_closed τ.val))
    (nameClosure_closed (A.check τ.val)) hf
    (subnameRecursionTable_spec (nameValueStep A.genericSet) (by definability) (A.check τ.val))
    (A.check τ.val) ((A.check_mem_iff _ _).mpr (mem_nameClosure_self τ.val))
    (mem_nameClosure_self (A.check τ.val))
  rw [A.evaluationGraph_value _ _ _ (mem_nameClosure_self τ.val)] at he
  exact he.symm

end ForcingContext
end ZFVP
