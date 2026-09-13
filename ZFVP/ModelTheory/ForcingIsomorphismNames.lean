import ZFVP.ModelTheory.ForcingIsomorphismFormula
import ZFVP.SetTheory.ForcingNameHierarchy
import ZFVP.SetTheory.ForcingSaturatedName

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameAction_forcingNameHierarchy {P Q f ζ τ : V} [IsOrdinal ζ]
    (hf : f ∈ Q ^ P) (hτ : τ ∈ forcingNameHierarchy P ζ) :
    nameAction f τ ∈ forcingNameHierarchy Q ζ := by
  have hall := transfinite_induction (fun α ↦ ∀ ν ∈ forcingNameHierarchy P α,
    nameAction f ν ∈ forcingNameHierarchy Q α) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal ζ) τ hτ
  intro α ih ν hν
  have hn := forcingNameHierarchy_names P (α : V) ν hν
  obtain ⟨β, hβ, hbound⟩ := (mem_forcingNameHierarchy P (α : V) ν).mp hν
  let := IsOrdinal.of_mem hβ
  apply (mem_forcingNameHierarchy Q (α : V) _).mpr
  refine ⟨β, hβ, ?_⟩
  intro z hz
  obtain ⟨σ, p, hσp, rfl⟩ := (mem_nameAction_iff hn f z).mp hz
  have hb := kpair_mem_iff.mp (hbound _ hσp)
  exact kpair_mem_iff.mpr ⟨ih (IsOrdinal.toOrdinal β) hβ σ hb.1, function_value_mem hf hb.2⟩

theorem IsForcingIsomorphism.name_hierarchy_iff {P R Q S f ζ τ : V} [IsOrdinal ζ]
    (hf : IsForcingIsomorphism P R Q S f) (hn : IsForcingName P τ) :
    nameAction f τ ∈ forcingNameHierarchy Q ζ ↔ τ ∈ forcingNameHierarchy P ζ := by
  constructor
  · intro hτ
    have hh := nameAction_forcingNameHierarchy hf.inverse_maps hτ
    simpa only [hf.name_inverse_cancel hn] using hh
  · exact nameAction_forcingNameHierarchy hf.1

theorem IsForcingIsomorphism.saturated_name {P R Q S f ζ N : V} [IsOrdinal ζ]
    (hf : IsForcingIsomorphism P R Q S f) (hN : IsForcingName P N) :
    nameAction f (forcingSaturatedName P R (forcingNameHierarchy P ζ) N) =
      forcingSaturatedName Q S (forcingNameHierarchy Q ζ) (nameAction f N) := by
  apply mem_ext
  intro z
  rw [mem_nameAction_iff (forcingSaturatedName_isName _ _ _ _)]
  constructor
  · rintro ⟨τ, p, hτp, rfl⟩
    obtain ⟨hτ, hp, hn, hm⟩ := (pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hτp
    exact (pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr
      ⟨nameAction_forcingNameHierarchy hf.1 hτ, function_value_mem hf.1 hp,
        nameAction_isName hf.1 hn, atomicMembership_isomorphism_forward hf hn hN hm⟩
  · intro hz
    obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp (forcingSaturatedName_subset _ _ _ _ _ hz)
    obtain ⟨_, _, hn, hm⟩ := (pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hz
    have hback := atomicMembership_isomorphism_forward hf.inverse hn (nameAction_isName hf.1 hN) hm
    rw [hf.name_inverse_cancel hN] at hback
    refine ⟨nameAction (converseGraph f) τ, (converseGraph f) ‘ p, ?_, ?_⟩
    · exact (pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr
        ⟨nameAction_forcingNameHierarchy hf.inverse_maps hτ, function_value_mem hf.inverse_maps hp,
          nameAction_isName hf.inverse_maps hn, hback⟩
    · rw [hf.name_cancel_inverse hn, hf.value_inverse hp]

end ZFVP
