import ZFVP.SetTheory.DeltaOneForcingNames
import ZFVP.SetTheory.ForcingSequenceNames
import ZFVP.SetTheory.BoundedCodingSupport

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsForcingNameFamily (P D : V) : Prop :=
  ∀ τ ∈ D, ∀ z ∈ τ, ∃ u ∈ D, ∃ p ∈ P, z = ⟨u, p⟩ₖ

instance boundedNameFamilyFormula_defined :
    ℒₛₑₜ-relation[V] IsForcingNameFamily via boundedNameFamilyFormula := ⟨fun v ↦ by
  simp [boundedNameFamilyFormula, IsForcingNameFamily]⟩

instance forcingNameFamily_definable : ℒₛₑₜ-relation[V] IsForcingNameFamily :=
  boundedNameFamilyFormula_defined.to_definable

theorem IsForcingNameFamily.subname_closed {P D : V} (hD : IsForcingNameFamily P D) :
    IsSubnameClosed D := by
  intro τ hτ u hu
  obtain ⟨p, hp⟩ := mem_domain_iff.mp hu
  obtain ⟨v, hv, q, _, he⟩ := hD τ hτ _ hp
  exact (kpair_iff.mp he).1 ▸ hv

theorem IsForcingNameFamily.names {P D : V} (hD : IsForcingNameFamily P D) :
    ∀ τ ∈ D, IsForcingName P τ := by
  intro τ hτ σ hσ z hz
  obtain ⟨u, _, p, hp, he⟩ := hD σ (nameClosure_minimal hD.subname_closed hτ σ hσ) z hz
  exact ⟨u, p, hp, he⟩

theorem forcingNameFamily_of_closed {P D : V} (hD : ∀ τ ∈ D, IsForcingName P τ)
    (hc : IsSubnameClosed D) : IsForcingNameFamily P D := by
  intro τ hτ z hz
  obtain ⟨u, p, hp, he⟩ := hD τ hτ τ (mem_nameClosure_self τ) z hz
  exact ⟨u, hc τ hτ u (mem_domain_of_kpair_mem (he ▸ hz)), p, hp, he⟩

theorem forcingNameFamily_transitive_part (P T : V) (hT : IsTransitive T) :
    IsForcingNameFamily P {τ ∈ T ; IsForcingName P τ} := by
  apply forcingNameFamily_of_closed (fun _ h ↦ (mem_sep_iff.mp h).2)
  intro τ hτ u hu
  obtain ⟨p, hp⟩ := mem_domain_iff.mp hu
  exact mem_sep_iff.mpr ⟨transitive_subnameClosed hT τ (mem_sep_iff.mp hτ).1 u hu,
    forcingName_subname (mem_sep_iff.mp hτ).2 hp⟩

theorem nameSequence_family_exists {P n b : V} [IsFunction b]
    (hs : IsNameSequence P b) (hd : domain b = n) :
    ∃ D : V, IsForcingNameFamily P D ∧ IsNonempty D ∧ b ∈ D ^ n := by
  let T : V := transitiveClosure ({b, ∅} : V)
  have hT : IsTransitive T := transitiveClosure_transitive _
  have hbT : b ∈ T := subset_transitiveClosure _ _ (by simp)
  have h0T : (∅ : V) ∈ T := subset_transitiveClosure _ _ (by simp)
  let D : V := {τ ∈ T ; IsForcingName P τ}
  refine ⟨D, forcingNameFamily_transitive_part P T hT, ⟨∅, mem_sep_iff.mpr ⟨h0T, empty_forcingName P⟩⟩, ?_⟩
  rw [← hd]
  apply mem_function_of_mem_function_of_subset (IsFunction.mem_function b)
  intro y hy
  obtain ⟨i, hi⟩ := mem_range_iff.mp hy
  have hid := mem_domain_of_kpair_mem hi
  have he := value_eq_of_kpair_mem hi
  exact mem_sep_iff.mpr ⟨(kpair_components_mem_transitive (hT.mem_trans hi hbT)).2, he ▸ hs i hid⟩

end ZFVP
