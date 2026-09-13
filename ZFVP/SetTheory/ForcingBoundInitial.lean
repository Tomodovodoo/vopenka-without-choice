import ZFVP.SetTheory.ForcingBoundExtension

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def forcingIdentityBound (P I : V) : V :=
  definableGraph ((P ^ I) ×ˢ P) kpair.π₂ (by definability)

instance forcingIdentityBound_definable : ℒₛₑₜ-function₂[V] forcingIdentityBound := by
  have h : ℒₛₑₜ-relation₃ (fun b P I : V ↦ ∀ z, z ∈ b ↔
      ∃ x ∈ (P ^ I) ×ˢ P, z = ⟨x, kpair.π₂ x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingIdentityBound (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [forcingIdentityBound, mem_definableGraph_iff]

theorem forcingIdentityBound_value {P I f p : V} (hf : f ∈ P ^ I) (hp : p ∈ P) :
    (forcingIdentityBound P I) ‘ ⟨f, p⟩ₖ = p := by
  rw [forcingIdentityBound, value_definableGraph _ _ _ (kpair_mem_iff.mpr ⟨hf, hp⟩)]
  simp

noncomputable def forcingInitialBound (i P I : V) : V :=
  forcingFamilyNext i ∅ (forcingIdentityBound (P ‘ i) I)

private theorem last_of_subset {i j : V} (hj : j ∈ succ i) (hij : i ⊆ j) : j = i := by
  rcases mem_succ_iff.mp hj with he | hji
  · exact he
  · exact (mem_irrefl j (hij j hji)).elim

theorem forcingInitialBound_coherent {i P R π E I : V}
    (h : IsSplitForcingSystem (succ i) P π E)
    (m : IsFunctionalSplitForcingSystem (succ i) P π E) :
    IsCoherentForcingBound (succ i) P R π (forcingInitialBound i P I) i I := by
  have hi : i ∈ succ i := mem_succ_self i
  constructor
  · intro j hj hij f hf p hp hb
    have he := last_of_subset hj hij
    subst j
    rw [forcingInitialBound, forcingFamilyNext_new, forcingIdentityBound_value hf.1 hp]
    refine ⟨hp, ?_, h.projId hi hp⟩
    intro a ha
    simpa only [h.projId hi (function_value_mem hf.1 ha)] using hb a ha
  · intro j hj k hk hij hjk f hf p hp _
    have hej := last_of_subset hj hij
    have hek := last_of_subset hk (subset_trans hij hjk)
    subst j k
    rw [forcingInitialBound, forcingFamilyNext_new, forcingIdentityBound_value hf.1 hp, h.projId hi hp,
      forcingIdentityBound_value (compose_function hf.1 (m.projection i hi i hi (subset_refl _))) hp]

end ZFVP
