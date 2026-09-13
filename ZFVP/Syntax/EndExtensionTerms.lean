import ZFVP.ModelTheory.EndExtensionLanguage
import ZFVP.Syntax.GeneratedTerms

/-! All internal term codes agree across ZF membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_boundVarCode (j : MembershipEndExtension V W) (i : V) :
    j (boundVarCode i) = boundVarCode (j i) := by
  unfold boundVarCode
  rw [j.map_kpair, show j (0 : V) = (0 : W) from j.map_numeral 0]

theorem map_freeVarCode (j : MembershipEndExtension V W) (i : V) :
    j (freeVarCode i) = freeVarCode (j i) := by
  unfold freeVarCode
  rw [j.map_kpair, show j (1 : V) = (1 : W) from j.map_numeral 1]

theorem map_functionTermCode (j : MembershipEndExtension V W) (f args : V) :
    j (functionTermCode f args) = functionTermCode (j f) (j args) := by
  unfold functionTermCode
  rw [j.map_kpair, j.map_kpair, show j (2 : V) = (2 : W) from j.map_numeral 2]

theorem termClosed_map (j : MembershipEndExtension V W) {L Γ n T : V} (hL : IsLanguageCode L)
    (hT : IsTermClosed L Γ n T) : IsTermClosed (j L) (j Γ) (j n) (j T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := j.endExtension n k hk
    rw [← j.map_boundVarCode]
    exact (j.mem_iff _ _).mpr (hT.1 i hi)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := j.endExtension Γ y hy
    rw [← j.map_freeVarCode]
    exact (j.mem_iff _ _).mpr (hT.2.1 x hx)
  · intro g hg bs hbs
    rw [← j.map_functionSymbols] at hg
    obtain ⟨f, hf, rfl⟩ := j.endExtension _ g hg
    rw [← j.map_functionArity hL hf, ← j.map_finiteFunctionSet T (hL.function_arity_natural hf)] at hbs
    obtain ⟨args, ha, rfl⟩ := j.endExtension _ bs hbs
    rw [← j.map_functionTermCode]
    exact (j.mem_iff _ _).mpr (hT.2.2 f hf args ha)

theorem termGenerated_map (j : MembershipEndExtension V W) {L Γ n T : V} (hL : IsLanguageCode L)
    (hT : IsTermGenerated L Γ n T) : IsTermGenerated (j L) (j Γ) (j n) (j T) := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := j.endExtension T u hu
  rcases hT t ht with ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨f, hf, args, ha, rfl⟩
  · exact Or.inl ⟨j i, (j.mem_iff _ _).mpr hi, j.map_boundVarCode i⟩
  · exact Or.inr (Or.inl ⟨j x, (j.mem_iff _ _).mpr hx, j.map_freeVarCode x⟩)
  · refine Or.inr (Or.inr ⟨j f, ?_, j args, ?_, j.map_functionTermCode f args⟩)
    · rw [← j.map_functionSymbols]; exact (j.mem_iff _ _).mpr hf
    · rw [← j.map_functionArity hL hf]; exact (j.function_iff _ _ _).mpr ha

theorem map_termSet (j : MembershipEndExtension V W) {L n : V} (hL : IsLanguageCode L)
    (hn : n ∈ (ω : V)) (Γ : V) : j (termSet L Γ n) = termSet (j L) (j Γ) (j n) := by
  apply SetTheory.subset_antisymm
  · exact termGenerated_subset ((j.languageCode_iff L).mpr hL) ((j.natural_iff n).mpr hn)
      (j.termGenerated_map hL (termSet_generated hL hn Γ))
  · exact termSet_minimal (j.termClosed_map hL (termSet_closed hL hn Γ))

end MembershipEndExtension
end ZFVP
