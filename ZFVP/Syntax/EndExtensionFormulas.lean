import ZFVP.Syntax.EndExtensionFormulaCodes
import ZFVP.Syntax.GeneratedFormulas

/-! Complete formula families agree across arbitrary ZF membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem formulaClosed_map (j : MembershipEndExtension V W) {L Γ Q : V} (hL : IsLanguageCode L)
    (hQ : IsFormulaClosed L Γ Q) : IsFormulaClosed (j L) (j Γ) (j Q) := by
  intro m hm
  rw [← j.map_omega] at hm
  obtain ⟨n, hn, rfl⟩ := j.endExtension ω m hm
  have hc := hQ n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rw [← j.map_truthCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hc.1.1
    · rw [← j.map_falsityCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hc.1.2
  · intro r args ha
    obtain ⟨s, bs, rfl, rfl, hsrc⟩ := j.atomicArguments_preimages hL hn ha
    have hh := hc.2.1 s bs hsrc
    constructor
    · rw [← j.map_atomCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.1
    · rw [← j.map_negAtomCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.2
  · intro φ ψ hφ hψ
    obtain ⟨a, ha, rfl⟩ := (j.pair_mem_image_left_iff Q n φ).mp hφ
    obtain ⟨b, hb, rfl⟩ := (j.pair_mem_image_left_iff Q n ψ).mp hψ
    have hh := hc.2.2.1 a b ha hb
    constructor
    · rw [← j.map_andCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.1
    · rw [← j.map_orCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.2
  · intro φ hφ
    rw [← j.map_succ] at hφ
    obtain ⟨a, ha, rfl⟩ := (j.pair_mem_image_left_iff Q (succ n) φ).mp hφ
    have hh := hc.2.2.2 a ha
    constructor
    · rw [← j.map_allCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.1
    · rw [← j.map_existsCode, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hh.2

theorem formulaGenerated_map (j : MembershipEndExtension V W) {L Γ Q : V} (hL : IsLanguageCode L)
    (hQ : IsFormulaGenerated L Γ Q) : IsFormulaGenerated (j L) (j Γ) (j Q) := by
  intro p hp
  obtain ⟨a, ha, rfl⟩ := j.endExtension Q p hp
  obtain ⟨n, hn, φ, rfl, hc⟩ := hQ a ha
  refine ⟨j n, (j.natural_iff n).mpr hn, j φ, j.map_kpair n φ, ?_⟩
  rcases hc with rfl | rfl | ⟨r, args, hargs, he⟩ | ⟨ψ, χ, hψ, hχ, he⟩ | ⟨ψ, hψ, he⟩
  · exact Or.inl j.map_truthCode
  · exact Or.inr (Or.inl j.map_falsityCode)
  · refine Or.inr (Or.inr (Or.inl ⟨j r, j args, j.atomicArguments_map hL hn hargs, ?_⟩))
    rcases he with rfl | rfl
    · exact Or.inl (j.map_atomCode r args)
    · exact Or.inr (j.map_negAtomCode r args)
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j ψ, j χ, ?_, ?_, ?_⟩)))
    · rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hψ
    · rw [← j.map_kpair]; exact (j.mem_iff _ _).mpr hχ
    · rcases he with rfl | rfl
      · exact Or.inl (j.map_andCode ψ χ)
      · exact Or.inr (j.map_orCode ψ χ)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨j ψ, ?_, ?_⟩)))
    · rw [← j.map_succ, ← j.map_kpair]; exact (j.mem_iff _ _).mpr hψ
    · rcases he with rfl | rfl
      · exact Or.inl (j.map_allCode ψ)
      · exact Or.inr (j.map_existsCode ψ)

theorem map_formulaFamily (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L) (Γ : V) :
    j (formulaFamily L Γ) = formulaFamily (j L) (j Γ) := by
  apply SetTheory.subset_antisymm
  · exact formulaGenerated_subset ((j.languageCode_iff L).mpr hL)
      (j.formulaGenerated_map hL (formulaFamily_generated hL Γ))
  · exact formulaFamily_minimal (j.formulaClosed_map hL (formulaFamily_closed hL Γ))

theorem map_formulaSet (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L) (Γ n : V) :
    j (formulaSet L Γ n) = formulaSet (j L) (j Γ) (j n) := by
  apply mem_ext
  intro φ
  rw [mem_formulaSet_iff, ← j.map_formulaFamily hL Γ, j.pair_mem_image_left_iff]
  constructor
  · intro h
    obtain ⟨ψ, hψ, rfl⟩ := j.endExtension _ φ h
    exact ⟨ψ, (mem_formulaSet_iff _ _ _ _).mp hψ, rfl⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact (j.mem_iff _ _).mpr ((mem_formulaSet_iff _ _ _ _).mpr hψ)

end MembershipEndExtension
end ZFVP
