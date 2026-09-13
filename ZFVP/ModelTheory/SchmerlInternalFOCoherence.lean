import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms
import ZFVP.Syntax.FormulaInversion

/-! Syntactic coherence between the finite first-order codes and the
infinitary constructors. Embedded first-order formulas do not behave as
independent propositional letters. All formula contexts are internal. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def equivCode (φ ψ : V) : V := andCode (impCode φ ψ) (impCode ψ φ)

instance equivCode_definable : ℒₛₑₜ-function₂[V] equivCode := by unfold equivCode; definability

theorem IsFragment.equiv_left_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, equivCode φ ψ⟩ₖ ∈ F) : ⟨n, φ⟩ₖ ∈ F := hF.imp_left_mem (hF.and_left_mem h)

theorem IsFragment.equiv_right_mem {L F n φ ψ : V} (hF : IsFragment L F)
    (h : ⟨n, equivCode φ ψ⟩ₖ ∈ F) : ⟨n, ψ⟩ₖ ∈ F := hF.imp_right_mem (hF.and_left_mem h)

theorem holds_equiv {L F M n φ ψ b : V} (hF : IsFragment L F)
    (h : ⟨n, equivCode φ ψ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (equivCode φ ψ) b ↔ (Holds L F M n φ b ↔ Holds L F M n ψ b) := by
  rw [equivCode, holds_and hF h hb, holds_imp hF (hF.and_left_mem h) hb,
    holds_imp hF (hF.and_right_mem h) hb]
  tauto

def IsFOCoherenceAxiom (L n χ : V) : Prop := IsLanguageCode L ∧ n ∈ (ω : V) ∧
  (χ = foCode truthCode ∨ χ = negCode (foCode falsityCode) ∨
  (∃ r args, atomCode r args ∈ formulaSet L ∅ n ∧
    χ = equivCode (foCode (negAtomCode r args)) (negCode (foCode (atomCode r args)))) ∨
  (∃ φ ψ, φ ∈ formulaSet L ∅ n ∧ ψ ∈ formulaSet L ∅ n ∧
    χ = equivCode (foCode (ZFVP.andCode φ ψ)) (andCode (foCode φ) (foCode ψ))) ∨
  (∃ φ ψ, φ ∈ formulaSet L ∅ n ∧ ψ ∈ formulaSet L ∅ n ∧
    χ = equivCode (foCode (orCode φ ψ)) (impCode (negCode (foCode φ)) (foCode ψ))) ∨
  (∃ φ, φ ∈ formulaSet L ∅ (succ n) ∧
    χ = equivCode (foCode (ZFVP.allCode φ)) (allCode (foCode φ))) ∨
  ∃ φ, φ ∈ formulaSet L ∅ (succ n) ∧
    χ = equivCode (foCode (existsCode φ)) (exsCode (foCode φ)))

instance isFOCoherenceAxiom_definable : ℒₛₑₜ-relation₃[V] IsFOCoherenceAxiom := by
  unfold IsFOCoherenceAxiom
  apply Language.Definable.and (by definability)
  apply Language.Definable.and (by definability)
  repeat' apply Language.Definable.or
  all_goals definability

theorem IsFOCoherenceAxiom.sound {L F M n χ b : V} (hχ : IsFOCoherenceAxiom L n χ)
    (hF : IsFragment L F) (ht : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n χ b := by
  obtain ⟨hL, hn, hχ⟩ := hχ
  rcases hχ with rfl | rfl | ⟨r, args, ha, rfl⟩ | ⟨φ, ψ, hφ, hψ, rfl⟩ |
    ⟨φ, ψ, hφ, hψ, rfl⟩ | ⟨φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩
  · exact (holds_fo hF ht).mpr ((satisfies_truth hL hn).mpr hb)
  · rw [holds_neg hF ht hb, holds_fo hF (hF.neg_mem ht)]
    exact not_satisfies_falsity hL hn
  · have hl := hF.equiv_left_mem ht
    have hr := hF.equiv_right_mem ht
    rw [holds_equiv hF ht hb, holds_fo hF hl, holds_neg hF hr hb,
      holds_fo hF (hF.neg_mem hr), satisfies_negAtom hL hn ((atomCode_mem_iff hL).mp ha).2 hb,
      satisfies_atom hL hn ((atomCode_mem_iff hL).mp ha).2 hb]
  · have hl := hF.equiv_left_mem ht
    have hr := hF.equiv_right_mem ht
    rw [holds_equiv hF ht hb, holds_fo hF hl, satisfies_and hL hn hφ hψ hb,
      holds_and hF hr hb, holds_fo hF (hF.and_left_mem hr), holds_fo hF (hF.and_right_mem hr)]
  · have hl := hF.equiv_left_mem ht
    have hr := hF.equiv_right_mem ht
    rw [holds_equiv hF ht hb, holds_fo hF hl, satisfies_or hL hn hφ hψ hb,
      holds_imp hF hr hb, holds_neg hF (hF.imp_left_mem hr) hb,
      holds_fo hF (hF.neg_mem (hF.imp_left_mem hr)), holds_fo hF (hF.imp_right_mem hr)]
    tauto
  · have hl := hF.equiv_left_mem ht
    have hr := hF.equiv_right_mem ht
    rw [holds_equiv hF ht hb, holds_fo hF hl, satisfies_all hL hn hφ hb, holds_all hF hr hb]
    apply forall₂_congr
    intro x _
    exact (holds_fo hF (hF.all_mem hr)).symm
  · have hl := hF.equiv_left_mem ht
    have hr := hF.equiv_right_mem ht
    rw [holds_equiv hF ht hb, holds_fo hF hl, satisfies_exists hL hn hφ hb, holds_exs hF hr hb]
    apply exists_congr
    intro x
    exact and_congr_right (fun _ ↦ (holds_fo hF (hF.exs_mem hr)).symm)

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_equivCode (φ ψ : V) : j (equivCode φ ψ) = equivCode (j φ) (j ψ) := by
  simp only [equivCode, map_andCode, map_impCode]

theorem foCoherenceAxiom_map {L n χ : V} (hχ : IsFOCoherenceAxiom L n χ) :
    IsFOCoherenceAxiom (j L) (j n) (j χ) := by
  obtain ⟨hL, hn, hχ⟩ := hχ
  refine ⟨(j.languageCode_iff L).mpr hL, (j.natural_iff n).mpr hn, ?_⟩
  have hm {m φ : V} (hφ : φ ∈ formulaSet L ∅ m) : j φ ∈ formulaSet (j L) ∅ (j m) := by
    simpa only [j.map_formulaSet hL, j.map_empty] using (j.mem_iff _ _).mpr hφ
  rcases hχ with rfl | rfl | ⟨r, args, ha, rfl⟩ | ⟨φ, ψ, hφ, hψ, rfl⟩ |
    ⟨φ, ψ, hφ, hψ, rfl⟩ | ⟨φ, hφ, rfl⟩ | ⟨φ, hφ, rfl⟩
  · exact Or.inl (by rw [map_foCode, j.map_truthCode])
  · exact Or.inr (Or.inl (by rw [map_negCode, map_foCode, j.map_falsityCode]))
  · refine Or.inr (Or.inr (Or.inl ⟨j r, j args, ?_, ?_⟩))
    · simpa only [j.map_atomCode] using hm ha
    · simp only [map_equivCode, map_foCode, map_negCode, j.map_negAtomCode, j.map_atomCode]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j φ, j ψ, hm hφ, hm hψ, ?_⟩)))
    simp only [map_equivCode, map_foCode, j.map_andCode, map_andCode]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j φ, j ψ, hm hφ, hm hψ, ?_⟩))))
    simp only [map_equivCode, map_foCode, j.map_orCode, map_impCode, map_negCode]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j φ, ?_, ?_⟩)))))
    · simpa only [j.map_succ] using hm hφ
    · simp only [map_equivCode, map_foCode, j.map_allCode, map_allCode]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j φ, ?_, ?_⟩)))))
    · simpa only [j.map_succ] using hm hφ
    · simp only [map_equivCode, map_foCode, j.map_existsCode, map_exsCode]

end EndExtension
end ZFVP.Infinitary.Internal
