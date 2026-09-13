import ZFVP.Syntax.FormulaInversion
import ZFVP.SetTheory.MeasuredWellFounded

/-! Context-sensitive immediate subformulas decrease the rank of the formula code. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsImmediateSubformula (s t : V) : Prop :=
  (∃ n φ ψ, (t = ⟨n, andCode φ ψ⟩ₖ ∨ t = ⟨n, orCode φ ψ⟩ₖ) ∧
    (s = ⟨n, φ⟩ₖ ∨ s = ⟨n, ψ⟩ₖ)) ∨
  ∃ n φ, (t = ⟨n, allCode φ⟩ₖ ∨ t = ⟨n, existsCode φ⟩ₖ) ∧ s = ⟨succ n, φ⟩ₖ

instance isImmediateSubformula_definable : ℒₛₑₜ-relation[V] IsImmediateSubformula := by
  unfold IsImmediateSubformula
  definability

theorem immediateSubformula_rank {s t : V} (h : IsImmediateSubformula s t) :
    rank (kpair.π₂ s) ∈ rank (kpair.π₂ t) := by
  rcases h with ⟨n, φ, ψ, ht, hs⟩ | ⟨n, φ, ht, rfl⟩
  · have hφ : rank φ ∈ rank ⟨φ, ψ⟩ₖ := rank_kpair_left_lt φ ψ
    have hψ : rank ψ ∈ rank ⟨φ, ψ⟩ₖ := rank_kpair_right_lt φ ψ
    rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using
        IsOrdinal.toIsTransitive.mem_trans hφ (rank_kpair_right_lt (4 : V) ⟨φ, ψ⟩ₖ)
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using
        IsOrdinal.toIsTransitive.mem_trans hψ (rank_kpair_right_lt (4 : V) ⟨φ, ψ⟩ₖ)
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using
        IsOrdinal.toIsTransitive.mem_trans hφ (rank_kpair_right_lt (5 : V) ⟨φ, ψ⟩ₖ)
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using
        IsOrdinal.toIsTransitive.mem_trans hψ (rank_kpair_right_lt (5 : V) ⟨φ, ψ⟩ₖ)
  · rcases ht with rfl | rfl
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using rank_kpair_right_lt (6 : V) φ
    · simpa only [kpair.π₂_kpair, andCode, orCode, allCode, existsCode] using rank_kpair_right_lt (7 : V) φ

noncomputable def subformulaRelation (F : V) : V :=
  {p ∈ F ×ˢ F ; IsImmediateSubformula (kpair.π₁ p) (kpair.π₂ p)}

theorem kpair_mem_subformulaRelation_iff (F s t : V) :
    ⟨s, t⟩ₖ ∈ subformulaRelation F ↔ s ∈ F ∧ t ∈ F ∧ IsImmediateSubformula s t := by
  simp [subformulaRelation, and_assoc]

instance subformulaRelation_definable : ℒₛₑₜ-function₁[V] subformulaRelation := by
  have h : ℒₛₑₜ-relation (fun R F : V ↦ ∀ p, p ∈ R ↔
      p ∈ F ×ˢ F ∧ IsImmediateSubformula (kpair.π₁ p) (kpair.π₂ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = subformulaRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp [subformulaRelation]

theorem subformulaRelation_wellFounded (F : V) : IsInternallyWellFounded (subformulaRelation F) F := by
  apply projectedRank_internallyWellFounded _ _ kpair.π₂ (by definability)
  intro s _ t _ hst
  exact immediateSubformula_rank ((kpair_mem_subformulaRelation_iff F s t).mp hst).2.2

theorem immediateSubformula_mem_family {L Γ s t : V} (hL : IsLanguageCode L)
    (ht : t ∈ formulaFamily L Γ) (hst : IsImmediateSubformula s t) : s ∈ formulaFamily L Γ := by
  rcases hst with ⟨n, φ, ψ, htcode, hscode⟩ | ⟨n, φ, htcode, rfl⟩
  · rcases htcode with rfl | rfl
    · have h := (andCode_mem_iff hL).mp ((mem_formulaSet_iff _ _ _ _).mpr ht)
      rcases hscode with rfl | rfl
      · exact (mem_formulaSet_iff _ _ _ _).mp h.2.1
      · exact (mem_formulaSet_iff _ _ _ _).mp h.2.2
    · have h := (orCode_mem_iff hL).mp ((mem_formulaSet_iff _ _ _ _).mpr ht)
      rcases hscode with rfl | rfl
      · exact (mem_formulaSet_iff _ _ _ _).mp h.2.1
      · exact (mem_formulaSet_iff _ _ _ _).mp h.2.2
  · rcases htcode with rfl | rfl
    · have h := (allCode_mem_iff hL).mp ((mem_formulaSet_iff _ _ _ _).mpr ht)
      exact (mem_formulaSet_iff _ _ _ _).mp h.2
    · have h := (existsCode_mem_iff hL).mp ((mem_formulaSet_iff _ _ _ _).mpr ht)
      exact (mem_formulaSet_iff _ _ _ _).mp h.2

theorem subformulaRelation_mem_iff {L Γ s t : V} (hL : IsLanguageCode L)
    (ht : t ∈ formulaFamily L Γ) :
    ⟨s, t⟩ₖ ∈ subformulaRelation (formulaFamily L Γ) ↔ IsImmediateSubformula s t := by
  rw [kpair_mem_subformulaRelation_iff]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨immediateSubformula_mem_family hL ht h, ht, h⟩⟩

end ZFVP

