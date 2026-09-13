import ZFVP.Syntax.EndExtensionFormulas
import ZFVP.SetTheory.EndExtensionRelations

/-! Immediate subformulas and their predecessor sets agree across end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem immediateSubformula_iff_components (s t : V) :
    IsImmediateSubformula s t ↔
      ((t = ⟨kpair.π₁ t, andCode (kpair.π₁ (kpair.π₂ (kpair.π₂ t))) (kpair.π₂ (kpair.π₂ (kpair.π₂ t)))⟩ₖ ∨
        t = ⟨kpair.π₁ t, orCode (kpair.π₁ (kpair.π₂ (kpair.π₂ t))) (kpair.π₂ (kpair.π₂ (kpair.π₂ t)))⟩ₖ) ∧
        (s = ⟨kpair.π₁ t, kpair.π₁ (kpair.π₂ (kpair.π₂ t))⟩ₖ ∨
          s = ⟨kpair.π₁ t, kpair.π₂ (kpair.π₂ (kpair.π₂ t))⟩ₖ)) ∨
      ((t = ⟨kpair.π₁ t, allCode (kpair.π₂ (kpair.π₂ t))⟩ₖ ∨
        t = ⟨kpair.π₁ t, existsCode (kpair.π₂ (kpair.π₂ t))⟩ₖ) ∧
        s = ⟨succ (kpair.π₁ t), kpair.π₂ (kpair.π₂ t)⟩ₖ) := by
  constructor
  · rintro (⟨n, φ, ψ, ht, hs⟩ | ⟨n, φ, ht, hs⟩)
    · rcases ht with rfl | rfl <;> rcases hs with rfl | rfl <;>
        simp only [andCode, orCode, kpair.π₁_kpair, kpair.π₂_kpair] <;> tauto
    · rcases ht with rfl | rfl <;> subst s <;>
        simp only [allCode, existsCode, kpair.π₁_kpair, kpair.π₂_kpair] <;> tauto
  · rintro (⟨ht, hs⟩ | ⟨ht, hs⟩)
    · exact Or.inl ⟨kpair.π₁ t, kpair.π₁ (kpair.π₂ (kpair.π₂ t)),
        kpair.π₂ (kpair.π₂ (kpair.π₂ t)), ht, hs⟩
    · exact Or.inr ⟨kpair.π₁ t, kpair.π₂ (kpair.π₂ t), ht, hs⟩

theorem subformulaPredecessors_eq {F p : V} (hp : p ∈ F) :
    predecessors (subformulaRelation F) F p = {s ∈ F ; IsImmediateSubformula s p} := by
  apply mem_ext
  intro s
  simp only [mem_predecessors_iff, kpair_mem_subformulaRelation_iff, mem_sep_iff, hp]
  tauto

namespace MembershipEndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem immediateSubformula_iff (j : MembershipEndExtension V W) (s t : V) :
    IsImmediateSubformula (j s) (j t) ↔ IsImmediateSubformula s t := by
  rw [immediateSubformula_iff_components, immediateSubformula_iff_components]
  simp only [← j.map_first, ← j.map_second, ← j.map_andCode, ← j.map_orCode,
    ← j.map_allCode, ← j.map_existsCode, ← j.map_succ, ← j.map_kpair, j.injective.eq_iff]

theorem map_formulaPredecessors (j : MembershipEndExtension V W) {L Γ p : V}
    (hL : IsLanguageCode L) (hp : p ∈ formulaFamily L Γ) :
    j (predecessors (subformulaRelation (formulaFamily L Γ)) (formulaFamily L Γ) p) =
      predecessors (subformulaRelation (formulaFamily (j L) (j Γ))) (formulaFamily (j L) (j Γ)) (j p) := by
  have hp' : j p ∈ formulaFamily (j L) (j Γ) := by
    rw [← j.map_formulaFamily hL Γ]; exact (j.mem_iff _ _).mpr hp
  rw [subformulaPredecessors_eq hp, subformulaPredecessors_eq hp']
  have he := j.map_separation (formulaFamily L Γ) (fun s ↦ IsImmediateSubformula s p)
    (fun s ↦ IsImmediateSubformula s (j p)) (by definability) (by definability)
    (fun s _ ↦ (j.immediateSubformula_iff s p).symm)
  simpa only [j.map_formulaFamily hL Γ] using he

end MembershipEndExtension
end ZFVP
