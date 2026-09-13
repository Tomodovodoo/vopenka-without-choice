import ZFVP.ModelTheory.SchmerlInternalBooleanSyntax

/-! The six propositional and countable-conjunction axiom schemas of the
Boolean part of Keisler's calculus, as predicates on internal syntax. The two
Q schemas are added separately from this Boolean part. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsBooleanAxiom (χ : V) : Prop :=
  (∃ φ ψ, χ = impCode φ (impCode ψ φ)) ∨
  (∃ φ ψ θ, χ = impCode (impCode φ (impCode ψ θ))
    (impCode (impCode φ ψ) (impCode φ θ))) ∨
  (∃ φ, χ = impCode (negCode (negCode φ)) φ) ∨
  (∃ φ ψ, χ = impCode (impCode (negCode φ) (negCode ψ)) (impCode ψ φ)) ∨
  (∃ f i, IsFunction f ∧ domain f = (ω : V) ∧ i ∈ (ω : V) ∧
    χ = impCode (conjCode f) (f ‘ i)) ∨
  ∃ φ f g, IsFunction f ∧ domain f = (ω : V) ∧ IsFunction g ∧ domain g = (ω : V) ∧
    (∀ i ∈ (ω : V), g ‘ i = impCode φ (f ‘ i)) ∧
    χ = impCode (conjCode g) (impCode φ (conjCode f))

instance isBooleanAxiom_definable : ℒₛₑₜ-predicate[V] IsBooleanAxiom := by
  unfold IsBooleanAxiom
  repeat' apply Language.Definable.or
  all_goals definability

theorem IsBooleanAxiom.sound {L F M n χ b : V} (hχ : IsBooleanAxiom χ)
    (hF : IsFragment L F) (ht : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n χ b := by
  rcases hχ with ⟨φ, ψ, rfl⟩ | ⟨φ, ψ, θ, rfl⟩ | ⟨φ, rfl⟩ |
    ⟨φ, ψ, rfl⟩ | ⟨f, i, _, _, hi, rfl⟩ | ⟨φ, f, g, _, _, _, _, hg, rfl⟩
  · rw [holds_imp hF ht hb, holds_imp hF (hF.imp_right_mem ht) hb]
    tauto
  · have hl := hF.imp_left_mem ht
    have hr := hF.imp_right_mem ht
    rw [holds_imp hF ht hb, holds_imp hF hl hb,
      holds_imp hF (hF.imp_right_mem hl) hb, holds_imp hF hr hb,
      holds_imp hF (hF.imp_left_mem hr) hb, holds_imp hF (hF.imp_right_mem hr) hb]
    tauto
  · have hl := hF.imp_left_mem ht
    rw [holds_imp hF ht hb, holds_neg hF hl hb, holds_neg hF (hF.neg_mem hl) hb]
    tauto
  · have hl := hF.imp_left_mem ht
    have hr := hF.imp_right_mem ht
    rw [holds_imp hF ht hb, holds_imp hF hl hb,
      holds_neg hF (hF.imp_left_mem hl) hb, holds_neg hF (hF.imp_right_mem hl) hb,
      holds_imp hF hr hb]
    tauto
  · rw [holds_imp hF ht hb, holds_conj hF (hF.imp_left_mem ht) hb]
    exact fun h ↦ h i hi
  · have hl := hF.imp_left_mem ht
    have hr := hF.imp_right_mem ht
    rw [holds_imp hF ht hb, holds_conj hF hl hb, holds_imp hF hr hb,
      holds_conj hF (hF.imp_right_mem hr) hb]
    intro hh hφ i hi
    have hiF := (hF.conj_data hl).2.2 i hi
    rw [hg i hi] at hiF
    have hhi := hh i hi
    rw [hg i hi, holds_imp hF hiF hb] at hhi
    exact hhi hφ

namespace EndExtension

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem booleanAxiom_map {χ : V} (hχ : IsBooleanAxiom χ) : IsBooleanAxiom (j χ) := by
  rcases hχ with ⟨φ, ψ, rfl⟩ | ⟨φ, ψ, θ, rfl⟩ | ⟨φ, rfl⟩ |
    ⟨φ, ψ, rfl⟩ | ⟨f, i, hf, hd, hi, rfl⟩ | ⟨φ, f, g, hf, hd, hg, hgd, hv, rfl⟩
  · exact Or.inl ⟨j φ, j ψ, by simp only [map_impCode]⟩
  · exact Or.inr (Or.inl ⟨j φ, j ψ, j θ, by simp only [map_impCode]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j φ, by simp only [map_impCode, map_negCode]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j φ, j ψ, by simp only [map_impCode, map_negCode]⟩)))
  · let := hf
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j f, j i, j.map_function f,
      ?_, (j.natural_iff i).mpr hi, ?_⟩))))
    · rw [← j.map_domain, hd, j.map_omega]
    · simp only [map_impCode, map_conjCode, j.map_value_total]
  · let := hf
    let := hg
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j φ, j f, j g,
      j.map_function f, ?_, j.map_function g, ?_, ?_, ?_⟩))))
    · rw [← j.map_domain, hd, j.map_omega]
    · rw [← j.map_domain, hgd, j.map_omega]
    · intro i hi
      rw [← j.map_omega] at hi
      obtain ⟨k, hk, rfl⟩ := j.endExtension ω i hi
      rw [← j.map_value_total, hv k hk, map_impCode, j.map_value_total]
    · simp only [map_impCode, map_conjCode]

end EndExtension
end ZFVP.Infinitary.Internal
