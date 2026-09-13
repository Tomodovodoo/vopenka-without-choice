import ZFVP.ModelTheory.SchmerlInternalBooleanAxioms
import ZFVP.ModelTheory.SchmerlInternalQuantifierLaws

/-! Universal closure and monotonicity schemas for existential and internal
uncountability quantifiers. Axiom recognition is a predicate on actual
internal formula codes. These schemas alone are not the full calculus. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def allCode (φ : V) : V := negCode (exsCode (negCode φ))

instance allCode_definable : ℒₛₑₜ-function₁[V] allCode := by unfold allCode; definability

theorem IsFragment.exs_mem {L F n φ : V} (hF : IsFragment L F)
    (h : ⟨n, exsCode φ⟩ₖ ∈ F) : ⟨succ n, φ⟩ₖ ∈ F :=
  hF.immediate_mem h ((immediate_exs_iff _ _ _).mpr rfl)

theorem IsFragment.q_mem {L F n φ : V} (hF : IsFragment L F)
    (h : ⟨n, qCode φ⟩ₖ ∈ F) : ⟨succ n, φ⟩ₖ ∈ F :=
  hF.immediate_mem h ((immediate_q_iff _ _ _).mpr rfl)

theorem IsFragment.all_mem {L F n φ : V} (hF : IsFragment L F)
    (h : ⟨n, allCode φ⟩ₖ ∈ F) : ⟨succ n, φ⟩ₖ ∈ F :=
  hF.neg_mem (hF.exs_mem (hF.neg_mem h))

theorem holds_all {L F M n φ b : V} (hF : IsFragment L F)
    (h : ⟨n, allCode φ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (allCode φ) b ↔
      ∀ x ∈ structureDomain M, Holds L F M (succ n) φ (assignmentPrepend n b x) := by
  rw [allCode, holds_neg hF h hb, holds_exs hF (hF.neg_mem h) hb]
  have hchild := hF.exs_mem (hF.neg_mem h)
  have hn := (hF.node h).1
  simp only [not_exists, not_and]
  apply forall₂_congr
  intro x hx
  rw [holds_neg hF hchild (assignmentPrepend_mem_function hn hb hx)]
  exact not_not

def IsQuantifierMonotonicityAxiom (χ : V) : Prop :=
  (∃ φ ψ, χ = impCode (allCode (impCode φ ψ)) (impCode (exsCode φ) (exsCode ψ))) ∨
  ∃ φ ψ, χ = impCode (allCode (impCode φ ψ)) (impCode (qCode φ) (qCode ψ))

instance isQuantifierMonotonicityAxiom_definable :
    ℒₛₑₜ-predicate[V] IsQuantifierMonotonicityAxiom := by
  unfold IsQuantifierMonotonicityAxiom
  definability

theorem IsQuantifierMonotonicityAxiom.sound {L F M n χ b : V}
    (hχ : IsQuantifierMonotonicityAxiom χ) (hF : IsFragment L F)
    (ht : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) : Holds L F M n χ b := by
  have hn := (hF.node ht).1
  rcases hχ with ⟨φ, ψ, rfl⟩ | ⟨φ, ψ, rfl⟩
  · have hl := hF.imp_left_mem ht
    have hr := hF.imp_right_mem ht
    rw [holds_imp hF ht hb, holds_all hF hl hb, holds_imp hF hr hb,
      holds_exs hF (hF.imp_left_mem hr) hb, holds_exs hF (hF.imp_right_mem hr) hb]
    rintro h ⟨x, hx, hp⟩
    exact ⟨x, hx, (holds_imp hF (hF.all_mem hl)
      (assignmentPrepend_mem_function hn hb hx)).mp (h x hx) hp⟩
  · have hl := hF.imp_left_mem ht
    have hr := hF.imp_right_mem ht
    rw [holds_imp hF ht hb, holds_all hF hl hb, holds_imp hF hr hb,
      holds_q hF (hF.imp_left_mem hr) hb, holds_q hF (hF.imp_right_mem hr) hb]
    intro h hp
    apply internal_uncountable_mono ?_ hp
    intro x hx
    obtain ⟨hx, hpx⟩ := mem_sep_iff.mp hx
    apply mem_sep_iff.mpr
    refine ⟨hx, ?_⟩
    exact (holds_imp hF (hF.all_mem hl)
      (assignmentPrepend_mem_function hn hb hx)).mp (h x hx) hpx

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_allCode (φ : V) : j (allCode φ) = allCode (j φ) := by
  simp only [allCode, map_negCode, map_exsCode]

theorem quantifierMonotonicityAxiom_map {χ : V} (h : IsQuantifierMonotonicityAxiom χ) :
    IsQuantifierMonotonicityAxiom (j χ) := by
  rcases h with ⟨φ, ψ, rfl⟩ | ⟨φ, ψ, rfl⟩
  · exact Or.inl ⟨j φ, j ψ, by simp only [map_impCode, map_allCode, map_exsCode]⟩
  · exact Or.inr ⟨j φ, j ψ, by simp only [map_impCode, map_allCode, map_qCode]⟩

end EndExtension
end ZFVP.Infinitary.Internal
