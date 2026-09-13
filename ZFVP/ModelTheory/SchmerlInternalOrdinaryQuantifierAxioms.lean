import ZFVP.ModelTheory.SchmerlInternalInstantiation
import ZFVP.ModelTheory.CodedSequentQuantifiers

/-! Universal distribution and vacuous generalization over internally finite
contexts. Weakening uses the actual successor-index graph. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def weakenCode (L H n φ : V) : V :=
  renameCode L H n (succ n) (successorIndices n) φ

instance weakenCode_definable : ℒₛₑₜ-function₄[V] weakenCode := by
  unfold weakenCode
  definability

theorem holds_weakenCode {L H F M n φ b x : V} (hH : IsFragment L H)
    (hF : IsFragment L F) (hM : IsStructureCode L M) (hn : n ∈ (ω : V))
    (hφ : ⟨n, φ⟩ₖ ∈ H) (hw : ⟨succ n, weakenCode L H n φ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) (hx : x ∈ structureDomain M) :
    Holds L F M (succ n) (weakenCode L H n φ) (assignmentPrepend n b x) ↔
      Holds L H M n φ b := by
  have hr := successorIndices_function hn
  have he := holds_renameCode hH hM hn (ω_succ_closed hn) hr hφ
    (assignmentPrepend_mem_function hn hb hx)
  rw [successorIndices_compose_prepend hn hb hx] at he
  exact (holds_fragment_iff hF (renamedFragment_valid hH hn (ω_succ_closed hn) hr)
    _ _ hw (renameCode_mem hφ) _).trans he

attribute [local aesop 4 (rule_sets := [Definability]) safe] Language.DefinableFunction₄.comp

def IsOrdinaryQuantifierAxiom (L n χ : V) : Prop := n ∈ (ω : V) ∧
  ((∃ φ ψ, χ = impCode (allCode (impCode φ ψ)) (impCode (allCode φ) (allCode ψ))) ∨
   ∃ H φ, IsFragment L H ∧ ⟨n, φ⟩ₖ ∈ H ∧ χ = impCode φ (allCode (weakenCode L H n φ)))

instance isOrdinaryQuantifierAxiom_definable : ℒₛₑₜ-relation₃[V] IsOrdinaryQuantifierAxiom := by
  unfold IsOrdinaryQuantifierAxiom
  definability

theorem IsOrdinaryQuantifierAxiom.sound {L F M n χ b : V}
    (hχ : IsOrdinaryQuantifierAxiom L n χ) (hF : IsFragment L F)
    (hM : IsStructureCode L M) (hc : ⟨n, χ⟩ₖ ∈ F) (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n χ b := by
  obtain ⟨hn, hχ⟩ := hχ
  rcases hχ with ⟨φ, ψ, rfl⟩ | ⟨H, φ, hH, hφ, rfl⟩
  · have hi := hF.imp_left_mem hc
    have hr := hF.imp_right_mem hc
    have ha := hF.imp_left_mem hr
    have hz := hF.imp_right_mem hr
    rw [holds_imp hF hc hb, holds_all hF hi hb, holds_imp hF hr hb,
      holds_all hF ha hb, holds_all hF hz hb]
    intro himp hall x hx
    exact (holds_imp hF (hF.all_mem hi) (assignmentPrepend_mem_function hn hb hx)).mp
      (himp x hx) (hall x hx)
  · have ha := hF.imp_right_mem hc
    rw [holds_imp hF hc hb, holds_all hF ha hb]
    intro hp x hx
    apply (holds_weakenCode hH hF hM hn hφ (hF.all_mem ha) hb hx).mpr
    exact (holds_fragment_iff hH hF _ _ hφ (hF.imp_left_mem hc) b).mpr hp

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem map_successorIndices (n : V) : j (successorIndices n) = successorIndices (j n) := by
  exact j.map_definableGraph n succ succ (by definability) (by definability)
    (fun i _ ↦ j.map_succ i)

theorem map_weakenCode {L H n : V} (hH : IsFragment L H) (hn : n ∈ (ω : V)) (φ : V) :
    j (weakenCode L H n φ) = weakenCode (j L) (j H) (j n) (j φ) := by
  rw [weakenCode, map_renameCode j hH hn (ω_succ_closed hn) (successorIndices_function hn),
    j.map_succ, map_successorIndices]
  rfl

theorem ordinaryQuantifierAxiom_map {L n χ : V} (hχ : IsOrdinaryQuantifierAxiom L n χ) :
    IsOrdinaryQuantifierAxiom (j L) (j n) (j χ) := by
  obtain ⟨hn, hχ⟩ := hχ
  refine ⟨(j.natural_iff _).mpr hn, ?_⟩
  rcases hχ with ⟨φ, ψ, rfl⟩ | ⟨H, φ, hH, hφ, rfl⟩
  · exact Or.inl ⟨j φ, j ψ, by simp only [map_impCode, map_allCode]⟩
  · refine Or.inr ⟨j H, j φ, fragment_map j hH, ?_, ?_⟩
    · simpa only [j.map_kpair] using (j.mem_iff _ _).mpr hφ
    · rw [map_impCode, map_allCode, map_weakenCode j hH hn]

end EndExtension
end ZFVP.Infinitary.Internal
