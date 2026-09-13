import ZFVP.ModelTheory.NormalizedBaseTwoStep
import ZFVP.SetTheory.ForcingThreadAction
import ZFVP.SetTheory.AtomicForcingDictionary

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local instance : ℒₛₑₜ-function₄[V] atomicEquality := atomicEqualityFormula_defined.to_definable
local instance : ℒₛₑₜ-function₄[V] atomicMembership := atomicMembershipFormula_defined.to_definable

attribute [local aesop 5 (rule_sets := [Definability]) safe]
  Language.DefinableFunction₄.comp Language.DefinableFunction₅.comp

instance forcingScottRelated_uniform_definable : ℒₛₑₜ-relation₅[V] ForcingScottRelated := by
  have hf : Language.DefinableFunction ℒₛₑₜ (fun v : Fin 5 → V ↦ atomicEquality (v 0) (v 1) (v 3) (v 4)) :=
    Language.DefinableFunction₄.comp (by definability) (by definability) (by definability) (by definability)
  change Language.Definable ℒₛₑₜ (fun v : Fin 5 → V ↦
    IsForcingName (v 0) (v 4) ∧ v 2 ∈ atomicEquality (v 0) (v 1) (v 3) (v 4))
  definability

private theorem scottRelated_comp {n : ℕ} {a b c d e : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) :
    Language.Definable ℒₛₑₜ (fun v ↦ ForcingScottRelated (a v) (b v) (c v) (d v) (e v)) :=
  Language.Definable.substitution (f := ![a, b, c, d, e]) forcingScottRelated_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he])

attribute [local aesop 5 (rule_sets := [Definability]) safe] scottRelated_comp

instance forcingLeastNameFamily_uniform_definable : ℒₛₑₜ-function₄[V] forcingLeastNameFamily := by
  have h : ℒₛₑₜ-relation₅[V] (fun X P R p τ ↦ ∀ σ, σ ∈ X ↔
      σ ∈ hierarchy (succ (rank τ)) ∧ ForcingScottRelated P R p τ σ ∧
        ∀ ν, ForcingScottRelated P R p τ ν → rank σ ⊆ rank ν) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingLeastNameFamily (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [forcingLeastNameFamily, mem_sep_iff]

instance forcingLeastRankName_uniform_definable : ℒₛₑₜ-function₄[V] forcingLeastRankName := by
  unfold forcingLeastRankName
  definability

instance forcingGuardedNormalization_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (forcingGuardedNormalization (V := V)) := by
  unfold forcingGuardedNormalization
  definability

instance boundedNameTwoStep_uniform_definable : ℒₛₑₜ-function₄[V] boundedNameTwoStep := by
  have h : ℒₛₑₜ-relation₅[V] (fun C P R δ Q ↦ ∀ z, z ∈ C ↔
      z ∈ P ×ˢ hierarchy δ ∧ IsForcingName P (kpair.π₂ z) ∧
        kpair.π₁ z ∈ atomicMembership P R (kpair.π₂ z) Q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = boundedNameTwoStep (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [boundedNameTwoStep, mem_sep_iff]

instance normalizedNamePool_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (normalizedNamePool (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun C P R one δ Q : V ↦ ∀ τ, τ ∈ C ↔
      τ ∈ hierarchy δ ∧ IsForcingName P τ ∧ forcingLeastRankName P R one τ = τ ∧
        one ∈ atomicMembership P R τ Q) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = normalizedNamePool (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [normalizedNamePool, mem_sep_iff]

instance normalizedNameTwoStep_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (normalizedNameTwoStep (V := V)) := by
  unfold normalizedNameTwoStep
  definability

instance guardedTwoStepCode_uniform_definable : ℒₛₑₜ-function₄[V] guardedTwoStepCode := by
  unfold guardedTwoStepCode
  definability

instance guardedTwoStepMap_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (guardedTwoStepMap (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun M P R one δ Q : V ↦ ∀ z, z ∈ M ↔
      ∃ x ∈ boundedNameTwoStep P R δ Q, z = ⟨x, guardedTwoStepCode P R one x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = guardedTwoStepMap (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [guardedTwoStepMap, mem_definableGraph_iff]

instance equivalentSuborderFix_uniform_definable : ℒₛₑₜ-function₃[V] equivalentSuborderFix := by
  have h : ℒₛₑₜ-relation₄[V] (fun y N f q ↦ (q ∈ N ∧ y = q) ∨ (q ∉ N ∧ y = f ‘ q)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = equivalentSuborderFix (v 1) (v 2) (v 3) ↔ _
  classical
  by_cases hv : v 3 ∈ v 1 <;> simp [equivalentSuborderFix, hv]

instance equivalentSuborderRetraction_uniform_definable : ℒₛₑₜ-function₃[V] equivalentSuborderRetraction := by
  have h : ℒₛₑₜ-relation₄[V] (fun r P N f ↦ ∀ z, z ∈ r ↔
      ∃ x ∈ P, z = ⟨x, equivalentSuborderFix N f x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = equivalentSuborderRetraction (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [equivalentSuborderRetraction, mem_definableGraph_iff]

instance normalizedTwoStepRetraction_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (normalizedTwoStepRetraction (V := V)) := by
  unfold normalizedTwoStepRetraction
  definability

instance retractedBaseTwoStepCode_uniform_definable : ℒₛₑₜ-function₂[V] retractedBaseTwoStepCode := by
  unfold retractedBaseTwoStepCode
  definability

instance retractedBaseTwoStepMap_uniform_definable : Language.DefinableFunction₅ ℒₛₑₜ (retractedBaseTwoStepMap (V := V)) := by
  have h : Language.DefinableRel₆ ℒₛₑₜ (fun f P R δ Q m : V ↦ ∀ z, z ∈ f ↔
      ∃ x ∈ boundedNameTwoStep P R δ Q, z = ⟨x, retractedBaseTwoStepCode m x⟩ₖ) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = retractedBaseTwoStepMap (v 1) (v 2) (v 3) (v 4) (v 5) ↔ _
  rw [mem_ext_iff]
  simp only [retractedBaseTwoStepMap, mem_definableGraph_iff]

instance normalizedBaseTwoStepMap_uniform_definable :
    Language.DefinableFunction ℒₛₑₜ (fun v : Fin 8 → V ↦
      normalizedBaseTwoStepMap (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) := by
  unfold normalizedBaseTwoStepMap
  definability

theorem normalizedBaseTwoStepMap_comp {n : ℕ} {a b c d e f g h : (Fin n → V) → V}
    (ha : Language.DefinableFunction ℒₛₑₜ a) (hb : Language.DefinableFunction ℒₛₑₜ b)
    (hc : Language.DefinableFunction ℒₛₑₜ c) (hd : Language.DefinableFunction ℒₛₑₜ d)
    (he : Language.DefinableFunction ℒₛₑₜ e) (hf : Language.DefinableFunction ℒₛₑₜ f)
    (hg : Language.DefinableFunction ℒₛₑₜ g) (hh : Language.DefinableFunction ℒₛₑₜ h) :
    Language.DefinableFunction ℒₛₑₜ (fun v ↦ normalizedBaseTwoStepMap
      (a v) (b v) (c v) (d v) (e v) (f v) (g v) (h v)) :=
  Language.DefinableFunction.substitution (f := ![a, b, c, d, e, f, g, h])
    normalizedBaseTwoStepMap_uniform_definable
    (by simp [Fin.forall_fin_iff_zero_and_forall_succ, ha, hb, hc, hd, he, hf, hg, hh])

instance forcingThreadActionMap_uniform_definable : ℒₛₑₜ-function₃[V] forcingThreadActionMap := by
  have h : ℒₛₑₜ-relation₄[V] (fun r θ m C ↦ ∀ z, z ∈ r ↔ ∃ f ∈ C, z = ⟨f, forcingThreadAction θ m f⟩ₖ) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = forcingThreadActionMap (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [forcingThreadActionMap, mem_definableGraph_iff]

end ZFVP
