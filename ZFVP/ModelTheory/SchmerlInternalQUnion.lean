import ZFVP.ModelTheory.SchmerlInternalQuantifierAxioms

/-! The internal Q countable-union schema. All three formula sequences
are actual functions on the model's entire omega. Soundness uses internal
Choice and internal countable unions, with no standard-omega assumption. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem holds_disjunction {L F M n f g b : V} (hF : IsFragment L F)
    (ht : ⟨n, negCode (conjCode g)⟩ₖ ∈ F)
    (hg : ∀ i ∈ (ω : V), g ‘ i = negCode (f ‘ i))
    (hb : b ∈ structureDomain M ^ n) :
    Holds L F M n (negCode (conjCode g)) b ↔
      ∃ i ∈ (ω : V), Holds L F M n (f ‘ i) b := by
  classical
  rw [holds_neg hF ht hb, holds_conj hF (hF.neg_mem ht) hb]
  have hiF (i : V) (hi : i ∈ (ω : V)) : ⟨n, negCode (f ‘ i)⟩ₖ ∈ F := by
    simpa only [hg i hi] using (hF.conj_data (hF.neg_mem ht)).2.2 i hi
  constructor
  · intro h
    by_contra hh
    apply h
    intro i hi
    rw [hg i hi, holds_neg hF (hiF i hi) hb]
    exact fun hp ↦ hh ⟨i, hi, hp⟩
  · rintro ⟨i, hi, hp⟩ hh
    have hn := hh i hi
    rw [hg i hi, holds_neg hF (hiF i hi) hb] at hn
    exact hn hp

def IsQUnionAxiom (χ : V) : Prop := ∃ f g h,
  IsFunction f ∧ domain f = (ω : V) ∧ IsFunction g ∧ domain g = (ω : V) ∧
  IsFunction h ∧ domain h = (ω : V) ∧
  (∀ i ∈ (ω : V), g ‘ i = negCode (f ‘ i) ∧ h ‘ i = negCode (qCode (f ‘ i))) ∧
  χ = impCode (qCode (negCode (conjCode g))) (negCode (conjCode h))

instance isQUnionAxiom_definable : ℒₛₑₜ-predicate[V] IsQUnionAxiom := by
  unfold IsQUnionAxiom
  definability

theorem exists_qUnionAxiom (f : V) (hf : IsFunction f) (hd : domain f = (ω : V)) :
    ∃ g h, IsQUnionAxiom (impCode (qCode (negCode (conjCode g))) (negCode (conjCode h))) ∧
      ∀ i ∈ (ω : V), g ‘ i = negCode (f ‘ i) ∧ h ‘ i = negCode (qCode (f ‘ i)) := by
  let g := definableGraph (ω : V) (fun i ↦ negCode (f ‘ i)) (by definability)
  let h := definableGraph (ω : V) (fun i ↦ negCode (qCode (f ‘ i))) (by definability)
  have hv : ∀ i ∈ (ω : V), g ‘ i = negCode (f ‘ i) ∧ h ‘ i = negCode (qCode (f ‘ i)) := by
    intro i hi
    exact ⟨value_definableGraph _ _ _ hi, value_definableGraph _ _ _ hi⟩
  refine ⟨g, h, ?_, hv⟩
  exact ⟨f, g, h, hf, hd, inferInstance, domain_definableGraph _ _ _,
    inferInstance, domain_definableGraph _ _ _, hv, rfl⟩

theorem IsQUnionAxiom.sound {L F M n χ b : V} (hχ : IsQUnionAxiom χ)
    (hAC : InternalChoice V) (hF : IsFragment L F) (ht : ⟨n, χ⟩ₖ ∈ F)
    (hb : b ∈ structureDomain M ^ n) : Holds L F M n χ b := by
  classical
  obtain ⟨f, g, h, _, _, _, _, _, _, hval, rfl⟩ := hχ
  have hl := hF.imp_left_mem ht
  have hr := hF.imp_right_mem ht
  have hdisj := hF.q_mem hl
  have hn := (hF.node ht).1
  let R : V → V → Prop := fun i x ↦
    Holds L F M (succ n) (f ‘ i) (assignmentPrepend n b x)
  have hR : ℒₛₑₜ-relation R := by unfold R Holds; definability
  let := hR
  have he : witnessFiber M n b (truthGraph L F M) (negCode (conjCode g)) =
      {x ∈ structureDomain M ; ∃ i ∈ (ω : V), R i x} := by
    apply mem_ext
    intro x
    simp only [witnessFiber, mem_sep_iff]
    apply and_congr_right
    intro hx
    exact holds_disjunction hF hdisj (fun i hi ↦ (hval i hi).1)
      (assignmentPrepend_mem_function hn hb hx)
  rw [holds_imp hF ht hb, holds_q hF hl hb, he]
  intro hbig
  obtain ⟨i, hi, hbig⟩ := internal_uncountable_exists_nat hAC (structureDomain M) R hR hbig
  apply (holds_neg hF hr hb).mpr
  intro hall
  have hiF := (hF.conj_data (hF.neg_mem hr)).2.2 i hi
  rw [(hval i hi).2] at hiF
  have hnot := (holds_conj hF (hF.neg_mem hr) hb).mp hall i hi
  rw [(hval i hi).2, holds_neg hF hiF hb, holds_q hF (hF.neg_mem hiF) hb] at hnot
  exact hnot hbig

namespace EndExtension
variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
  (j : MembershipEndExtension V W)

theorem qUnionAxiom_map {χ : V} (hχ : IsQUnionAxiom χ) : IsQUnionAxiom (j χ) := by
  obtain ⟨f, g, h, hf, hfd, hg, hgd, hh, hhd, hv, rfl⟩ := hχ
  let := hf
  let := hg
  let := hh
  refine ⟨j f, j g, j h, j.map_function f, ?_, j.map_function g, ?_, j.map_function h, ?_, ?_, ?_⟩
  · rw [← j.map_domain, hfd, j.map_omega]
  · rw [← j.map_domain, hgd, j.map_omega]
  · rw [← j.map_domain, hhd, j.map_omega]
  · intro i hi
    rw [← j.map_omega] at hi
    obtain ⟨k, hk, rfl⟩ := j.endExtension ω i hi
    constructor
    · rw [← j.map_value_total, (hv k hk).1, map_negCode, j.map_value_total]
    · rw [← j.map_value_total, (hv k hk).2, map_negCode, map_qCode, j.map_value_total]
  · simp only [map_impCode, map_qCode, map_negCode, map_conjCode]

end EndExtension
end ZFVP.Infinitary.Internal
