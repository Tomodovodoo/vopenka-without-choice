import ZFVP.Syntax.Subformulas
import ZFVP.Syntax.EndExtensionSatisfaction

/-! Internal codes for countable infinitary fragments. A conjunction carries
an actual function on the model's omega. Context/code pairs and their entire
subformula family are internal sets; Foundation supplies the recursion order. -/

namespace ZFVP.Infinitary.Internal

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def foCode (φ : V) : V := ⟨(0 : V), φ⟩ₖ
noncomputable def negCode (φ : V) : V := ⟨(1 : V), φ⟩ₖ
noncomputable def conjCode (f : V) : V := ⟨(2 : V), f⟩ₖ
noncomputable def exsCode (φ : V) : V := ⟨(3 : V), φ⟩ₖ
noncomputable def qCode (φ : V) : V := ⟨(4 : V), φ⟩ₖ

instance foCode_definable : ℒₛₑₜ-function₁[V] foCode := by unfold foCode; definability
instance negCode_definable : ℒₛₑₜ-function₁[V] negCode := by unfold negCode; definability
instance conjCode_definable : ℒₛₑₜ-function₁[V] conjCode := by unfold conjCode; definability
instance exsCode_definable : ℒₛₑₜ-function₁[V] exsCode := by unfold exsCode; definability
instance qCode_definable : ℒₛₑₜ-function₁[V] qCode := by unfold qCode; definability

def IsNode (L F n φ : V) : Prop := n ∈ (ω : V) ∧
  ((∃ ψ ∈ formulaSet L ∅ n, φ = foCode ψ) ∨
    (∃ ψ, φ = negCode ψ ∧ ⟨n, ψ⟩ₖ ∈ F) ∨
    (∃ f, IsFunction f ∧ domain f = (ω : V) ∧ φ = conjCode f ∧
      ∀ i ∈ (ω : V), ⟨n, f ‘ i⟩ₖ ∈ F) ∨
    (∃ ψ, φ = exsCode ψ ∧ ⟨succ n, ψ⟩ₖ ∈ F) ∨
    ∃ ψ, φ = qCode ψ ∧ ⟨succ n, ψ⟩ₖ ∈ F)

instance isNode_definable : ℒₛₑₜ-relation₄[V] IsNode := by
  unfold IsNode
  definability

def IsFragment (L F : V) : Prop := IsLanguageCode L ∧ ∀ t ∈ F,
  t = ⟨kpair.π₁ t, kpair.π₂ t⟩ₖ ∧ IsNode L F (kpair.π₁ t) (kpair.π₂ t)

instance isFragment_definable : ℒₛₑₜ-relation[V] IsFragment := by
  unfold IsFragment
  definability

theorem IsFragment.node {L F n φ : V} (h : IsFragment L F) (ht : ⟨n, φ⟩ₖ ∈ F) :
    IsNode L F n φ := by
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using (h.2 _ ht).2

def IsImmediate (s t : V) : Prop :=
  (∃ n φ, t = ⟨n, negCode φ⟩ₖ ∧ s = ⟨n, φ⟩ₖ) ∨
    (∃ n f i, IsFunction f ∧ i ∈ domain f ∧
      t = ⟨n, conjCode f⟩ₖ ∧ s = ⟨n, f ‘ i⟩ₖ) ∨
    ∃ n φ, (t = ⟨n, exsCode φ⟩ₖ ∨ t = ⟨n, qCode φ⟩ₖ) ∧ s = ⟨succ n, φ⟩ₖ

instance isImmediate_definable : ℒₛₑₜ-relation[V] IsImmediate := by
  unfold IsImmediate
  definability

theorem immediate_rank {s t : V} (h : IsImmediate s t) :
    rank (kpair.π₂ s) ∈ rank (kpair.π₂ t) := by
  rcases h with ⟨n, φ, rfl, rfl⟩ | ⟨n, f, i, hf, hi, rfl, rfl⟩ | ⟨n, φ, ht, rfl⟩
  · simpa only [kpair.π₂_kpair, negCode] using rank_kpair_right_lt (1 : V) φ
  · let := hf
    have hri : rank (f ‘ i) ∈ rank f := rank_lt_of_mem_range
      (mem_range_of_kpair_mem (kpair_value_mem hi))
    simpa only [kpair.π₂_kpair, conjCode] using
      IsOrdinal.toIsTransitive.mem_trans hri (rank_kpair_right_lt (2 : V) f)
  · rcases ht with rfl | rfl
    · simpa only [kpair.π₂_kpair, exsCode] using rank_kpair_right_lt (3 : V) φ
    · simpa only [kpair.π₂_kpair, qCode] using rank_kpair_right_lt (4 : V) φ

noncomputable def immediateRelation (F : V) : V :=
  {a ∈ F ×ˢ F ; IsImmediate (kpair.π₁ a) (kpair.π₂ a)}

theorem pair_mem_immediateRelation (F s t : V) :
    ⟨s, t⟩ₖ ∈ immediateRelation F ↔ s ∈ F ∧ t ∈ F ∧ IsImmediate s t := by
  simp only [immediateRelation, mem_sep_iff, kpair_mem_iff,
    kpair.π₁_kpair, kpair.π₂_kpair, and_assoc]

instance immediateRelation_definable : ℒₛₑₜ-function₁[V] immediateRelation := by
  have h : ℒₛₑₜ-relation[V] (fun R F ↦ ∀ a,
      a ∈ R ↔ a ∈ F ×ˢ F ∧ IsImmediate (kpair.π₁ a) (kpair.π₂ a)) := by
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = immediateRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [immediateRelation, mem_sep_iff]

theorem immediateRelation_wellFounded (F : V) : IsInternallyWellFounded (immediateRelation F) F := by
  apply projectedRank_internallyWellFounded _ _ kpair.π₂ (by definability)
  intro s _ t _ hst
  exact immediate_rank ((pair_mem_immediateRelation F s t).mp hst).2.2

theorem immediate_fo_iff (s n φ : V) : ¬IsImmediate s ⟨n, foCode φ⟩ₖ := by
  unfold foCode
  simp [IsImmediate, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem immediate_neg_iff (s n φ : V) :
    IsImmediate s ⟨n, negCode φ⟩ₖ ↔ s = ⟨n, φ⟩ₖ := by
  simp [IsImmediate, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem immediate_conj_iff (s n f : V) :
    IsImmediate s ⟨n, conjCode f⟩ₖ ↔
      IsFunction f ∧ ∃ i ∈ domain f, s = ⟨n, f ‘ i⟩ₖ := by
  simp [IsImmediate, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem immediate_exs_iff (s n φ : V) :
    IsImmediate s ⟨n, exsCode φ⟩ₖ ↔ s = ⟨succ n, φ⟩ₖ := by
  simp [IsImmediate, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff]

theorem immediate_q_iff (s n φ : V) :
    IsImmediate s ⟨n, qCode φ⟩ₖ ↔ s = ⟨succ n, φ⟩ₖ := by
  simp [IsImmediate, negCode, conjCode, exsCode, qCode, OfNat.ofNat, internalNumeral_eq_iff]

end ZFVP.Infinitary.Internal
