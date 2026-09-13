import ZFVP.SetTheory.NaturalAddition
import ZFVP.SetTheory.FiniteCardinalArithmetic

/-! Natural addition as a definable relation: for naturals `m`, `j`, the sum `ordinalAdd m j` is
the unique natural equinumerous with the tagged disjoint union `m ⊔ j`. This makes statements
quantifying over both summands definable. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem natural_eq_of_cardEQ {n m : V} (hn : n ∈ (ω : V)) (hm : m ∈ (ω : V)) (h : n ≋ m) : n = m :=
  SetTheory.subset_antisymm (natural_subset_of_cardLE hn hm h.le) (natural_subset_of_cardLE hm hn h.ge)

theorem disjointUnion_succ_eq (m j : V) :
    disjointUnion m (succ j) = insert ⟨j, succ ∅⟩ₖ (disjointUnion m j) := by
  apply mem_ext
  intro z
  rw [mem_insert, mem_disjointUnion_iff, mem_disjointUnion_iff]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
    · rcases mem_succ_iff.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
  · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact Or.inr ⟨j, mem_succ_self j, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨b, mem_succ_iff.mpr (Or.inr hb), rfl⟩

theorem not_mem_disjointUnion_self (m j : V) : ⟨j, succ ∅⟩ₖ ∉ disjointUnion m j := by
  intro h
  rcases (mem_disjointUnion_iff _ _ _).mp h with ⟨a, _, he⟩ | ⟨b, hb, he⟩
  · exact succ_empty_ne_empty (kpair_inj he).2
  · obtain ⟨hbj, -⟩ := kpair_inj he
    rw [hbj] at hb
    exact mem_irrefl b hb

theorem disjointUnion_zero_cardEQ (m : V) : disjointUnion m (∅ : V) ≋ m := by
  constructor
  · refine cardLE_of_injective_map kpair.π₁ (by definability) ?_ ?_
    · intro z hz
      rcases (mem_disjointUnion_iff _ _ _).mp hz with ⟨a, ha, rfl⟩ | ⟨b, hb, -⟩
      · rw [kpair.π₁_kpair]; exact ha
      · exact (not_mem_empty hb).elim
    · intro z hz z' hz' h
      rcases (mem_disjointUnion_iff _ _ _).mp hz with ⟨a, _, rfl⟩ | ⟨b, hb, -⟩
      · rcases (mem_disjointUnion_iff _ _ _).mp hz' with ⟨a', _, rfl⟩ | ⟨b', hb', -⟩
        · simp only [kpair.π₁_kpair] at h
          rw [h]
        · exact (not_mem_empty hb').elim
      · exact (not_mem_empty hb).elim
  · refine cardLE_of_injective_map (fun x ↦ ⟨x, ∅⟩ₖ) (by definability) ?_ ?_
    · intro x hx
      exact (mem_disjointUnion_iff _ _ _).mpr (Or.inl ⟨x, hx, rfl⟩)
    · intro x _ y _ h
      exact (kpair_inj h).1

/-- The predicate `m + j ≋ m ⊔ j`. -/
def AddCardPred (m j : V) : Prop := ordinalAdd m j ≋ disjointUnion m j

instance addCardPred_definable (m : V) : ℒₛₑₜ-predicate[V] (AddCardPred m) := by
  unfold AddCardPred disjointUnion
  definability

/-- For naturals, the ordinal sum is equinumerous with the tagged disjoint union. -/
theorem ordinalAdd_natural_cardEQ {m j : V} (hm : m ∈ (ω : V)) (hj : j ∈ (ω : V)) :
    ordinalAdd m j ≋ disjointUnion m j := by
  have : IsOrdinal m := IsOrdinal.nat hm
  change AddCardPred m j
  apply naturalNumber_induction (AddCardPred m) (by definability) ?_ ?_ j hj
  · unfold AddCardPred
    rw [zero_def, ordinalAdd_zero]
    exact (disjointUnion_zero_cardEQ m).symm
  · intro j hj ih
    have : IsOrdinal j := IsOrdinal.nat hj
    unfold AddCardPred at ih ⊢
    rw [ordinalAdd_succ, disjointUnion_succ_eq]
    have hfresh : ordinalAdd m j ∉ ordinalAdd m j := mem_irrefl _
    have hfresh' := not_mem_disjointUnion_self m j
    constructor
    · have := cardLE_insert_fresh ih.le hfresh hfresh'
      simpa only [succ] using this
    · have := cardLE_insert_fresh ih.ge hfresh' hfresh
      simpa only [succ] using this

/-- The graph of natural addition. -/
def NatAddRel (p m j : V) : Prop := m ∈ (ω : V) ∧ j ∈ (ω : V) ∧ p = ordinalAdd m j

theorem natAddRel_iff (p m j : V) :
    NatAddRel p m j ↔ m ∈ (ω : V) ∧ j ∈ (ω : V) ∧ p ∈ (ω : V) ∧ disjointUnion m j ≋ p := by
  constructor
  · rintro ⟨hm, hj, rfl⟩
    exact ⟨hm, hj, ordinalAdd_natural hm hj, (ordinalAdd_natural_cardEQ hm hj).symm⟩
  · rintro ⟨hm, hj, hp, he⟩
    refine ⟨hm, hj, natural_eq_of_cardEQ hp (ordinalAdd_natural hm hj) ?_⟩
    exact he.symm.trans (ordinalAdd_natural_cardEQ hm hj).symm

instance natAddRel_definable : ℒₛₑₜ-relation₃[V] NatAddRel := by
  have h : ℒₛₑₜ-relation₃ (fun p m j : V ↦ m ∈ (ω : V) ∧ j ∈ (ω : V) ∧ p ∈ (ω : V) ∧
      disjointUnion m j ≋ p) := by
    unfold disjointUnion
    definability
  apply Language.Definable.of_iff h
  intro v
  exact natAddRel_iff (v 0) (v 1) (v 2)

theorem natAddRel_add {m j : V} (hm : m ∈ (ω : V)) (hj : j ∈ (ω : V)) : NatAddRel (ordinalAdd m j) m j :=
  ⟨hm, hj, rfl⟩

end ZFVP
