import ZFVP.ModelTheory.WoodinQuotientBoundRecursion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem woodinQuotientBoundHistory_table (θ i p f j : V) :
    IsIterationTable j (woodinQuotientBoundHistory θ i p f j) := by
  unfold woodinQuotientBoundHistory
  exact ⟨inferInstance, domain_definableGraph _ _ _⟩

theorem woodinQuotientBoundHistory_value {θ i p f j k : V} (hk : k ∈ j) :
    (woodinQuotientBoundHistory θ i p f j) ‘ k = woodinQuotientBoundRec θ i p f k :=
  value_definableGraph _ _ _ hk

theorem woodinQuotientBoundHistory_extends {θ i p f j k : V} (hjk : j ⊆ k) :
    woodinQuotientBoundHistory θ i p f j ⊆ woodinQuotientBoundHistory θ i p f k := by
  apply (woodinQuotientBoundHistory_table θ i p f j).subset_of_values
    (woodinQuotientBoundHistory_table θ i p f k) hjk
  intro l hl
  rw [woodinQuotientBoundHistory_value hl, woodinQuotientBoundHistory_value (hjk l hl)]

private theorem after_base {i j : V} [IsOrdinal j] (hi : i ∈ j) : j ≠ i ∧ j ∉ i := by
  constructor
  · rintro rfl
    exact mem_irrefl _ hi
  · intro hji
    exact mem_irrefl j (IsOrdinal.toIsTransitive.mem_trans hji hi)

theorem woodinQuotientBoundRec_successor {θ i p f k : V} [IsOrdinal k] (hi : i ∈ succ k) :
    woodinQuotientBoundRec θ i p f (succ k) =
      ⟨woodinQuotientBoundRec θ i p f k, woodinBoundSuccessorTail θ i p f k⟩ₖ := by
  have hn := after_base hi
  rw [woodinQuotientBoundRec_rule]
  simp only [woodinQuotientBoundRule, ite_eq_right hn.1, ite_eq_right hn.2,
    sUnion_succ_of_transitive, ite_true, woodinQuotientBoundHistory_value (mem_succ_self k)]

theorem woodinQuotientBoundRec_direct {θ i p f j : V} [IsOrdinal j]
    (hi : i ∈ j) (hs : j ≠ succ (⋃ˢ j))
    (hinac : IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    woodinQuotientBoundRec θ i p f j = woodinQuotientBoundHistory θ i p f j := by
  have hn := after_base hi
  rw [woodinQuotientBoundRec_rule]
  simp only [woodinQuotientBoundRule, ite_eq_right hn.1, ite_eq_right hn.2,
    ite_eq_right hs, ite_eq_left hinac]

theorem woodinQuotientBoundRec_inverse {θ i p f j : V} [IsOrdinal j]
    (hi : i ∈ j) (hs : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    woodinQuotientBoundRec θ i p f j =
      ⟨woodinQuotientBoundHistory θ i p f j, woodinBoundInverseTail θ i p f j⟩ₖ := by
  have hn := after_base hi
  rw [woodinQuotientBoundRec_rule]
  simp only [woodinQuotientBoundRule, ite_eq_right hn.1, ite_eq_right hn.2,
    ite_eq_right hs, ite_eq_right hinac]

end ZFVP
