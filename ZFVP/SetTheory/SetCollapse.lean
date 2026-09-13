import ZFVP.SetTheory.FinitePartialFunctions
import ZFVP.SetTheory.FiniteNaturalSets

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def collapseConditions (A : V) : V := finitePartialFunctions ω A

noncomputable def collapseOrder (A : V) : V := reverseInclusionOrder (collapseConditions A)

instance collapseConditions_definable : ℒₛₑₜ-function₁[V] collapseConditions := by
  unfold collapseConditions
  definability

instance collapseOrder_definable : ℒₛₑₜ-function₁[V] collapseOrder := by
  unfold collapseOrder
  definability

theorem collapse_poset (A : V) : IsForcingPoset (collapseConditions A) (collapseOrder A) :=
  reverseInclusionOrder_poset _

theorem collapse_top (A : V) : IsForcingTop (collapseConditions A) (collapseOrder A) ∅ :=
  finitePartialFunctions_top ω A

theorem collapse_domain_dense {A n : V} (hn : n ∈ (ω : V)) (hA : IsNonempty A) :
    ForcingDense (collapseConditions A) (collapseOrder A)
      {p ∈ collapseConditions A ; n ∈ domain p} := by
  obtain ⟨a, ha⟩ := hA.nonempty
  exact finitePartialFunctions_domain_dense hn ha

theorem collapse_range_dense {A a : V} (ha : a ∈ A) :
    ForcingDense (collapseConditions A) (collapseOrder A)
      {p ∈ collapseConditions A ; a ∈ range p} := by
  refine ⟨fun _ h ↦ (mem_sep_iff.mp h).1, ?_⟩
  intro p hp
  obtain ⟨n, hn, hnp⟩ := internallyFinite_fresh_natural
    ((mem_finitePartialFunctions ω A p).mp hp).2.2
  have hq := finitePartialFunction_insert hp hn ha hnp
  refine ⟨insert ⟨n, a⟩ₖ p, mem_sep_iff.mpr ⟨hq, ?_⟩,
    (pair_mem_reverseInclusionOrder _ _ _).mpr ⟨hq, hp, fun z hz ↦ mem_insert.mpr (Or.inr hz)⟩⟩
  exact mem_range_of_kpair_mem (show ⟨n, a⟩ₖ ∈ insert ⟨n, a⟩ₖ p by simp)

end ZFVP
