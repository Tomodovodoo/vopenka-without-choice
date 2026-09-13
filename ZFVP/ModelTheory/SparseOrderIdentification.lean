import ZFVP.ModelTheory.SparseOrderCoordinates

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def sparseRecoveredOrder (S : V) : V := sparseCarrierOrder S (succ (rank S))

instance sparseRecoveredOrder_definable : ℒₛₑₜ-function₁[V] sparseRecoveredOrder := by
  unfold sparseRecoveredOrder
  definability

theorem sparseCarrierOrder_subset {S a : V} [IsOrdinal a] :
    sparseCarrierOrder S a ⊆ sparseCarrierCut S a ×ˢ sparseCarrierCut S a := by
  intro z hz
  rw [sparseCarrierOrder_eq] at hz
  have hh := (mem_sep_iff.mp hz).1
  simpa only [sparseCarrierOrderTable, domain_definableGraph] using hh

theorem sparseCarrierOrder_eq_cut_of_coordinates {S R a : V} [IsOrdinal a]
    (hcoord : ∀ b : V, IsOrdinal b → ∀ p ∈ sparseCarrierCut S b, ∀ q ∈ sparseCarrierCut S b,
      ⟨p, q⟩ₖ ∈ R ↔ SparseOrderCoordinates S R b p q) :
    sparseCarrierOrder S a = sparseCutOrder S R a := by
  classical
  have hall := transfinite_induction (fun b : V ↦ sparseCarrierOrder S b = sparseCutOrder S R b) (by definability) ?_
  · exact hall (IsOrdinal.toOrdinal a)
  intro b ih
  apply mem_ext
  intro z
  by_cases hz : z ∈ sparseCarrierCut S (b : V) ×ˢ sparseCarrierCut S (b : V)
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    rw [sparseCarrierOrder_row, pair_mem_sparseCutOrder]
    simp only [hp, hq, true_and]
    rw [hcoord (b : V) inferInstance p hp q hq]
    unfold SparseOrderCoordinates SparseCoordinateComparison
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hc
    let := IsOrdinal.of_mem hc
    have he : sparseCarrierOrder S c = sparseCutOrder S R c := ih (IsOrdinal.toOrdinal c) hc
    rw [he]
  · apply iff_of_false (fun h ↦ hz (sparseCarrierOrder_subset z h))
    intro h
    unfold sparseCutOrder forcingOrderRestriction at h
    exact hz (mem_sep_iff.mp h).1

end ZFVP
