import ZFVP.ModelTheory.BoundedSparseOrderCertificate
import ZFVP.ModelTheory.SparseOrderIdentification

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseOrderCertificate_unique {W T S a C O E : V} [IsOrdinal a] [IsTransitive T]
    (hc : boundedSparseOrderCertificateFormula.Evalb ![W, T, S, a, C, O, E])
    (hpre : ∀ b ∈ a, IsForcingPreorder (sparseCarrierCut S b) (sparseCarrierOrder S b))
    (hname : ∀ b ∈ a, ∀ p ∈ S, IsForcingName (sparseCarrierCut S b) (p ‘ b))
    (hsupp : ∀ b ∈ a, ∀ p ∈ S, p ↾ b ∈ T ∧ p ‘ b ∈ T) :
    ∀ b ∈ a, O ‘ b = sparseCarrierOrder S b := by
  have hrows := eval_boundedSparseOrderCertificateFormula.mp hc
  have hall := transfinite_induction
    (fun b : V ↦ b ∈ a → O ‘ b = sparseCarrierOrder S b) (by definability) ?_
  · intro b hb
    let := IsOrdinal.of_mem hb
    exact hall (IsOrdinal.toOrdinal b) hb
  intro b ih hb
  obtain ⟨_, _, _, hCb, _, hsub, hrow⟩ := hrows (b : V) hb
  rw [hCb] at hsub hrow
  apply mem_ext
  intro z
  by_cases hz : z ∈ sparseCarrierCut S (b : V) ×ˢ sparseCarrierCut S (b : V)
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_prod_iff.mp hz
    rw [hrow p hp q hq, sparseCarrierOrder_row]
    simp only [hp, hq, true_and]
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hcb
    have hca := (IsOrdinal.toIsTransitive : IsTransitive a).mem_trans hcb hb
    let := IsOrdinal.of_mem hca
    have hOc : O ‘ c = sparseCarrierOrder S c := ih (IsOrdinal.toOrdinal c) hcb hca
    obtain ⟨hCW, hOW, hEW, hCc, hH, _, _⟩ := hrows c hca
    have hpS := (mem_sparseCarrierCut_iff.mp hp).1
    have hqS := (mem_sparseCarrierCut_iff.mp hq).1
    have he := eval_boundedSparseComparisonFormula hCW hOW hEW
      (hsupp c hca p hpS).1 (hsupp c hca q hqS).2 (hsupp c hca p hpS).2
      (by rw [hCc, hOc]; exact hpre c hca)
      (by rw [hCc]; exact hname c hca q hqS)
      (by rw [hCc]; exact hname c hca p hpS) hH
    simpa only [hCc, hOc] using he
  · exact iff_of_false (fun h ↦ hz (hsub z h)) (fun h ↦ hz (sparseCarrierOrder_subset z h))

end ZFVP
