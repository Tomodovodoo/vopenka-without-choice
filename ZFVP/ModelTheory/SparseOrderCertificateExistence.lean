import ZFVP.ModelTheory.SparseOrderCertificateUniqueness

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem sparseOrderCertificate_of_tables {W T S a C O E : V} [IsOrdinal a] [IsTransitive T]
    (hC : ∀ b ∈ a, C ‘ b = sparseCarrierCut S b)
    (hO : ∀ b ∈ a, O ‘ b = sparseCarrierOrder S b)
    (hE : ∀ b ∈ a, IsAtomicTruthTable (C ‘ b) (O ‘ b) T (E ‘ b))
    (hW : ∀ b ∈ a, C ‘ b ∈ W ∧ O ‘ b ∈ W ∧ E ‘ b ∈ W)
    (hpre : ∀ b ∈ a, IsForcingPreorder (sparseCarrierCut S b) (sparseCarrierOrder S b))
    (hname : ∀ b ∈ a, ∀ p ∈ S, IsForcingName (sparseCarrierCut S b) (p ‘ b))
    (hsupp : ∀ b ∈ a, ∀ p ∈ S, p ↾ b ∈ T ∧ p ‘ b ∈ T) :
    boundedSparseOrderCertificateFormula.Evalb ![W, T, S, a, C, O, E] := by
  apply eval_boundedSparseOrderCertificateFormula.mpr
  intro b hb
  let := IsOrdinal.of_mem hb
  refine ⟨(hW b hb).1, (hW b hb).2.1, (hW b hb).2.2, hC b hb, hE b hb, ?_, ?_⟩
  · rw [hC b hb, hO b hb]
    exact sparseCarrierOrder_subset
  · intro p hp q hq
    rw [hC b hb] at hp hq
    rw [hO b hb, sparseCarrierOrder_row]
    simp only [hp, hq, true_and]
    apply forall_congr'
    intro c
    apply forall_congr'
    intro hcb
    have hca := (IsOrdinal.toIsTransitive : IsTransitive a).mem_trans hcb hb
    have hpS := (mem_sparseCarrierCut_iff.mp hp).1
    have hqS := (mem_sparseCarrierCut_iff.mp hq).1
    have he := eval_boundedSparseComparisonFormula (hW c hca).1 (hW c hca).2.1 (hW c hca).2.2
      (hsupp c hca p hpS).1 (hsupp c hca q hqS).2 (hsupp c hca p hpS).2
      (by rw [hC c hca, hO c hca]; exact hpre c hca)
      (by rw [hC c hca]; exact hname c hca q hqS)
      (by rw [hC c hca]; exact hname c hca p hpS) (hE c hca)
    simpa only [hC c hca, hO c hca] using he.symm

end ZFVP
