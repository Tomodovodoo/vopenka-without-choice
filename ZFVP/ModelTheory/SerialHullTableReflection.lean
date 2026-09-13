import ZFVP.ModelTheory.ReflectedPairWitnessTable
import ZFVP.ModelTheory.SerialForcingWitnessTables

/-! Witness tables reflect dense initial and successor witnesses into an elementary hull. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsElementaryInclusion
variable {X B P R one p : V} [IsTransitive B] [Countable V]

theorem serial_initial_dense (h : IsElementaryInclusion X B)
    (hP : P ⊆ X) (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P) (hT : serialInitialWitnessTable P R A.val ∈ X)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val])) :
    ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ∃ ν ∈ X ∩ domain A.val,
      ⟨r, q⟩ₖ ∈ R ∧ r ∈ forcingFormula P R serialHullInitialFormula
        (standardTuple ![A.val, ν]) := by
  intro q hq hqp
  obtain ⟨r, _, ν, hνX, ht⟩ := h.table_pair_fiber_witness hT (hP q hq)
    (serialInitialWitnessTable_fiber_countable hR htop A S hp hq hqp)
  obtain ⟨_, hr, hνd, hrq, hf⟩ := (mem_serialInitialWitnessTable _ _ _ _ _ _).mp ht
  exact ⟨r, hr, ν, mem_inter_iff.mpr ⟨hνX, hνd⟩, hrq, hf⟩

theorem serial_next_dense (h : IsElementaryInclusion X B)
    (hP : P ⊆ X) (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (A S : ForcingName P) (hT : serialNextWitnessTable P R A.val S.val ∈ X)
    (hpairs : ∀ q ∈ P, ∀ τ ∈ domain A.val, ⟨q, τ⟩ₖ ∈ B)
    (hp : p ∈ forcingFormula P R serialHullPremiseFormula (standardTuple ![A.val, S.val])) :
    ∀ τ ∈ X ∩ domain A.val, ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R →
      q ∈ forcingFormula P R serialHullInitialFormula (standardTuple ![A.val, τ]) →
      ∃ r ∈ P, ∃ ν ∈ X ∩ domain A.val, ⟨r, q⟩ₖ ∈ R ∧
        r ∈ forcingFormula P R serialHullNextFormula (standardTuple ![A.val, S.val, τ, ν]) := by
  intro τ hτ q hq hqp hfτ
  obtain ⟨hτX, hτd⟩ := mem_inter_iff.mp hτ
  have hinput : ⟨q, τ⟩ₖ ∈ X := h.kpair_mem (hP q hq) hτX (hpairs q hq τ hτd)
  obtain ⟨r, _, ν, hνX, ht⟩ := h.table_pair_fiber_witness hT hinput
    (serialNextWitnessTable_fiber_countable hR htop A S hp hq hqp hτd hfτ)
  obtain ⟨_, _, hr, hνd, hrq, hf⟩ := (mem_serialNextWitnessTable _ _ _ _ _ _ _ _).mp ht
  exact ⟨r, hr, ν, mem_inter_iff.mpr ⟨hνX, hνd⟩, hrq, hf⟩

end IsElementaryInclusion
end ZFVP
