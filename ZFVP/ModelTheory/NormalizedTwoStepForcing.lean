import ZFVP.ModelTheory.NormalizedTwoStepComparison
import ZFVP.ModelTheory.EquivalentSuborderGeneric

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameTwoStepOrderOn_preorder {P R one δ Q S C : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S]))
    (hC : C ⊆ boundedNameTwoStep P R δ Q) :
    IsForcingPreorder C (nameTwoStepOrderOn P R S C) := by
  refine ⟨fun z hz ↦ (mem_sep_iff.mp hz).1, ?_, ?_⟩
  · intro z hz
    have hb := hC z hz
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hb).1
    obtain ⟨hp, _, hτ, hm⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hb
    exact (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr
      ⟨hz, hz, hR.2.1 p hp, forcedPreorder_refl hR ht hp ⟨Q, hQ⟩ ⟨S, hS⟩ ⟨τ, hτ⟩ (hpre p hp) hm⟩
  · intro z hz w hw u hu hzw hwu
    have hbz := hC z hz
    have hbw := hC w hw
    have hbu := hC u hu
    obtain ⟨p, _, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hbz).1
    obtain ⟨q, _, σ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hbw).1
    obtain ⟨r, _, ν, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hbu).1
    obtain ⟨hp, _, hτ, _⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hbz
    obtain ⟨hq, _, hσ, _⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hbw
    obtain ⟨hr, _, hν, _⟩ := (pair_mem_boundedNameTwoStep _ _ _ _ _ _).mp hbu
    obtain ⟨_, _, hpq, hτσ⟩ := (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mp hzw
    obtain ⟨_, _, hqr, hσν⟩ := (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mp hwu
    have hpσν := (forcingFormula_regular hR boundedPairMemberFormula _).2.1 q hσν p hp hpq
    exact (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr
      ⟨hz, hu, hR.2.2 p hp q hq r hr hpq hqr,
        forcedPreorder_trans hR ht hp ⟨Q, hQ⟩ ⟨S, hS⟩ ⟨τ, hτ⟩ ⟨σ, hσ⟩ ⟨ν, hν⟩
          (hpre p hp) hτσ hpσν⟩

theorem boundedNameTwoStep_preorder {P R one δ Q S : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S])) :
    IsForcingPreorder (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) :=
  nameTwoStepOrderOn_preorder hR ht hQ hS hpre (fun _ hz ↦ hz)

theorem normalizedNameTwoStep_preorder {P R one δ Q S : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S])) :
    IsForcingPreorder (normalizedNameTwoStep P R one δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q)) :=
  nameTwoStepOrderOn_preorder hR ht hQ hS hpre (normalizedNameTwoStep_subset hR ht)

theorem normalizedNameTwoStep_dense {P R one δ Q S : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S])) :
    ForcingDense (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) (normalizedNameTwoStep P R one δ Q) := by
  refine ⟨normalizedNameTwoStep_subset hR ht, ?_⟩
  intro z hz
  have hp : kpair.π₁ z ∈ P := by
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    simpa using hp
  exact ⟨guardedTwoStepCode P R one z, guardedTwoStepCode_mem hR ht hδ hP h0 hz,
    (guardedTwoStepCode_equivalent hR ht hδ hP hQ hS h0 (hpre _ hp) hz).1⟩

theorem normalizedNameTwoStep_equivalent_representatives {P R one δ Q S : V} [IsOrdinal δ]
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S])) :
    ∀ z ∈ boundedNameTwoStep P R δ Q, ∃ n ∈ normalizedNameTwoStep P R one δ Q,
      ⟨n, z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) ∧
      ⟨z, n⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) := by
  intro z hz
  have hp : kpair.π₁ z ∈ P := by
    obtain ⟨p, hp, τ, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    simpa using hp
  exact ⟨guardedTwoStepCode P R one z, guardedTwoStepCode_mem hR ht hδ hP h0 hz,
    guardedTwoStepCode_equivalent hR ht hδ hP hQ hS h0 (hpre _ hp) hz⟩

theorem normalizedNameTwoStep_generic_iff {P R one δ Q S : V} [IsOrdinal δ] {G : Set V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S]))
    (hG : IsExternalForcingFilter (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G) :
    IsExternalForcingGeneric (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G ↔
    IsExternalForcingGeneric (normalizedNameTwoStep P R one δ Q)
      (nameTwoStepOrderOn P R S (normalizedNameTwoStep P R one δ Q))
      {z | z ∈ G ∧ z ∈ normalizedNameTwoStep P R one δ Q} :=
  equivalentSuborder_generic_iff (boundedNameTwoStep_preorder hR ht hQ hS hpre)
    (normalizedNameTwoStep_subset hR ht)
    (fun _ hz _ hw ↦ normalizedNameTwoStep_inclusion_order_iff hR ht hz hw)
    (normalizedNameTwoStep_equivalent_representatives hR ht hδ hP hQ hS h0 hpre) hG

theorem normalizedNameTwoStep_filter_recover {P R one δ Q S : V} [IsOrdinal δ] {G : Set V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one)
    (hδ : ∀ β ∈ δ, succ β ∈ δ) (hP : P ∈ hierarchy δ)
    (hQ : IsForcingName P Q) (hS : IsForcingName P S)
    (h0 : one ∈ atomicMembership P R ∅ Q)
    (hpre : ∀ p ∈ P, p ∈ forcingFormula P R forcingPreorderFormula (standardTuple ![Q, S]))
    (hG : IsExternalForcingFilter (boundedNameTwoStep P R δ Q)
      (nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q)) G) (z : V) :
    z ∈ G ↔ z ∈ boundedNameTwoStep P R δ Q ∧ ∃ n ∈ G,
      n ∈ normalizedNameTwoStep P R one δ Q ∧
      ⟨n, z⟩ₖ ∈ nameTwoStepOrderOn P R S (boundedNameTwoStep P R δ Q) :=
  equivalentSuborder_filter_recover (normalizedNameTwoStep_subset hR ht)
    (normalizedNameTwoStep_equivalent_representatives hR ht hδ hP hQ hS h0 hpre) hG z

end ZFVP
