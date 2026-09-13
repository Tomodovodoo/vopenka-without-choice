import ZFVP.ModelTheory.SparseNormalizedTwoStep

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem normalizedTail_commonExtension {P R top δ Q S r ν p τ q σ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hr : r ∈ P) (hν : ν ∈ normalizedNamePool P R top δ Q)
    (hp : ⟨p, τ⟩ₖ ∈ normalizedNameTwoStep P R top δ Q)
    (hq : ⟨q, σ⟩ₖ ∈ normalizedNameTwoStep P R top δ Q)
    (hrp : ⟨r, p⟩ₖ ∈ R) (hrq : ⟨r, q⟩ₖ ∈ R)
    (hντ : top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, ν, τ]))
    (hνσ : top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, ν, σ])) :
    let C := normalizedNameTwoStep P R top δ Q
    let T := nameTwoStepOrderOn P R S C
    ⟨r, ν⟩ₖ ∈ C ∧ ⟨⟨r, ν⟩ₖ, ⟨p, τ⟩ₖ⟩ₖ ∈ T ∧ ⟨⟨r, ν⟩ₖ, ⟨q, σ⟩ₖ⟩ₖ ∈ T := by
  have hw : ⟨r, ν⟩ₖ ∈ normalizedNameTwoStep P R top δ Q := kpair_mem_iff.mpr ⟨hr, hν⟩
  exact ⟨hw, (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr
    ⟨hw, hp, hrp, (forcingFormula_regular hR boundedPairMemberFormula _).2.1 top hντ r hr (ht.2 r hr)⟩,
    (pair_mem_nameTwoStepOrderOn _ _ _ _ _ _ _ _).mpr
    ⟨hw, hq, hrq, (forcingFormula_regular hR boundedPairMemberFormula _).2.1 top hνσ r hr (ht.2 r hr)⟩⟩

theorem sparseTail_commonExtension {a P R top δ Q S r ν p q : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z)
    (hr : r ∈ P) (hν : ν ∈ normalizedNamePool P R top δ Q)
    (hp : p ∈ sparseNormalizedTwoStep a P R top δ Q)
    (hq : q ∈ sparseNormalizedTwoStep a P R top δ Q)
    (hrp : ⟨r, p ↾ a⟩ₖ ∈ R) (hrq : ⟨r, q ↾ a⟩ₖ ∈ R)
    (hνp : top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, ν, p ‘ a]))
    (hνq : top ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S, ν, q ‘ a])) :
    let C := sparseNormalizedTwoStep a P R top δ Q
    let T := sparseNormalizedTwoStepOrder a P R top δ Q S
    let w := sparseAppend a r ν
    w ∈ C ∧ ⟨w, p⟩ₖ ∈ T ∧ ⟨w, q⟩ₖ ∈ T ∧ w ↾ a = r ∧ w ‘ a = ν := by
  have hs := hsp r hr
  let := hs.1
  have hw : sparseAppend a r ν ∈ sparseNormalizedTwoStep a P R top δ Q :=
    sparseAppend_mem_pairCarrier hsp hr hν
  have hres : (sparseAppend a r ν) ↾ a = r := sparseAppend_restrict hs.2.1
  have htail : (sparseAppend a r ν) ‘ a = ν := sparseAppend_value_new hs.2.1
  refine ⟨hw, ?_, ?_, hres, htail⟩
  · apply pair_mem_sparseNormalizedTwoStepOrder.mpr
    rw [hres, htail]
    exact ⟨hw, hp, hrp,
      (forcingFormula_regular hR boundedPairMemberFormula _).2.1 top hνp r hr (ht.2 r hr)⟩
  · apply pair_mem_sparseNormalizedTwoStepOrder.mpr
    rw [hres, htail]
    exact ⟨hw, hq, hrq,
      (forcingFormula_regular hR boundedPairMemberFormula _).2.1 top hνq r hr (ht.2 r hr)⟩

end ZFVP
