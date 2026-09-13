import ZFVP.ModelTheory.ForcingConditionalEquivalence
import ZFVP.ModelTheory.ForcingReverseOrderName
import ZFVP.ModelTheory.NormalizedTwoStepComparison

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem reverseInclusionOrderName_comparison {P R one p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hp : p ∈ P)
    (Q τ σ : ForcingName P)
    (hτ : p ∈ atomicMembership P R τ.val Q.val)
    (hσ : p ∈ atomicMembership P R σ.val Q.val) :
    p ∈ forcingFormula P R boundedPairMemberFormula
      (standardTuple ![reverseInclusionOrderName P R Q.val, τ.val, σ.val]) ↔
    p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ.val, τ.val]) := by
  let S : ForcingName P := ⟨_, reverseInclusionOrderName_isName P R Q.val⟩
  let φ : SetTheorySemisentence 4 :=
    (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 4) i))).and
      ((nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 4) i))).and
        (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 0] : Fin 2 → Fin 4) i))))
  let ψ : SetTheorySemisentence 4 := boundedPairMemberFormula.subst
    (fun i ↦ .bvar ((![1, 2, 3] : Fin 3 → Fin 4) i))
  let χ : SetTheorySemisentence 4 := isSubsetOf.subst
    (fun i ↦ .bvar ((![3, 2] : Fin 2 → Fin 4) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, τ.val, σ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename]
    exact ⟨reverseInclusionOrderName_forces hR ht hp Q,
      (forcingFormula_nameMember P R τ.val Q.val).symm ▸ hτ,
      (forcingFormula_nameMember P R σ.val Q.val).symm ▸ hσ⟩
  have hh := forcingFormula_iff_under φ ψ χ (by
    intro W _ _ _ v hv
    change (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 4) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 4) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![3, 0] : Fin 2 → Fin 4) i))).Evalb v at hv
    have he : v 1 = reverseInclusionOrder (v 0) ∧ v 2 ∈ v 0 ∧ v 3 ∈ v 0 := by
      simpa [φ, Semiformula.eval_substs, nameMemberFormula] using hv
    simp [ψ, χ, Semiformula.eval_substs, he.1, pair_mem_reverseInclusionOrder,
      he.2.1, he.2.2] ) hR ht hp ![Q, S, τ, σ] hφ
  dsimp only [ψ, χ] at hh
  rw [forcingFormula_rename, forcingFormula_rename] at hh
  exact hh

theorem normalizedNameTwoStep_reverse_order_comparison {P R one δ Q p q τ σ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R one) (hQ : IsForcingName P Q)
    (hp : p ∈ P) (hq : q ∈ P)
    (hτ : τ ∈ normalizedNamePool P R one δ Q) (hσ : σ ∈ normalizedNamePool P R one δ Q) :
    ⟨⟨p, τ⟩ₖ, ⟨q, σ⟩ₖ⟩ₖ ∈ nameTwoStepOrderOn P R (reverseInclusionOrderName P R Q)
      (normalizedNameTwoStep P R one δ Q) ↔
      ⟨p, q⟩ₖ ∈ R ∧ p ∈ forcingFormula P R isSubsetOf (standardTuple ![σ, τ]) := by
  have hτ' := mem_sep_iff.mp hτ
  have hσ' := mem_sep_iff.mp hσ
  rw [pair_mem_nameTwoStepOrderOn]
  have hpτ : ⟨p, τ⟩ₖ ∈ normalizedNameTwoStep P R one δ Q := kpair_mem_iff.mpr ⟨hp, hτ⟩
  have hqσ : ⟨q, σ⟩ₖ ∈ normalizedNameTwoStep P R one δ Q := kpair_mem_iff.mpr ⟨hq, hσ⟩
  simp only [hpτ, hqσ, true_and]
  exact and_congr_right (fun _ ↦ reverseInclusionOrderName_comparison hR ht hp ⟨Q, hQ⟩
    ⟨τ, hτ'.2.1⟩ ⟨σ, hσ'.2.1⟩
    (atomicMembership_mono hR hτ'.2.2.2 hp (ht.2 p hp))
    (atomicMembership_mono hR hσ'.2.2.2 hp (ht.2 p hp)))

end ZFVP
