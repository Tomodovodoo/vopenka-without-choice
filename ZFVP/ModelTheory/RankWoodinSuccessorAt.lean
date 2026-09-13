import ZFVP.ModelTheory.RankSaturatedWoodinName
import ZFVP.ModelTheory.RankInternalReverseOrderName
import ZFVP.ModelTheory.TwoStepOrderGenericEquality
import ZFVP.SetTheory.WoodinSuccessorCode

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_woodinSuccessorAt_val_countable (hξ : IsChoicelessInaccessible ξ)
    (P R one κ γ : SetDomain (hierarchy ξ)) (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (hγ : IsOrdinal γ) :
    (woodinSuccessorAt P R one κ γ).val = woodinSuccessorAt P.val R.val one.val κ.val γ.val := by
  let := hierarchy_transitive ξ
  let Q := saturatedWoodinPrefixPosetName P R one κ γ
  let S := reverseInclusionOrderName P R Q
  have hQ : IsForcingName P Q := saturatedWoodinPrefixPosetName_isName _ _ _ _ _
  have hS : IsForcingName P S := reverseInclusionOrderName_isName _ _ _
  have hQval := rank_saturatedWoodinPrefixPosetName_val_countable hξ P R one κ γ hR ht hγ
  have hR' := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mp hR
  have ht' := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mp ht
  let q : ForcingName P.val := ⟨Q.val, (TransitiveZF.forcingName_iff (hierarchy ξ) P Q).mp hQ⟩
  let s : ForcingName P.val := ⟨S.val, (TransitiveZF.forcingName_iff (hierarchy ξ) P S).mp hS⟩
  let s' : ForcingName P.val := ⟨reverseInclusionOrderName P.val R.val Q.val,
    reverseInclusionOrderName_isName _ _ _⟩
  have horder := twoStepOrder_eq_of_all_order_values hR' ht' q s s' ⟨∅, empty_forcingName P.val⟩ (by
    intro G hG
    let A : ForcingContext V := ⟨P.val, R.val, one.val, G, hR', ht', hG⟩
    have hi : A.ofName s = reverseInclusionOrder (A.ofName q) :=
      A.rankInternalReverseOrder_value hξ P R one rfl rfl rfl ⟨Q, hQ⟩
    exact hi.trans (A.reverseOrderName_value q).symm)
  have hC : (twoStepConditions P R Q (∅ : SetDomain (hierarchy ξ))).val =
      twoStepConditions P.val R.val (saturatedWoodinPrefixPosetName P.val R.val one.val κ.val γ.val) ∅ := by
    rw [TransitiveZF.twoStepConditions_val, TransitiveZF.empty_val]
    exact congrArg (fun q ↦ twoStepConditions P.val R.val q ∅) hQval
  have hT : (twoStepOrder P R Q S (∅ : SetDomain (hierarchy ξ))).val =
      twoStepOrder P.val R.val (saturatedWoodinPrefixPosetName P.val R.val one.val κ.val γ.val)
        (saturatedWoodinPrefixOrderName P.val R.val one.val κ.val γ.val) ∅ := by
    rw [TransitiveZF.twoStepOrder_val_of_names (hierarchy ξ) P R Q S ∅ hR hQ hS (empty_forcingName P),
      TransitiveZF.empty_val]
    change twoStepOrder P.val R.val q.val s.val ∅ = _
    rw [horder]
    change twoStepOrder P.val R.val Q.val (reverseInclusionOrderName P.val R.val Q.val) ∅ = _
    rw [hQval]
    rfl
  change (woodinStageCode (twoStepConditions P R Q ∅) (twoStepOrder P R Q S ∅) ⟨one, ∅⟩ₖ γ).val = _
  unfold woodinStageCode woodinSuccessorAt
  rw [TransitiveZF.kpair_val, TransitiveZF.kpair_val, TransitiveZF.kpair_val,
    TransitiveZF.kpair_val, TransitiveZF.empty_val, hC, hT]
  rfl

end ZFVP
