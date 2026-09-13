import ZFVP.ModelTheory.InternalLKRuleInterpretation

/-! Every accepted local LK instruction preserves validity in an internal structure. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open PrimitiveProgram

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem naturalLKRuleCore_sound {M S C tag φ ψ θ k Γ Δ : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hS : S ∈ (ω : V)) (hC : C ∈ (ω : V))
    (hφ : φ ∈ (ω : V)) (hψ : ψ ∈ (ω : V)) (hθ : θ ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hΓ : Γ ∈ (ω : V)) (hΔ : Δ ∈ (ω : V))
    (hin : naturalLKInputs S C φ ψ θ Γ Δ)
    (hr : naturalLKRuleCore S C tag φ ψ θ k Γ Δ)
    (hp : ∀ xs ∈ range (decodedNaturalList S), NaturalSequentValid M xs) :
    NaturalSequentValid M C := by
  classical
  obtain ⟨_, _, hvφ, hvψ, hvθ, hvΓ, _⟩ := hin
  have h0 : (0 : V) ∈ (ω : V) := by simp [zero_def]
  have h1 : (1 : V) ∈ (ω : V) := by simp
  have hmem {xs : V} (hxs : xs ∈ (ω : V))
      (hm : listMember.evalSet (naturalSquarePair xs S) = 1) : NaturalSequentValid M xs :=
    hp xs ((evalSet_listMember_iff hxs hS).mp hm)
  unfold naturalLKRuleCore at hr
  split at hr
  · rw [hr]
    exact NaturalSequentValid.eta M hφ hvφ
  · split at hr
    · obtain ⟨ha, hb, rfl⟩ := hr
      exact NaturalSequentValid.cut hφ hΓ hΔ hvφ
        (hmem (ω_succ_closed (naturalSquarePair_natural hφ hΓ)) ha)
        (hmem (ω_succ_closed (naturalSquarePair_natural (evalSet_natural _ hφ) hΔ)) hb)
    · split at hr
      · exact (hmem hΔ hr.1).mono ((evalSet_listSubset_iff hΔ hC).mp hr.2)
      · split at hr
        · rw [hr]
          exact NaturalSequentValid.truth M
        · split at hr
          · obtain ⟨ha, rfl⟩ := hr
            exact NaturalSequentValid.or_rule hφ hψ hΓ hvφ hvψ
              (hmem (ω_succ_closed (naturalSquarePair_natural hφ
                (ω_succ_closed (naturalSquarePair_natural hψ hΓ)))) ha)
          · split at hr
            · obtain ⟨ha, hb, rfl⟩ := hr
              exact NaturalSequentValid.and_rule hφ hψ hΓ hvφ hvψ
                (hmem (ω_succ_closed (naturalSquarePair_natural hφ hΓ)) ha)
                (hmem (ω_succ_closed (naturalSquarePair_natural hψ hΓ)) hb)
            · split at hr
              · obtain ⟨ha, rfl⟩ := hr
                exact NaturalSequentValid.all_rule hM hθ hΓ hvθ hvΓ
                  (hmem (ω_succ_closed (naturalSquarePair_natural
                    (evalSet_natural _ (naturalSquarePair_natural h1 (naturalSquarePair_natural h0 hθ)))
                    (evalSet_natural _ (naturalSquarePair_natural h0 hΓ)))) ha)
              · split at hr
                · obtain ⟨ha, rfl⟩ := hr
                  exact NaturalSequentValid.exists_rule hM hθ hΓ hk hvθ
                    (hmem (ω_succ_closed (naturalSquarePair_natural
                      (evalSet_natural _ (naturalSquarePair_natural
                        (ω_succ_closed (ω_succ_closed hk)) (naturalSquarePair_natural h0 hθ))) hΓ)) ha)
                · exact False.elim hr

theorem evalSet_lkRuleCheck_sound {M S C tag φ ψ θ k Γ Δ : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hS : S ∈ (ω : V)) (hC : C ∈ (ω : V)) (ht : tag ∈ (ω : V))
    (hφ : φ ∈ (ω : V)) (hψ : ψ ∈ (ω : V)) (hθ : θ ∈ (ω : V)) (hk : k ∈ (ω : V))
    (hΓ : Γ ∈ (ω : V)) (hΔ : Δ ∈ (ω : V))
    (hcheck : lkRuleCheck.evalSet (naturalSquarePair S (naturalSquarePair C (naturalSquarePair tag
      (naturalSquarePair φ (naturalSquarePair ψ (naturalSquarePair θ (naturalSquarePair k (naturalSquarePair Γ Δ)))))))) = 1)
    (hp : ∀ xs ∈ range (decodedNaturalList S), NaturalSequentValid M xs) :
    NaturalSequentValid M C := by
  obtain ⟨hin, hr⟩ := (evalSet_lkRuleCheck_eq_one hS hC ht hφ hψ hθ hk hΓ hΔ).mp hcheck
  exact naturalLKRuleCore_sound hM hS hC hφ hψ hθ hk hΓ hΔ hin hr hp

theorem evalSet_lkRuleCheck_sound_raw {M S C w : V}
    (hM : IsStructureCode membershipLanguageCode M)
    (hS : S ∈ (ω : V)) (hC : C ∈ (ω : V)) (hw : w ∈ (ω : V))
    (hcheck : lkRuleCheck.evalSet (naturalSquarePair S (naturalSquarePair C w)) = 1)
    (hp : ∀ xs ∈ range (decodedNaturalList S), NaturalSequentValid M xs) :
    NaturalSequentValid M C := by
  obtain ⟨tag, ht, w1, hw1, rfl⟩ := naturalSquarePair_surjective hw
  obtain ⟨φ, hφ, w2, hw2, rfl⟩ := naturalSquarePair_surjective hw1
  obtain ⟨ψ, hψ, w3, hw3, rfl⟩ := naturalSquarePair_surjective hw2
  obtain ⟨θ, hθ, w4, hw4, rfl⟩ := naturalSquarePair_surjective hw3
  obtain ⟨k, hk, w5, hw5, rfl⟩ := naturalSquarePair_surjective hw4
  obtain ⟨Γ, hΓ, Δ, hΔ, rfl⟩ := naturalSquarePair_surjective hw5
  exact evalSet_lkRuleCheck_sound hM hS hC ht hφ hψ hθ hk hΓ hΔ hcheck hp

end ZFVP
