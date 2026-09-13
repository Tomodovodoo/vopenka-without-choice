import ZFVP.SetTheory.WoodinCollapse
import ZFVP.SetTheory.OrdinalLeftOne
import ZFVP.SetTheory.BoundedFunctionDomain
import ZFVP.SetTheory.PiOneInitialOrdinal
import ZFVP.SetTheory.PiOneHierarchy

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneWoodinRowFormula : SetTheorySemisentence 4 :=
  “z κ β H. ∃ a ∈ κ, ∃ η ∈ β, ∃ x ∈ H, ∃ b, ∃ ξ,
    !boundedKpairFormula b a η ∧ !boundedKpairFormula z b x ∧
    !sigmaOneOrdinalLeftOneFormula ξ η ∧ !sigmaOneRankLtFormula x ξ”

theorem sigmaOneWoodinRowFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinRowFormula :=
  .boundedExs (.bvar 1) (.boundedExs (.bvar 3) (.boundedExs (.bvar 5) (.exs (.exs
    (.and (.bounded (boundedKpairFormula_bounded.subst _))
      (.and (.bounded (boundedKpairFormula_bounded.subst _))
        (.and (sigmaOneOrdinalLeftOneFormula_sigmaOne.subst _)
          (sigmaOneRankLtFormula_sigmaOne.subst _))))))))

def sigmaOneWoodinConditionFormula : SetTheorySemisentence 4 :=
  “p κ β H. (∃ D, !boundedFunctionDomainFormula p D ∧
    ∃ α ∈ κ, ∃ g, !boundedInjectionFormula g D α) ∧
    ∀ z ∈ p, !sigmaOneWoodinRowFormula z κ β H”

theorem sigmaOneWoodinConditionFormula_sigmaOne : IsSigmaFormula 1 sigmaOneWoodinConditionFormula :=
  .and (.exs (.and (.bounded (boundedFunctionDomainFormula_bounded.subst _))
    (.boundedExs (.bvar 2) (.exs (.bounded (boundedInjectionFormula_bounded.subst _))))))
    (.boundedAll (.bvar 0) (sigmaOneWoodinRowFormula_sigmaOne.subst _))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneWoodinRowFormula (z κ β H : V) [IsOrdinal β] :
    sigmaOneWoodinRowFormula.Evalb ![z, κ, β, H] ↔
      ∃ a ∈ κ, ∃ η ∈ β, ∃ x ∈ H, z = ⟨⟨a, η⟩ₖ, x⟩ₖ ∧
        x ∈ hierarchy (ordinalAdd (1 : V) η) := by
  let : IsOrdinal (1 : V) := IsOrdinal.of_mem (show (1 : V) ∈ (ω : V) by simp)
  simp [sigmaOneWoodinRowFormula, eval_sigmaOneOrdinalLeftOneFormula, eval_sigmaOneRankLtFormula]
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  apply exists_congr
  intro η
  apply and_congr_right
  intro hη
  let := IsOrdinal.of_mem hη
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  simp [mem_hierarchy_iff_rank_mem, show IsOrdinal η from inferInstance]

theorem eval_sigmaOneWoodinConditionFormula (p κ β : V) [IsOrdinal β] :
    sigmaOneWoodinConditionFormula.Evalb ![p, κ, β, hierarchy β] ↔
      p ∈ woodinCollapse κ β := by
  have hr : (∀ z ∈ p, sigmaOneWoodinRowFormula.Evalb ![z, κ, β, hierarchy β]) ↔
      p ⊆ (κ ×ˢ β) ×ˢ hierarchy β ∧
        ∀ a η x, ⟨⟨a, η⟩ₖ, x⟩ₖ ∈ p → x ∈ hierarchy (ordinalAdd (1 : V) η) := by
    simp only [eval_sigmaOneWoodinRowFormula]
    constructor
    · intro h
      constructor
      · intro z hz
        obtain ⟨a, ha, η, hη, x, hx, rfl, _⟩ := h z hz
        exact kpair_mem_iff.mpr ⟨kpair_mem_iff.mpr ⟨ha, hη⟩, hx⟩
      · intro a η x hz
        obtain ⟨b, hb, ξ, hξ, y, hy, he, hv⟩ := h _ hz
        have h := kpair_inj he
        have h' := kpair_inj h.1
        simpa only [h'.1, h'.2, h.2] using hv
    · rintro ⟨hs, hv⟩ z hz
      obtain ⟨b, hb, x, hx, rfl⟩ := mem_prod_iff.mp (hs z hz)
      obtain ⟨a, ha, η, hη, rfl⟩ := mem_prod_iff.mp hb
      exact ⟨a, ha, η, hη, x, hx, rfl, hv a η x hz⟩
  have hf : (∃ D, boundedFunctionDomainFormula.Evalb ![p, D] ∧
      ∃ α ∈ κ, ∃ g, boundedInjectionFormula.Evalb ![g, D, α]) ↔
      IsFunction p ∧ IsCardinalSmall κ (domain p) := by
    simp [IsCardinalSmall, CardLE]
  rw [mem_woodinCollapse]
  have he : sigmaOneWoodinConditionFormula.Evalb ![p, κ, β, hierarchy β] ↔
      (IsFunction p ∧ IsCardinalSmall κ (domain p)) ∧
        p ⊆ (κ ×ˢ β) ×ˢ hierarchy β ∧
          ∀ a η x, ⟨⟨a, η⟩ₖ, x⟩ₖ ∈ p → x ∈ hierarchy (ordinalAdd (1 : V) η) := by
    simpa [sigmaOneWoodinConditionFormula] using and_congr hf hr
  rw [he]
  tauto

end ZFVP



