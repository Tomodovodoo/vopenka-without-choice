import ZFVP.ModelTheory.SuccessorRankGenericClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace SuccessorRankLiftData
variable {A B : ForcingContext V} {ρ ε e κ : V} (L : SuccessorRankLiftData A B ρ ε e)
  (hP : A.P ⊆ B.P) (hG : ∀ p, p ∈ A.G ↔ p ∈ B.G ∧ p ∈ A.P)

theorem genericGraph_dependentChoicePath [IsOrdinal κ]
    (heone : e ‘ A.one = B.one) (hκ : κ ∈ hierarchy ρ)
    (hfix : ∀ α ∈ κ, e ‘ α = α)
    (hpre : ∀ α ∈ κ, ∀ (X : A.Model) (f : B.Model),
      f ∈ A.genericInclusion B hG X ^ B.check α →
      ∃ g ∈ X ^ A.check α, A.genericInclusion B hG g = f)
    {X R : B.Model} (hX : X ∈ domain (L.genericGraph hP)) (hR : R ∈ domain (L.genericGraph hP))
    (hw : IsWellOrderable X)
    (hserial : ∀ s ∈ shorterSequences (B.check κ) ((L.genericGraph hP) ‘ X),
      ∃ x ∈ (L.genericGraph hP) ‘ X, ⟨s, x⟩ₖ ∈ (L.genericGraph hP) ‘ R) :
    ∃ f, IsDependentChoicePath ((L.genericGraph hP) ‘ X) ((L.genericGraph hP) ‘ R) (B.check κ) f := by
  let := L.source_correct.ordinal
  apply (L.genericGraph_boundedElementary hP hG).dependentChoicePath hX hR
    (L.check_mem_genericGraph_domain hP hG hκ) ?_ ?_ hw hserial
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := (B.mem_check_iff κ α).mp hα
    rw [L.genericGraph_check hP hG heone ((hierarchy_transitive ρ).mem_trans ha hκ), hfix a ha]
  · intro α hα s hs
    obtain ⟨a, ha, rfl⟩ := (B.mem_check_iff κ α).mp hα
    exact L.genericGraph_function_closed hP hG ((hierarchy_transitive ρ).mem_trans ha hκ)
      (hpre a ha) hX hs

end SuccessorRankLiftData
end ZFVP
