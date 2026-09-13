import ZFVP.ModelTheory.LocalSelectedUnionInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (A : ForcingContext V)

theorem selectedName_subset_normalizedUnion {C D H d q : V}
    (hC : ∀ σ ∈ C, IsForcingName A.P σ) (hH : H ∈ C ^ D)
    (f ν : ForcingName A.P) {X i : A.Model} (hf : A.ofName f ∈ A.check D ^ X)
    (hi : i ∈ X) (hd : d ∈ D) (he : (A.ofName f) ‘ i = A.check d)
    (hq : q ∈ A.G)
    (hn : q ∈ atomicEquality A.P A.R ν.val
      (forcingSelectedUnion A.P A.R A.one C H f.val)) :
    A.ofName ⟨H ‘ d, hC _ (function_value_mem hH hd)⟩ ⊆ A.ofName ν := by
  have hn' : A.ofName ν = A.ofName
      ⟨forcingSelectedUnion A.P A.R A.one C H f.val, forcingSelectedUnion_isName _ _ _ _ _ _⟩ :=
    (forcingQuotientMk_eq_iff A.P A.R A.G A.order A.generic.1 _ _).mpr ⟨q, hq, hn⟩
  rw [hn']
  exact A.selectedName_subset_union hC hH f hf hi hd he

end ForcingContext
end ZFVP
