import ZFVP.ModelTheory.CohenModel
import ZFVP.SetTheory.CohenLocalSupport

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Equal evaluated supported names have a common supported representative, with the
coordinates of a witnessing generic condition recorded explicitly. -/
theorem common_representative_of_equal
    (τ σ : (cohenContext (ω : V) G hG).Name) {E F : V}
    (hE : IsCohenNameSupport τ.val E) (hF : IsCohenNameSupport σ.val F)
    (he : (cohenContext (ω : V) G hG).ofName τ = (cohenContext (ω : V) G hG).ofName σ) :
    ∃ p ∈ G, ∃ ν : (cohenContext (ω : V) G hG).Name,
      (cohenContext (ω : V) G hG).ofName ν = (cohenContext (ω : V) G hG).ofName τ ∧
      IsCohenNameSupport ν.val ((E ∩ F) ∪ cohenSupport p) := by
  let S := cohenContext (ω : V) G hG
  have he' : GenericMeets G (atomicEquality S.P S.R τ.val σ.val) :=
    (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ τ σ).mp he
  obtain ⟨p, hpG, hpEq⟩ := he'
  obtain ⟨ν, hν, hpν, hνS⟩ :=
    cohen_common_representative_below τ.property σ.property hE hF (hG.1.1 p hpG) hpEq
  refine ⟨p, hpG, ⟨ν, hν⟩, ?_, hνS⟩
  exact (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ ⟨ν, hν⟩ τ).mpr
    ⟨p, hpG, hpν⟩

end CohenModel

end ZFVP
