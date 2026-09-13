import ZFVP.ModelTheory.CohenModel
import ZFVP.SetTheory.CohenRepresentativeIntersection

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace CohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (cohenConditions (ω : V)) (cohenOrder (ω : V)) G)

/-- Equal evaluated names admit an actual representative supported by the exact intersection.
This theorem compares representatives directly, without an action on the fixed-generic quotient. -/
theorem representative_intersection_of_equal
    (τ σ : (cohenContext (ω : V) G hG).Name) {E F : V}
    (hE : IsCohenNameSupport τ.val E) (hF : IsCohenNameSupport σ.val F)
    (he : (cohenContext (ω : V) G hG).ofName τ = (cohenContext (ω : V) G hG).ofName σ) :
    ∃ ν : (cohenContext (ω : V) G hG).Name,
      (cohenContext (ω : V) G hG).ofName ν = (cohenContext (ω : V) G hG).ofName τ ∧
      IsCohenNameSupport ν.val (E ∩ F) := by
  let S := cohenContext (ω : V) G hG
  have he' : GenericMeets G (atomicEquality S.P S.R τ.val σ.val) :=
    (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ τ σ).mp he
  obtain ⟨p, hpG, hpEq⟩ := he'
  obtain ⟨ν, hν, hpν, hνS⟩ :=
    cohen_representative_intersection_below τ.property σ.property hE hF hpEq
  refine ⟨⟨ν, hν⟩, ?_, hνS⟩
  exact (ClassForcingQuotient.ofName_eq_iff S.P S.R S.G S.order S.generic.1 _ _ ⟨ν, hν⟩ τ).mpr
    ⟨p, hpG, hpν⟩

end CohenModel

end ZFVP
