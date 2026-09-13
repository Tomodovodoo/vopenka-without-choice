import ZFVP.ModelTheory.ProjectionInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

noncomputable def projectionQuotientRealization :
    ForcingRealization (A.projectionQuotientContext B hπ he) B.Model where
  ground := A.projectionInclusion B hπ he
  genericSet := B.genericSet
  generic_subset := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (B.mem_genericSet_iff x).mp hx
    rw [← A.projectionInclusion_check B hπ he]
    apply (A.projectionInclusion B hπ he).mem_iff _ _ |>.mpr
    exact (A.check_mem_projectionQuotient_iff hπ.projection.maps).mpr
      ⟨B.generic.1.1 q hq, he ▸ hπ.projection.image_mem A.order B.generic.1 hq⟩
  generic_mem := by
    intro x
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := (B.mem_genericSet_iff _).mp hx
      refine ⟨q, hq, ?_⟩
      apply (A.projectionInclusion B hπ he).injective
      exact hqx.trans (A.projectionInclusion_check B hπ he q).symm
    · rintro ⟨q, hq, rfl⟩
      rw [A.projectionInclusion_check B hπ he, B.check_mem_genericSet_iff]
      exact hq

theorem projectionQuotientRealization_surjective :
    Function.Surjective (A.projectionQuotientRealization B hπ he).value := by
  let C := A.projectionQuotientContext B hπ he
  let L := A.projectionQuotientRealization B hπ he
  apply ForcingRealization.value_surjective_of_generators B L
  · intro x
    refine ⟨C.check (A.check x), ?_⟩
    exact (L.value_check (A.check x)).trans (A.projectionInclusion_check B hπ he x)
  · exact ⟨C.genericSet, L.value_genericSet⟩

/-- The total extension is the extension by the projection quotient over the intermediate model. -/
noncomputable def projectionFactorizationEquiv :
    (A.projectionQuotientContext B hπ he).Model ≃ B.Model :=
  Equiv.ofBijective (A.projectionQuotientRealization B hπ he).value
    ⟨(A.projectionQuotientRealization B hπ he).embedding.injective,
      A.projectionQuotientRealization_surjective B hπ he⟩

theorem projectionFactorizationEquiv_mem_iff
    (x y : (A.projectionQuotientContext B hπ he).Model) :
    A.projectionFactorizationEquiv B hπ he x ∈ A.projectionFactorizationEquiv B hπ he y ↔ x ∈ y :=
  (A.projectionQuotientRealization B hπ he).value_mem_iff x y

theorem projectionFactorizationEquiv_check (x : A.Model) :
    A.projectionFactorizationEquiv B hπ he ((A.projectionQuotientContext B hπ he).check x) =
      A.projectionInclusion B hπ he x :=
  (A.projectionQuotientRealization B hπ he).value_check x

theorem projectionFactorizationEquiv_ground (x : V) :
    A.projectionFactorizationEquiv B hπ he ((A.projectionQuotientContext B hπ he).check (A.check x)) =
      B.check x :=
  (A.projectionFactorizationEquiv_check B hπ he (A.check x)).trans
    (A.projectionInclusion_check B hπ he x)

noncomputable def projectionFactorizationElementaryMap :
    ElementaryMap (A.projectionQuotientContext B hπ he).Model B.Model :=
  ElementaryMap.ofMembershipIso (A.projectionFactorizationEquiv B hπ he)
    (A.projectionFactorizationEquiv_mem_iff B hπ he)

end ForcingContext
end ZFVP
