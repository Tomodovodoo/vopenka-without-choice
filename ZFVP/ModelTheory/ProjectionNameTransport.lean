import ZFVP.ModelTheory.ProjectionInclusion
import ZFVP.SetTheory.EndExtensionNameAction

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext
variable (A B : ForcingContext V) {π E : V}
  (hπ : IsForcingSplitProjection A.P A.R B.P B.R π E)
  (he : forcingProjectionGeneric A.P A.R π B.G = A.G)

include he

/-- Apply the section to every condition in an earlier-stage name. Its value
is the image under the actual projection inclusion. -/
theorem projectionInclusion_nameAction (τ : ForcingName A.P) :
    B.ofName ⟨nameAction E τ.val, nameAction_isName hπ.maps τ.property⟩ =
      A.projectionInclusion B hπ he (A.ofName τ) := by
  rw [← B.nameValue_genericSet_check]
  change nameValue B.genericSet (B.check (nameAction E τ.val)) =
    nameValue (A.projectedGenericSet B E) (B.check τ.val)
  rw [show B.check (nameAction E τ.val) = nameAction (B.check E) (B.check τ.val)
    from B.checkEmbedding.map_nameAction E τ.val]
  apply nameValue_nameAction_of_membership
    ((B.checkEmbedding.forcingName_iff A.P τ.val).mp τ.property)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := (B.mem_check_iff A.P p).mp hp
  rw [← show B.check (E ‘ q) = (B.check E) ‘ (B.check q)
    from B.checkEmbedding.map_value_total E q, B.check_mem_genericSet_iff,
    A.check_mem_projectedGenericSet B hπ he]
  exact (hπ.generic_iff_section A.order B.generic.1 hq).symm.trans
    (by rw [he])

theorem projection_nameAction_selects (τ : ForcingName A.P) {x : V}
    (hτ : A.ofName τ = A.check x) :
    B.ofName ⟨nameAction E τ.val, nameAction_isName hπ.maps τ.property⟩ = B.check x := by
  rw [A.projectionInclusion_nameAction B hπ he τ, hτ, A.projectionInclusion_check B hπ he]

end ForcingContext
end ZFVP
