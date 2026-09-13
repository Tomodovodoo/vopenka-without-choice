import ZFVP.ModelTheory.ForcingPullbackGeneric
import ZFVP.ModelTheory.ForcingRealizationGeneration
import ZFVP.SetTheory.EndExtensionNameAction
import ZFVP.ModelTheory.ForcingGenericInclusion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace ForcingContext
variable (B : ForcingContext V) {Q π : V} (hπ : π ∈ B.P ^ Q)
  (hs : ∀ p ∈ B.P, ∃ q ∈ Q, π ‘ q = p)

noncomputable def pullbackContext : ForcingContext V := by
  classical
  let q := Classical.choose (hs B.one B.top.1)
  have hq := Classical.choose_spec (hs B.one B.top.1)
  refine ⟨Q, forcingPullbackOrder Q B.R π, q, forcingPullbackGeneric Q π B.G,
    forcingPullbackOrder_preorder B.order hπ, ⟨hq.1, ?_⟩,
    forcingPullbackGeneric_generic hπ hs B.generic⟩
  intro p hp
  apply (mem_forcingPullbackOrder_iff _ _ _ _ _).mpr
  refine ⟨hp, hq.1, ?_⟩
  rw [hq.2]
  exact B.top.2 _ (function_value_mem hπ hp)

noncomputable def pullbackGenericSet (Q π : V) : B.Model :=
  {q ∈ B.check Q ; (B.check π) ‘ q ∈ B.genericSet}

theorem check_mem_pullbackGenericSet (q : V) :
    B.check q ∈ B.pullbackGenericSet Q π ↔ q ∈ forcingPullbackGeneric Q π B.G := by
  simp only [pullbackGenericSet, mem_sep_iff, B.check_mem_iff]
  rw [← show B.check (π ‘ q) = (B.check π) ‘ (B.check q) from B.checkEmbedding.map_value_total π q,
    B.check_mem_genericSet_iff]
  rfl

noncomputable def pullbackRealization : ForcingRealization (B.pullbackContext hπ hs) B.Model where
  ground := B.checkEmbedding
  genericSet := B.pullbackGenericSet Q π
  generic_subset := fun _ h ↦ (mem_sep_iff.mp h).1
  generic_mem := B.check_mem_pullbackGenericSet

noncomputable def pullbackInclusion : MembershipEndExtension (B.pullbackContext hπ hs).Model B.Model :=
  (B.pullbackRealization hπ hs).embedding

theorem pullbackInclusion_check (x : V) :
    B.pullbackInclusion hπ hs ((B.pullbackContext hπ hs).check x) = B.check x :=
  (B.pullbackRealization hπ hs).value_check x

theorem pullbackInclusion_ofName (τ : ForcingName Q) :
    B.pullbackInclusion hπ hs ((B.pullbackContext hπ hs).ofName τ) =
      B.ofName ⟨nameAction π τ.val, nameAction_isName hπ τ.property⟩ := by
  change nameValue (B.pullbackGenericSet Q π) (B.check τ.val) = _
  rw [← B.nameValue_genericSet_check]
  rw [show B.check (nameAction π τ.val) = nameAction (B.check π) (B.check τ.val)
    from B.checkEmbedding.map_nameAction π τ.val]
  symm
  apply nameValue_nameAction_of_membership ((B.checkEmbedding.forcingName_iff Q τ.val).mp τ.property)
  intro p hp
  change p ∈ B.check Q at hp
  simp only [pullbackGenericSet, mem_sep_iff, hp, true_and]

end ForcingContext
end ZFVP
