import ZFVP.ModelTheory.NormalizedMapDefinability
import ZFVP.ModelTheory.ForcingIsomorphismFormula
import ZFVP.ModelTheory.ForcingNameActionRank

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Translate a name and take the specified canonical representative over the new base. -/
noncomputable def normalizedIsomorphismName (Q S top f τ : V) : V :=
  forcingLeastRankName Q S top (nameAction f τ)

instance normalizedIsomorphismName_definable :
    Language.DefinableFunction₅ ℒₛₑₜ (normalizedIsomorphismName (V := V)) := by
  unfold normalizedIsomorphismName
  apply Language.DefinableFunction₄.comp <;> definability

theorem normalizedIsomorphismName_isName {P R Q S top f τ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hS : IsForcingPreorder Q S)
    (ht : top ∈ Q) (hτ : IsForcingName P τ) :
    IsForcingName Q (normalizedIsomorphismName Q S top f τ) :=
  forcingLeastRankName_isName hS ht (nameAction_isName hf.1 hτ)

theorem normalizedIsomorphismName_fixed {P R Q S top f τ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hS : IsForcingPreorder Q S)
    (ht : top ∈ Q) (hτ : IsForcingName P τ) :
    forcingLeastRankName Q S top (normalizedIsomorphismName Q S top f τ) =
      normalizedIsomorphismName Q S top f τ :=
  forcingLeastRankName_idempotent hS ht (nameAction_isName hf.1 hτ)

theorem normalizedIsomorphismName_equal {P R Q S top f τ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hS : IsForcingPreorder Q S)
    (ht : top ∈ Q) (hτ : IsForcingName P τ) :
    top ∈ atomicEquality Q S (nameAction f τ) (normalizedIsomorphismName Q S top f τ) :=
  forcingLeastRankName_forced_equal hS ht (nameAction_isName hf.1 hτ)

theorem normalizedIsomorphismName_empty {Q S top f : V}
    (hS : IsForcingPreorder Q S) (ht : top ∈ Q) :
    normalizedIsomorphismName Q S top f ∅ = ∅ := by
  unfold normalizedIsomorphismName
  rw [nameAction_empty, forcingLeastRankName_empty hS ht]

/-- Renormalization after an intermediate base change does not alter composition. -/
theorem normalizedIsomorphismName_comp {P R Q S A B top u f g τ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hg : IsForcingIsomorphism Q S A B g)
    (hS : IsForcingPreorder Q S) (hB : IsForcingPreorder A B)
    (ht : top ∈ Q) (hu : u ∈ A) (hgu : g ‘ top = u) (hτ : IsForcingName P τ) :
    normalizedIsomorphismName A B u g (normalizedIsomorphismName Q S top f τ) =
      normalizedIsomorphismName A B u (compose f g) τ := by
  have he := atomicEquality_isomorphism_forward hg (nameAction_isName hf.1 hτ)
    (normalizedIsomorphismName_isName hf hS ht hτ) (normalizedIsomorphismName_equal hf hS ht hτ)
  rw [hgu, nameAction_compose hf.1 hg.1 hτ] at he
  exact (forcingLeastRankName_congr hB hu (nameAction_isName (compose_function hf.1 hg.1) hτ)
    (nameAction_isName hg.1 (normalizedIsomorphismName_isName hf hS ht hτ)) he).symm

theorem normalizedIsomorphismName_inverse {P R Q S one top f τ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hR : IsForcingPreorder P R) (hS : IsForcingPreorder Q S)
    (ho : one ∈ P) (ht : top ∈ Q) (hft : f ‘ one = top) (hτ : IsForcingName P τ)
    (hfix : forcingLeastRankName P R one τ = τ) :
    normalizedIsomorphismName P R one (converseGraph f) (normalizedIsomorphismName Q S top f τ) = τ := by
  have hback : (converseGraph f) ‘ top = one := by rw [← hft, hf.inverse_value ho]
  rw [normalizedIsomorphismName_comp hf hf.inverse hS hR ht ho hback hτ,
    hf.compose_inverse]
  unfold normalizedIsomorphismName
  rw [nameAction_identity hτ, hfix]

theorem normalizedIsomorphismName_mem_hierarchy {P R Q S top f τ δ : V}
    (hf : IsForcingIsomorphism P R Q S f) (hS : IsForcingPreorder Q S) (ht : top ∈ Q)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hQ : Q ∈ hierarchy δ)
    (hτ : IsForcingName P τ) (hτδ : τ ∈ hierarchy δ) :
    normalizedIsomorphismName Q S top f τ ∈ hierarchy δ := by
  let := hδ.1
  have hfδ : f ∈ hierarchy δ := subset_mem_hierarchy_limit hδ.rankCriterion.2.2.1
    (prod_mem_hierarchy_limit hδ.rankCriterion.2.2.1 hP hQ) (subset_prod_of_mem_function hf.1)
  have ha := nameAction_isName hf.1 hτ
  have haδ := nameAction_mem_hierarchy_of_inaccessible hδ hP hfδ hτδ hτ
  exact forcingLeastRankName_mem_hierarchy_of_equiv hS ht ha ha
    (by rwa [atomicEquality_refl hS]) haδ

end ZFVP
