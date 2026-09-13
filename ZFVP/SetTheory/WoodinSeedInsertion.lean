import ZFVP.SetTheory.WoodinSourceIndex
import ZFVP.SetTheory.FunctionUnion

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def woodinInsertSeedValue (f a β : V) : V := by
  classical
  exact if β = ∅ then a else f ‘ (woodinRecursiveIndex β)

instance woodinInsertSeedValue_definable : ℒₛₑₜ-function₃[V] woodinInsertSeedValue := by
  have hd : ℒₛₑₜ-relation₄ (fun z f a β : V ↦
      (β = ∅ ∧ z = a) ∨ (β ≠ ∅ ∧ z = f ‘ (woodinRecursiveIndex β))) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = woodinInsertSeedValue (v 1) (v 2) (v 3) ↔ _
  classical
  by_cases h : v 3 = ∅ <;> simp [woodinInsertSeedValue, h]

noncomputable def woodinInsertSeed (θ f a : V) : V :=
  definableGraph (woodinSourceIndex θ) (woodinInsertSeedValue f a) (by definability)

noncomputable def woodinRemoveSeed (θ g : V) : V :=
  definableGraph θ (fun α ↦ g ‘ (woodinSourceIndex α)) (by definability)

instance woodinInsertSeed_isFunction (θ f a : V) : IsFunction (woodinInsertSeed θ f a) := by
  unfold woodinInsertSeed
  infer_instance

instance woodinRemoveSeed_isFunction (θ g : V) : IsFunction (woodinRemoveSeed θ g) := by
  unfold woodinRemoveSeed
  infer_instance

theorem woodinInsertSeed_domain (θ f a : V) : domain (woodinInsertSeed θ f a) = woodinSourceIndex θ :=
  domain_definableGraph _ _ _

theorem woodinRemoveSeed_domain (θ g : V) : domain (woodinRemoveSeed θ g) = θ :=
  domain_definableGraph _ _ _

theorem woodinInsertSeed_zero (θ f a : V) [IsOrdinal θ] : (woodinInsertSeed θ f a) ‘ ∅ = a := by
  have hz : (∅ : V) ∈ woodinSourceIndex θ :=
    subset_ordinalAdd 1 θ ∅ (by change (0 : V) ∈ succ 0; simp)
  rw [woodinInsertSeed, value_definableGraph _ _ _ hz]
  simp [woodinInsertSeedValue]

theorem woodinInsertSeed_nonzero {θ f a β : V} [IsOrdinal θ]
    (hβ : β ∈ woodinSourceIndex θ) (hne : β ≠ ∅) :
    (woodinInsertSeed θ f a) ‘ β = f ‘ (woodinRecursiveIndex β) := by
  rw [woodinInsertSeed, value_definableGraph _ _ _ hβ]
  simp [woodinInsertSeedValue, hne]

theorem woodinInsertSeed_at_sourceIndex {θ f a α : V} [IsOrdinal θ] (hα : α ∈ θ) :
    (woodinInsertSeed θ f a) ‘ (woodinSourceIndex α) = f ‘ α := by
  let := IsOrdinal.of_mem hα
  rw [woodinInsertSeed_nonzero (woodinSourceIndex_mem_iff.mpr hα) (woodinSourceIndex_nonzero α),
    woodinRecursiveIndex_sourceIndex]

theorem woodinRemoveSeed_value {θ g α : V} (hα : α ∈ θ) :
    (woodinRemoveSeed θ g) ‘ α = g ‘ (woodinSourceIndex α) := value_definableGraph _ _ _ hα

theorem woodinRemoveSeed_insert {θ f a : V} [IsOrdinal θ] [IsFunction f] (hf : domain f = θ) :
    woodinRemoveSeed θ (woodinInsertSeed θ f a) = f := by
  apply functions_eq_of_domain_values ((woodinRemoveSeed_domain _ _).trans hf.symm)
  intro α hα
  rw [woodinRemoveSeed_domain] at hα
  rw [woodinRemoveSeed_value hα, woodinInsertSeed_at_sourceIndex hα]

theorem woodinInsertSeed_remove {θ g a : V} [IsOrdinal θ] [IsFunction g]
    (hg : domain g = woodinSourceIndex θ) (hzero : g ‘ ∅ = a) :
    woodinInsertSeed θ (woodinRemoveSeed θ g) a = g := by
  apply functions_eq_of_domain_values ((woodinInsertSeed_domain _ _ _).trans hg.symm)
  intro β hβ
  rw [woodinInsertSeed_domain] at hβ
  by_cases hz : β = ∅
  · subst β
    rw [woodinInsertSeed_zero, hzero]
  · let := IsOrdinal.of_mem hβ
    rw [woodinInsertSeed_nonzero hβ hz,
      woodinRemoveSeed_value ((woodinRecursiveIndex_mem_iff hz).mpr hβ),
      woodinSourceIndex_recursiveIndex β hz]

theorem woodinInsertSeed_function {θ f A a : V} [IsOrdinal θ] (hf : f ∈ A ^ θ) (ha : a ∈ A) :
    woodinInsertSeed θ f a ∈ A ^ woodinSourceIndex θ := by
  unfold woodinInsertSeed
  apply definableGraph_mem_function_of_mapsTo
  intro β hβ
  classical
  by_cases hz : β = ∅
  · simpa only [woodinInsertSeedValue, hz, ↓reduceIte] using ha
  · let := IsOrdinal.of_mem hβ
    simpa only [woodinInsertSeedValue, hz, ↓reduceIte] using
      function_value_mem hf ((woodinRecursiveIndex_mem_iff hz).mpr hβ)

theorem woodinRemoveSeed_function {θ g A : V} [IsOrdinal θ]
    (hg : g ∈ A ^ woodinSourceIndex θ) : woodinRemoveSeed θ g ∈ A ^ θ := by
  unfold woodinRemoveSeed
  apply definableGraph_mem_function_of_mapsTo
  intro α hα
  let := IsOrdinal.of_mem hα
  exact function_value_mem hg (woodinSourceIndex_mem_iff.mpr hα)

end ZFVP
