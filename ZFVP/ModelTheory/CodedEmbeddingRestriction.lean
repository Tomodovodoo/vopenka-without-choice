import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.SetTheory.TransitiveRestriction

/-! The restriction of an internal embedding graph represents the elementary restriction map. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace IsCodedMembershipEmbedding

variable {A B f a : V} [hA : IsTransitive A] [IsTransitive B]

omit [IsTransitive B] in
theorem restriction_function (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A) :
    f ↾ a ∈ (f ‘ a) ^ a := by
  have : IsFunction f := IsFunction.of_mem h.function
  apply restrict_mem_function_of_values
  · intro x hx
    rw [domain_eq_of_mem_function h.function]
    exact hA.mem_trans hx ha
  · intro x hx
    exact (h.value_mem_iff (hA.mem_trans hx ha) ha).mpr hx

noncomputable def restrictElementaryMap (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A) :
    ElementaryMap (SetDomain a) (SetDomain (f ‘ a)) :=
  transitiveRestriction A B h.toElementaryMap ⟨a, ha⟩

theorem restrictElementaryMap_value (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A)
    (x : SetDomain a) : (h.restrictElementaryMap ha x).val = (f ↾ a) ‘ x.val := by
  have : IsFunction f := IsFunction.of_mem h.function
  change value f x.val = value (restrict f a) x.val
  exact (value_restrict (by
    rw [domain_eq_of_mem_function h.function]
    exact hA.mem_trans x.property ha) x.property).symm

theorem restriction_eval (h : IsCodedMembershipEmbedding A B f) (ha : a ∈ A)
    {ξ : Type} {n : ℕ} (φ : SetTheorySemiformula ξ n)
    (b : Fin n → SetDomain a) (e : ξ → SetDomain a) :
    φ.Eval b e ↔
      φ.Eval (M := SetDomain (f ‘ a)) (fun i ↦ (⟨(f ↾ a) ‘ (b i).val,
        function_value_mem (h.restriction_function ha) (b i).property⟩ : SetDomain (f ‘ a)))
      (fun i ↦ (⟨(f ↾ a) ‘ (e i).val,
        function_value_mem (h.restriction_function ha) (e i).property⟩ : SetDomain (f ‘ a))) := by
  have hb : (h.restrictElementaryMap ha ∘ b) =
      (fun i ↦ (⟨(f ↾ a) ‘ (b i).val,
        function_value_mem (h.restriction_function ha) (b i).property⟩ : SetDomain (f ‘ a))) := by
    funext i
    exact Subtype.ext (h.restrictElementaryMap_value ha (b i))
  have he : (h.restrictElementaryMap ha ∘ e) =
      (fun i ↦ (⟨(f ↾ a) ‘ (e i).val,
        function_value_mem (h.restriction_function ha) (e i).property⟩ : SetDomain (f ‘ a))) := by
    funext i
    exact Subtype.ext (h.restrictElementaryMap_value ha (e i))
  rw [← hb, ← he]
  exact (h.restrictElementaryMap ha).elementary φ b e

end IsCodedMembershipEmbedding

end ZFVP
