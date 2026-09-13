import ZFVP.ModelTheory.TransitiveZFSetOperations
import ZFVP.SetTheory.SubnameRecursion
import ZFVP.SetTheory.MembershipRecursion

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem subnameRecursionTable_val (C f : SetDomain U)
    (F : SetDomain U → SetDomain U → SetDomain U) (G : V → V → V)
    (hf : IsSubnameRecursion C F f)
    (hstep : ∀ σ ∈ C, ∀ g : SetDomain U, IsFunction g → (F σ g).val = G σ.val g.val) :
    IsSubnameRecursion C.val G f.val := by
  have : IsFunction f := hf.1
  have hfun := (function_on_iff U f C).mp ⟨hf.1, hf.2.1⟩
  refine ⟨hfun.1, hfun.2, ?_⟩
  intro σ hσ
  let σ' : SetDomain U := ⟨σ, (inferInstance : IsTransitive U).mem_trans hσ C.property⟩
  have he := congrArg Subtype.val (hf.2.2 σ' hσ)
  rw [value_val U f σ' (hf.2.1.symm ▸ hσ), hstep σ' hσ _ inferInstance,
    restrict_val U, domain_val U] at he
  exact he

theorem subnameRecursion_val
    (F : SetDomain U → SetDomain U → SetDomain U) (hF : ℒₛₑₜ-function₂ F)
    (G : V → V → V) (hG : ℒₛₑₜ-function₂ G) (τ : SetDomain U)
    (hstep : ∀ σ ∈ nameClosure τ, ∀ g : SetDomain U, IsFunction g → (F σ g).val = G σ.val g.val) :
    (subnameRecursion F hF τ).val = subnameRecursion G hG τ.val := by
  let f := subnameRecursionTable F hF τ
  have hf := subnameRecursionTable_spec F hF τ
  have : IsFunction f := hf.1
  have hC := subnameClosed_val U (nameClosure τ) (nameClosure_closed τ)
  have ht : τ ∈ nameClosure τ := mem_nameClosure_self τ
  have htval : τ.val ∈ (nameClosure τ).val := ht
  have he := subnameRecursion_coherent hC (nameClosure_closed τ.val)
    (subnameRecursionTable_val U _ _ F G hf hstep) (subnameRecursionTable_spec G hG τ.val)
    τ.val htval (mem_nameClosure_self τ.val)
  change (f ‘ τ).val = _
  rw [value_val U f τ (hf.2.1.symm ▸ ht)]
  exact he

theorem membershipRecursionTable_val (C f : SetDomain U)
    (F : SetDomain U → SetDomain U → SetDomain U) (G : V → V → V)
    (hf : IsMembershipRecursion C F f)
    (hstep : ∀ x ∈ C, ∀ g : SetDomain U, IsFunction g → (F x g).val = G x.val g.val) :
    IsMembershipRecursion C.val G f.val := by
  have : IsFunction f := hf.1
  have hfun := (function_on_iff U f C).mp ⟨hf.1, hf.2.1⟩
  refine ⟨hfun.1, hfun.2, ?_⟩
  intro x hx
  let x' : SetDomain U := ⟨x, (inferInstance : IsTransitive U).mem_trans hx C.property⟩
  have he := congrArg Subtype.val (hf.2.2 x' hx)
  rw [value_val U f x' (hf.2.1.symm ▸ hx), hstep x' hx _ inferInstance, restrict_val U] at he
  exact he

theorem membershipRecursion_val
    (F : SetDomain U → SetDomain U → SetDomain U) (hF : ℒₛₑₜ-function₂ F)
    (G : V → V → V) (hG : ℒₛₑₜ-function₂ G) (x : SetDomain U)
    (hstep : ∀ y ∈ transitiveClosure ({x} : SetDomain U), ∀ g : SetDomain U,
      IsFunction g → (F y g).val = G y.val g.val) :
    (membershipRecursion F hF x).val = membershipRecursion G hG x.val := by
  let f := membershipRecursionTable F hF x
  have hf := membershipRecursionTable_spec F hF x
  have : IsFunction f := hf.1
  have hC := transitive_val U _ (transitiveClosure_transitive ({x} : SetDomain U))
  have hx : x ∈ transitiveClosure ({x} : SetDomain U) := subset_transitiveClosure _ _ (by simp)
  have hxval : x.val ∈ (transitiveClosure ({x} : SetDomain U)).val := hx
  have he := membershipRecursion_coherent hC (transitiveClosure_transitive ({x.val} : V))
    (membershipRecursionTable_val U _ _ F G hf hstep) (membershipRecursionTable_spec G hG x.val)
    x.val hxval (subset_transitiveClosure _ _ (by simp))
  change (f ‘ x).val = _
  rw [value_val U f x (hf.2.1.symm ▸ hx)]
  exact he

end TransitiveZF
end ZFVP
