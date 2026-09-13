import ZFVP.ModelTheory.TransitiveZFRecursion
import ZFVP.ModelTheory.TransitiveZFValues
import ZFVP.SetTheory.NameClosureRecursion
import ZFVP.SetTheory.NameActionClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace TransitiveZF

variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem nameClosure_val (τ : SetDomain U) : (nameClosure τ).val = nameClosure τ.val := by
  rw [nameClosure_eq_subnameRecursion, nameClosure_eq_subnameRecursion]
  apply subnameRecursion_val U
  intro σ _ g _
  unfold nameClosureStep
  rw [insert_val U, sUnion_val U, range_val U]

theorem forcingName_iff (P τ : SetDomain U) : IsForcingName P τ ↔ IsForcingName P.val τ.val := by
  constructor
  · intro hτ σ hσ z hz
    have hσ' : σ ∈ (nameClosure τ).val := nameClosure_val U τ ▸ hσ
    let σ' : SetDomain U := ⟨σ, (inferInstance : IsTransitive U).mem_trans hσ' (nameClosure τ).property⟩
    let z' : SetDomain U := ⟨z, (inferInstance : IsTransitive U).mem_trans hz σ'.property⟩
    obtain ⟨υ, p, hp, he⟩ := hτ σ' hσ' z' hz
    refine ⟨υ.val, p.val, hp, ?_⟩
    have hv := congrArg Subtype.val he
    simpa only [kpair_val U] using hv
  · intro hτ σ hσ z hz
    have hσ' : σ.val ∈ nameClosure τ.val := nameClosure_val U τ ▸ hσ
    obtain ⟨υ, p, hp, he⟩ := hτ σ.val hσ' z.val hz
    have hup := kpair_components_mem_transitive (he ▸ z.property)
    let υ' : SetDomain U := ⟨υ, hup.1⟩
    let p' : SetDomain U := ⟨p, hup.2⟩
    refine ⟨υ', p', hp, ?_⟩
    apply Subtype.ext
    simpa only [kpair_val U] using he

theorem checkName_val (one x : SetDomain U) : (checkName one x).val = checkName one.val x.val := by
  unfold checkName
  apply membershipRecursion_val U
  intro σ _ g _
  unfold checkNameStep
  apply repl_val U
  intro y _
  rw [kpair_val U, value_val_total U]

theorem nameAction_val (P π τ : SetDomain U) (hτ : IsForcingName P τ) :
    (nameAction π τ).val = nameAction π.val τ.val := by
  unfold nameAction
  apply subnameRecursion_val U
  intro σ hσ g _
  unfold nameActionStep
  apply repl_val U
  intro w hw
  obtain ⟨υ, p, _, rfl⟩ := (forcingName_mem_closure hτ hσ) σ (mem_nameClosure_self σ) w hw
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_val U, value_val_total U]

end TransitiveZF
end ZFVP
