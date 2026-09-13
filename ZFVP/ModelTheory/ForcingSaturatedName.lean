import ZFVP.SetTheory.ForcingSaturatedName
import ZFVP.ModelTheory.ForcingHierarchyEvaluation
import ZFVP.ModelTheory.ForcedOrderLaws

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ForcingContext

noncomputable def saturatedName (A : ForcingContext V) (U : V) (Q : ForcingName A.P) : ForcingName A.P :=
  ⟨forcingSaturatedName A.P A.R U Q.val, forcingSaturatedName_isName _ _ _ _⟩

theorem mem_saturatedName_iff (A : ForcingContext V) (U : V) (Q : ForcingName A.P) (x : A.Model) :
    x ∈ A.ofName ⟨forcingSaturatedName A.P A.R U Q.val, forcingSaturatedName_isName _ _ _ _⟩ ↔
      x ∈ A.ofName Q ∧ ∃ τ : ForcingName A.P, τ.val ∈ U ∧ x = A.ofName τ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨τ, p, hpG, hpair, rfl⟩
    obtain ⟨hτU, _, _, hmem⟩ := (pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hpair
    have ht : p ∈ forcingFormula A.P A.R nameMemberFormula (standardTuple ![τ.val, Q.val]) := by
      rwa [forcingFormula_nameMember]
    have he := (A.formula_truth nameMemberFormula ![τ, Q]).mpr ⟨p, hpG, ht⟩
    exact ⟨by simpa [nameMemberFormula] using he, τ, hτU, rfl⟩
  · rintro ⟨hx, τ, hτU, rfl⟩
    have he : nameMemberFormula.Evalb (fun i ↦ A.ofName (![τ, Q] i)) := by
      simpa [nameMemberFormula] using hx
    obtain ⟨p, hpG, hp⟩ := (A.formula_truth nameMemberFormula ![τ, Q]).mp he
    change p ∈ forcingFormula A.P A.R nameMemberFormula (standardTuple ![τ.val, Q.val]) at hp
    rw [forcingFormula_nameMember] at hp
    exact ⟨τ, p, hpG, (pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr
      ⟨hτU, A.generic.1.1 p hpG, τ.property, hp⟩, rfl⟩

theorem saturatedName_value (A : ForcingContext V) (U : V) (Q : ForcingName A.P)
    (hcover : ∀ x ∈ A.ofName Q, ∃ τ : ForcingName A.P, τ.val ∈ U ∧ x = A.ofName τ) :
    A.ofName ⟨forcingSaturatedName A.P A.R U Q.val, forcingSaturatedName_isName _ _ _ _⟩ = A.ofName Q := by
  apply mem_ext
  intro x
  rw [A.mem_saturatedName_iff U Q x]
  exact ⟨And.left, fun hx ↦ ⟨hx, hcover x hx⟩⟩

theorem saturatedName_value_of_domain (A : ForcingContext V) (U : V) (Q : ForcingName A.P)
    (hU : domain Q.val ⊆ U) :
    A.ofName ⟨forcingSaturatedName A.P A.R U Q.val, forcingSaturatedName_isName _ _ _ _⟩ = A.ofName Q := by
  apply A.saturatedName_value U Q
  intro x hx
  obtain ⟨τ, p, _, hp, rfl⟩ := (A.mem_ofName_iff Q x).mp hx
  exact ⟨τ, hU _ (mem_domain_of_kpair_mem hp), rfl⟩

theorem saturatedName_value_of_hierarchy (A : ForcingContext V) (δ : V) [IsOrdinal δ]
    (Q : ForcingName A.P) (hQ : A.ofName Q ⊆ hierarchy (A.check δ)) :
    A.ofName ⟨forcingSaturatedName A.P A.R (forcingNameHierarchy A.P δ) Q.val,
      forcingSaturatedName_isName _ _ _ _⟩ = A.ofName Q := by
  apply A.saturatedName_value _ Q
  intro x hx
  have hx' := hQ x hx
  rw [← A.hierarchyName_value δ] at hx'
  exact (A.mem_hierarchyName_iff δ x).mp hx'

end ForcingContext
end ZFVP

