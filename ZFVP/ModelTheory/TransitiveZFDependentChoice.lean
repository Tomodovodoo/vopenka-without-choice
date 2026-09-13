import ZFVP.ModelTheory.TransitiveZFValues
import ZFVP.SetTheory.DependentChoiceFailureCertificate

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoice_of_functionClosed (κ : SetDomain U)
    (hclosed : ∀ A ∈ U, ∀ β ∈ succ κ.val, ∀ f ∈ A ^ β, f ∈ U)
    (hDC : InternalDependentChoiceAt κ.val) : InternalDependentChoiceAt κ := by
  intro A R hA hserial
  have hne : IsNonempty A.val := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a.val, ha⟩
  have hs : ∀ s ∈ shorterSequences κ.val A.val, ∃ x ∈ A.val, ⟨s, x⟩ₖ ∈ R.val := by
    intro s hs
    obtain ⟨β, hβ, hsf⟩ := (mem_shorterSequences _ _ _).mp hs
    let β' : SetDomain U := ⟨β, (inferInstance : IsTransitive U).mem_trans hβ κ.property⟩
    let s' : SetDomain U := ⟨s, hclosed A.val A.property β (mem_succ_iff.mpr (Or.inr hβ)) s hsf⟩
    have hs' : s' ∈ shorterSequences κ A :=
      (mem_shorterSequences _ _ _).mpr ⟨β', hβ, (function_iff U s' β' A).mpr hsf⟩
    obtain ⟨x, hx, hp⟩ := hserial s' hs'
    refine ⟨x.val, hx, ?_⟩
    change (⟨s', x⟩ₖ : SetDomain U).val ∈ R.val at hp
    simpa only [kpair_val U] using hp
  obtain ⟨f, hf, hsteps⟩ := hDC A.val R.val hne hs
  let f' : SetDomain U := ⟨f, hclosed A.val A.property κ.val (mem_succ_self _) f hf⟩
  refine ⟨f', (function_iff U f' κ A).mpr hf, ?_⟩
  intro β hβ
  change (⟨f' ↾ β, f' ‘ β⟩ₖ : SetDomain U).val ∈ R.val
  simpa only [kpair_val U, restrict_val U, value_val_total U] using hsteps β.val hβ

theorem not_dependentChoice_of_bounded_failure (κ B : SetDomain U)
    (hκ : IsOrdinal κ.val) (hf : IsBoundedDependentChoiceFailure κ.val B.val)
    (hclosed : ∀ A ∈ B.val, ∀ β ∈ succ κ.val, ∀ f ∈ A ^ β, f ∈ B.val) :
    ¬InternalDependentChoiceAt κ := by
  let := (ordinal_iff U κ).mpr hκ
  have hf' : IsBoundedDependentChoiceFailure κ B :=
    (bounded_defined_absolute U boundedDependentChoiceFailureFormula_bounded
      (fun v ↦ IsBoundedDependentChoiceFailure (v 0) (v 1))
      (fun v ↦ IsBoundedDependentChoiceFailure (v 0) (v 1)) ![κ, B]).mpr hf
  apply hf'.not_dependentChoice
  intro A hA β hβ f hfunc
  have hβ' : β.val ∈ succ κ.val := by
    change β.val ∈ (succ κ).val at hβ
    simpa only [succ_val U] using hβ
  exact hclosed A.val hA β.val hβ' f.val ((function_iff U f β A).mp hfunc)

end TransitiveZF

theorem rank_dependentChoice_of_ambient {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (κ : SetDomain (hierarchy ξ))
    (hκ : IsOrdinal κ.val) (hDC : InternalDependentChoiceAt κ.val) :
    InternalDependentChoiceAt κ := by
  let := hκ
  let := hierarchy_transitive ξ
  apply TransitiveZF.dependentChoice_of_functionClosed (hierarchy ξ) κ ?_ hDC
  intro A hA β hβ f hf
  have hsκ : succ κ.val ∈ ξ := hs _ (ordinal_mem_hierarchy_iff.mp κ.property)
  have hβξ := IsOrdinal.toIsTransitive.mem_trans hβ hsκ
  let := IsOrdinal.of_mem hβξ
  exact (hierarchy_transitive ξ).mem_trans hf
    (function_mem_hierarchy_limit hs (ordinal_mem_hierarchy_iff.mpr hβξ) hA)

end ZFVP
