import ZFVP.ModelTheory.TransitiveZFInaccessible
import ZFVP.SetTheory.CardinalSmallUnions
import ZFVP.SetTheory.PiOneInitialOrdinal

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem injection_iff (f A B : SetDomain U) :
    (f ∈ B ^ A ∧ Injective f) ↔ f.val ∈ B.val ^ A.val ∧ Injective f.val :=
  bounded_defined_absolute U boundedInjectionFormula_bounded
    (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ Injective (v 0))
    (fun v ↦ v 0 ∈ v 2 ^ v 1 ∧ Injective (v 0)) ![f, A, B]

end TransitiveZF

theorem rank_cardLE_iff {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (A B : SetDomain (hierarchy ξ)) :
    A ≤# B ↔ A.val ≤# B.val := by
  let := hierarchy_transitive ξ
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.val, (TransitiveZF.injection_iff (hierarchy ξ) f A B).mp hf⟩
  · rintro ⟨f, hf⟩
    have hfU := (hierarchy_transitive ξ).mem_trans hf.1
      (function_mem_hierarchy_limit hs A.property B.property)
    exact ⟨⟨f, hfU⟩, (TransitiveZF.injection_iff (hierarchy ξ) ⟨f, hfU⟩ A B).mpr hf⟩

theorem rank_cardinalSmall_iff {ξ : V} [IsOrdinal ξ]
    [Nonempty (SetDomain (hierarchy ξ))] [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hs : ∀ β ∈ ξ, succ β ∈ ξ) (κ A : SetDomain (hierarchy ξ)) :
    IsCardinalSmall κ A ↔ IsCardinalSmall κ.val A.val := by
  let := hierarchy_transitive ξ
  unfold IsCardinalSmall
  apply TransitiveZF.exists_mem_val_iff (hierarchy ξ) κ
  intro α
  exact rank_cardLE_iff hs A α

end ZFVP
