import ZFVP.SetTheory.FiniteSets
import ZFVP.SetTheory.Collection
import ZFVP.SetTheory.InternalChoice
import ZFVP.SetTheory.SchroederBernstein

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Ground choice selects internal bijective finite enumerations for a definable family of
internally finite sets. Collection first bounds the available enumerations by one set. -/
theorem finite_domain_enumeration_family (hAC : InternalChoice V) (D : V)
    (E : V → V) (hE : ℒₛₑₜ-function₁[V] E)
    (hfin : ∀ z ∈ D, IsInternallyFinite (E z)) :
    ∃ s : V, IsFunction s ∧ domain s = D ∧ ∀ z ∈ D, ∃ n ∈ (ω : V),
      s ‘ z ∈ (E z) ^ n ∧ Injective (s ‘ z) ∧ range (s ‘ z) = E z := by
  let R := fun z e : V ↦ ∃ n ∈ (ω : V), e ∈ (E z) ^ n ∧ Injective e ∧ range e = E z
  have hR : ℒₛₑₜ-relation R := by
    dsimp [R]
    definability
  have hex : ∀ z ∈ D, ∃ e, R z e := by
    intro z hz
    obtain ⟨n, hn, hEn⟩ := hfin z hz
    obtain ⟨e, he, hei, her⟩ := exists_bijection_of_cardEQ (And.intro hEn.2 hEn.1)
    exact ⟨e, n, hn, he, hei, her⟩
  obtain ⟨C, hC⟩ := collection D R hR hex
  let F := fun z : V ↦ {e ∈ C ; R z e}
  have hF : ℒₛₑₜ-function₁[V] F := by
    have h : ℒₛₑₜ-relation (fun S z : V ↦ ∀ e, e ∈ S ↔ e ∈ C ∧ R z e) := by definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp only [F, mem_sep_iff]
    rfl
  obtain ⟨s, hs, hsd, hsel⟩ := choice_for_definable_family hAC D F hF (by
    intro z hz
    obtain ⟨e, heC, heR⟩ := hC z hz
    exact ⟨e, mem_sep_iff.mpr ⟨heC, heR⟩⟩)
  exact ⟨s, hs, hsd, fun z hz ↦ (mem_sep_iff.mp (hsel z hz)).2⟩

/-- Precomposition by a surjective internal function cancels from equality of functions. -/
theorem compose_cancel_surjective {n B A e a c : V} (he : e ∈ B ^ n)
    (hr : range e = B) (ha : a ∈ A ^ B) (hc : c ∈ A ^ B)
    (heq : compose e a = compose e c) : a = c := by
  have : IsFunction e := IsFunction.of_mem he
  have : IsFunction a := IsFunction.of_mem ha
  have : IsFunction c := IsFunction.of_mem hc
  have hv : ∀ x ∈ B, a ‘ x = c ‘ x := by
    intro x hx
    obtain ⟨k, hkx⟩ := mem_range_iff.mp (hr.symm ▸ hx)
    have hk : k ∈ n := (mem_of_mem_functions he hkx).1
    have hek : e ‘ k = x := value_eq_of_kpair_mem hkx
    have hval := congrArg (fun f : V ↦ f ‘ k) heq
    rw [value_compose_of_mem_function he ha hk, value_compose_of_mem_function he hc hk, hek] at hval
    exact hval
  apply function_ext ha hc
  intro x hx y _hy hxy
  have hy : y = c ‘ x := (value_eq_of_kpair_mem hxy).symm.trans (hv x hx)
  rw [hy]
  exact kpair_value_mem ((domain_eq_of_mem_function hc).symm ▸ hx)

end ZFVP

