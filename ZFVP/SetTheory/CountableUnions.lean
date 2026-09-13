import ZFVP.SetTheory.CountableChoice
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.NaturalPairing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsInternallyCountable (A : V) : Prop := A ≤# (ω : V)

instance isInternallyCountable_definable : ℒₛₑₜ-predicate[V] IsInternallyCountable := by
  unfold IsInternallyCountable
  definability

noncomputable def firstCoverIndex (C x : V) : V := ⋂ˢ {n ∈ (ω : V) ; x ∈ C ‘ n}

instance firstCoverIndex_definable : ℒₛₑₜ-function₂[V] firstCoverIndex := by
  have h : ℒₛₑₜ-function₂[V] (fun C x ↦ {n ∈ (ω : V) ; x ∈ C ‘ n}) := by
    have hrel : ℒₛₑₜ-relation₃[V] (fun N C x ↦ ∀ n, n ∈ N ↔ n ∈ (ω : V) ∧ x ∈ C ‘ n) := by
      definability
    apply Language.Definable.of_iff hrel
    intro v
    rw [mem_ext_iff]
    simp
  unfold firstCoverIndex
  definability

theorem firstCoverIndex_spec {C x : V} [IsFunction C] (hd : domain C = (ω : V))
    (hx : x ∈ ⋃ˢ range C) : firstCoverIndex C x ∈ (ω : V) ∧ x ∈ C ‘ (firstCoverIndex C x) := by
  obtain ⟨X, hX, hxX⟩ := mem_sUnion_iff.mp hx
  obtain ⟨n, hnX⟩ := mem_range_iff.mp hX
  have hn : n ∈ (ω : V) := hd ▸ mem_domain_of_kpair_mem hnX
  have hxCn : x ∈ C ‘ n := (value_eq_of_kpair_mem hnX).symm ▸ hxX
  let S : V := {n ∈ (ω : V) ; x ∈ C ‘ n}
  have : IsNonempty S := ⟨n, mem_sep_iff.mpr ⟨hn, hxCn⟩⟩
  have hm := IsOrdinal.sInter_mem (X := S) (fun n hn ↦ IsOrdinal.of_mem (mem_sep_iff.mp hn).1)
  exact mem_sep_iff.mp hm

theorem countable_family_injections (hCC : InternalCountableChoice V) {C : V}
    (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n)) :
    ∃ g, IsFunction g ∧ domain g = (ω : V) ∧
      ∀ n ∈ (ω : V), g ‘ n ∈ (ω : V) ^ (C ‘ n) ∧ Injective (g ‘ n) := by
  let B : V → V := fun n ↦ {f ∈ (ω : V) ^ (C ‘ n) ; Injective f}
  have hB : ℒₛₑₜ-function₁ B := by
    have h : ℒₛₑₜ-relation (fun S n : V ↦ ∀ f, f ∈ S ↔ f ∈ (ω : V) ^ (C ‘ n) ∧ Injective f) := by
      definability
    apply Language.Definable.of_iff h
    intro v
    rw [mem_ext_iff]
    simp [B]
  let b := definableGraph (ω : V) B hB
  have hb (n : V) (hn : n ∈ (ω : V)) : b ‘ n = B n := value_definableGraph _ _ _ hn
  have hnB : ∀ n ∈ (ω : V), IsNonempty (b ‘ n) := by
    intro n hn
    obtain ⟨f, hf, hfi⟩ := hcount n hn
    rw [hb n hn]
    exact ⟨f, mem_sep_iff.mpr ⟨hf, hfi⟩⟩
  obtain ⟨g, hg, hval⟩ := hCC b (definableGraph_isFunction _ _ _) (domain_definableGraph _ _ _) hnB
  refine ⟨g, IsFunction.of_mem hg, domain_eq_of_mem_function hg, ?_⟩
  intro n hn
  have hm := hval n hn
  rw [hb n hn] at hm
  exact mem_sep_iff.mp hm

theorem union_cardLE_omega_prod_of_injection_family {C g : V} [IsFunction C]
    (hd : domain C = (ω : V))
    (hg : ∀ n ∈ (ω : V), g ‘ n ∈ (ω : V) ^ (C ‘ n) ∧ Injective (g ‘ n)) :
    (⋃ˢ range C) ≤# ((ω : V) ×ˢ (ω : V)) := by
  let F : V → V := fun x ↦ ⟨firstCoverIndex C x, (g ‘ (firstCoverIndex C x)) ‘ x⟩ₖ
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let f := definableGraph (⋃ˢ range C) F hF
  have hf : f ∈ ((ω : V) ×ˢ (ω : V)) ^ (⋃ˢ range C) :=
    definableGraph_mem_function_of_mapsTo _ _ _ _ (by
      intro x hx
      have hs := firstCoverIndex_spec hd hx
      exact kpair_mem_iff.mpr ⟨hs.1, function_value_mem (hg _ hs.1).1 hs.2⟩)
  refine ⟨f, hf, ?_⟩
  intro x y z hx hy
  obtain ⟨hxU, hzx⟩ := (pair_mem_definableGraph_iff _ F hF x z).mp hx
  obtain ⟨hyU, hzy⟩ := (pair_mem_definableGraph_iff _ F hF y z).mp hy
  have heq : F x = F y := hzx.symm.trans hzy
  have hpair := kpair_iff.mp heq
  have hx' := firstCoverIndex_spec hd hxU
  have hy' := firstCoverIndex_spec hd hyU
  have hxy : y ∈ C ‘ (firstCoverIndex C x) := hpair.1.symm ▸ hy'.2
  have hval : (g ‘ (firstCoverIndex C x)) ‘ x = (g ‘ (firstCoverIndex C x)) ‘ y := by
    simpa only [← hpair.1] using hpair.2
  exact injective_value_eq (hg _ hx'.1).1 (hg _ hx'.1).2 hx'.2 hxy hval

theorem union_cardLE_omega_prod_of_countableChoice (hCC : InternalCountableChoice V)
    {C : V} [IsFunction C] (hd : domain C = (ω : V))
    (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n)) :
    (⋃ˢ range C) ≤# ((ω : V) ×ˢ (ω : V)) := by
  obtain ⟨g, _, _, hg⟩ := countable_family_injections hCC hcount
  exact union_cardLE_omega_prod_of_injection_family hd hg

theorem countable_union_of_countableChoice (hCC : InternalCountableChoice V)
    {C : V} [IsFunction C] (hd : domain C = (ω : V))
    (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n)) :
    IsInternallyCountable (⋃ˢ range C) :=
  (union_cardLE_omega_prod_of_countableChoice hCC hd hcount).trans omega_prod_cardLE_omega

theorem countable_union_of_dependentChoice (hDC : InternalDependentChoice V)
    {C : V} [IsFunction C] (hd : domain C = (ω : V))
    (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n)) :
    IsInternallyCountable (⋃ˢ range C) :=
  countable_union_of_countableChoice (countableChoice_of_dependentChoice hDC) hd hcount

theorem not_countableChoice_of_uncountable_union {C : V} [IsFunction C]
    (hd : domain C = (ω : V)) (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n))
    (hU : ¬IsInternallyCountable (⋃ˢ range C)) : ¬InternalCountableChoice V :=
  fun hCC ↦ hU (countable_union_of_countableChoice hCC hd hcount)

theorem not_dependentChoice_of_uncountable_union {C : V} [IsFunction C]
    (hd : domain C = (ω : V)) (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n))
    (hU : ¬IsInternallyCountable (⋃ˢ range C)) : ¬InternalDependentChoice V :=
  fun hDC ↦ hU (countable_union_of_dependentChoice hDC hd hcount)

theorem power_omega_not_countable : ¬IsInternallyCountable (power (ω : V)) :=
  (cardLT_power (ω : V)).2

theorem not_countableChoice_of_countable_cover_power_omega {C : V} [IsFunction C]
    (hd : domain C = (ω : V)) (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n))
    (hcover : ⋃ˢ range C = power (ω : V)) : ¬InternalCountableChoice V := by
  apply not_countableChoice_of_uncountable_union hd hcount
  rw [hcover]
  exact power_omega_not_countable

theorem not_dependentChoice_of_countable_cover_power_omega {C : V} [IsFunction C]
    (hd : domain C = (ω : V)) (hcount : ∀ n ∈ (ω : V), IsInternallyCountable (C ‘ n))
    (hcover : ⋃ˢ range C = power (ω : V)) : ¬InternalDependentChoice V :=
  not_dependentChoice_of_not_countableChoice (not_countableChoice_of_countable_cover_power_omega hd hcount hcover)

def internallyCountableFormula : SetTheorySemisentence 1 := f“A. !CardLE.dfn A (!isω)”

instance internallyCountableFormula_defined :
    ℒₛₑₜ-predicate[V] IsInternallyCountable via internallyCountableFormula :=
  ⟨fun v ↦ by simp [internallyCountableFormula, IsInternallyCountable]⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_internallyCountable_iff (j : ElementaryMap V W) (A : V) :
    IsInternallyCountable (j A) ↔ IsInternallyCountable A :=
  (j.map_defined internallyCountableFormula (fun v ↦ IsInternallyCountable (v 0))
    (fun v ↦ IsInternallyCountable (v 0)) ![A]).symm

end ElementaryMap
end ZFVP
