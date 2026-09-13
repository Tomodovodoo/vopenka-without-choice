import ZFVP.SetTheory.InternalOrderType
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.InverseFunction
import ZFVP.SetTheory.TransitiveClosure

/-! Coding sets by well-founded extensional relations on ordinals.

A transitive collapse is automatically well founded and extensional on its domain, so those two
side conditions never have to be checked separately. Under internal choice every set of the model
is the value of the Mostowski collapse of such a relation at some point of the ordinal, which is
the coding step behind Laver's ground-model definability theorem. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A relation that admits a transitive collapse is internally well founded on its domain:
minimal elements are found by pushing a subset forward and taking a membership-minimal value. -/
theorem isInternallyWellFounded_of_collapse {R D C f : V} (h : IsTransitiveCollapse R D C f) :
    IsInternallyWellFounded R D := by
  obtain ⟨hC, hf, hrange, hinj, hmem⟩ := h
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = D := domain_eq_of_mem_function hf
  intro A hAD hA
  have hmemS : ∀ a ∈ A, f ‘ a ∈ range (f ↾ A) := by
    intro a ha
    exact mem_range_iff.mpr ⟨a, kpair_mem_restrict_iff.mpr
      ⟨kpair_value_mem (by rw [hdom]; exact hAD a ha), ha⟩⟩
  have hSC : range (f ↾ A) ⊆ C := by
    intro z hz
    obtain ⟨u, hu⟩ := mem_range_iff.mp hz
    rw [← hrange]
    exact mem_range_of_kpair_mem (kpair_mem_restrict_iff.mp hu).1
  have hSne : IsNonempty (range (f ↾ A)) := by
    obtain ⟨a, ha⟩ := hA.nonempty
    exact ⟨f ‘ a, hmemS a ha⟩
  obtain ⟨s, hsS, hsmin⟩ := membershipRelation_wellFounded C (range (f ↾ A)) hSC hSne
  obtain ⟨a, hax⟩ := mem_range_iff.mp hsS
  obtain ⟨haf, haA⟩ := kpair_mem_restrict_iff.mp hax
  have hfa : f ‘ a = s := value_eq_of_kpair_mem haf
  refine ⟨a, haA, ?_⟩
  intro b hb hbaR
  have hfb : f ‘ b ∈ f ‘ a := (hmem b (hAD b hb) a (hAD a haA)).mpr hbaR
  have hbS : f ‘ b ∈ range (f ↾ A) := hmemS b hb
  exact hsmin (f ‘ b) hbS
    ((pair_mem_membershipRelation C _ _).mpr ⟨hSC _ hbS, hSC _ hsS, hfa ▸ hfb⟩)

/-- A relation that admits a transitive collapse is extensional on its domain. -/
theorem isExtensionalOn_of_collapse {R D C f : V} (h : IsTransitiveCollapse R D C f) :
    IsExtensionalOn R D := by
  obtain ⟨hC, hf, hrange, hinj, hmem⟩ := h
  have hfun : IsFunction f := IsFunction.of_mem hf
  have hdom : domain f = D := domain_eq_of_mem_function hf
  intro x hx y hy hpred
  apply hinj x hx y hy
  have hval : ∀ u, u ∈ D → f ‘ u ∈ C := by
    intro u hu
    rw [← hrange]
    exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hdom]; exact hu))
  have key : ∀ u ∈ D, ∀ v ∈ D, ∀ w : V, w ∈ f ‘ u →
      ∃ z ∈ D, f ‘ z = w ∧ (⟨z, u⟩ₖ ∈ R) := by
    intro u hu _ _ w hw
    have hwC : w ∈ C := hC.mem_trans hw (hval u hu)
    have hwr : w ∈ range f := by rw [hrange]; exact hwC
    obtain ⟨z, hz⟩ := mem_range_iff.mp hwr
    have hzD : z ∈ D := by rw [← hdom]; exact mem_domain_of_kpair_mem hz
    have hfz : f ‘ z = w := value_eq_of_kpair_mem hz
    exact ⟨z, hzD, hfz, (hmem z hzD u hu).mp (hfz ▸ hw)⟩
  apply mem_ext
  intro w
  constructor
  · intro hw
    obtain ⟨z, hzD, hfz, hzx⟩ := key x hx y hy w hw
    exact hfz ▸ (hmem z hzD y hy).mpr ((hpred z hzD).mp hzx)
  · intro hw
    obtain ⟨z, hzD, hfz, hzy⟩ := key y hy x hx w hw
    exact hfz ▸ (hmem z hzD x hx).mpr ((hpred z hzD).mpr hzy)

/-- The relation on `D` that a function `g` pulls back from membership between its values. -/
noncomputable def valueRelation (g D : V) : V :=
  {p ∈ D ×ˢ D ; g ‘ (kpair.π₁ p) ∈ g ‘ (kpair.π₂ p)}

@[simp] theorem pair_mem_valueRelation (g D x y : V) :
    ⟨x, y⟩ₖ ∈ valueRelation g D ↔ x ∈ D ∧ y ∈ D ∧ g ‘ x ∈ g ‘ y := by
  simp [valueRelation, and_assoc]

theorem valueRelation_subset (g D : V) : valueRelation g D ⊆ D ×ˢ D :=
  fun _ hp ↦ (mem_sep_iff.mp hp).1

/-- If `g` is an injection of `D` onto a transitive set `C`, then `g` is the transitive collapse
of the relation it pulls back from membership. -/
theorem isTransitiveCollapse_valueRelation {C D g : V} [IsTransitive C] (hg : g ∈ C ^ D)
    (hinj : Injective g) (hrange : range g = C) :
    IsTransitiveCollapse (valueRelation g D) D C g := by
  refine ⟨inferInstance, hg, hrange, ?_, ?_⟩
  · intro a ha b hb heq
    exact injective_value_eq hg hinj ha hb heq
  · intro a ha b hb
    rw [pair_mem_valueRelation]
    exact ⟨fun h ↦ ⟨ha, hb, h⟩, fun h ↦ h.2.2⟩

/-- Under internal choice every set is the value at some point of the Mostowski collapse of a
well-founded extensional relation on an ordinal. -/
theorem exists_set_code (hAC : InternalChoice V) (x : V) :
    ∃ β E t : V, IsOrdinal β ∧ E ⊆ β ×ˢ β ∧ IsInternallyWellFounded E β ∧ IsExtensionalOn E β ∧
      t ∈ β ∧ (mostowskiMap E β) ‘ t = x := by
  set T : V := transitiveClosure ({x} : V) with hT
  have hTtrans : IsTransitive T := transitiveClosure_transitive _
  have hxT : x ∈ T := subset_transitiveClosure ({x} : V) x (by simp)
  obtain ⟨R, hR⟩ := wellOrderable_of_internalChoice hAC T
  have hwf := hR.2.1
  have hext := internalWellOrder_extensional hR
  have hc := mostowskiMap_isTransitiveCollapse hwf hext
  set h : V := mostowskiMap R T with hh
  set β : V := range h with hβ
  have hβord : IsOrdinal β := internalOrderType_ordinal hR
  have hhf : h ∈ β ^ T := hc.2.1
  have hhfun : IsFunction h := IsFunction.of_mem hhf
  have hhdom : domain h = T := domain_eq_of_mem_function hhf
  have hhinj : Injective h := by
    intro u₁ u₂ y hu₁ hu₂
    have h₁ : u₁ ∈ T := by rw [← hhdom]; exact mem_domain_of_kpair_mem hu₁
    have h₂ : u₂ ∈ T := by rw [← hhdom]; exact mem_domain_of_kpair_mem hu₂
    exact hc.2.2.2.1 u₁ h₁ u₂ h₂
      ((value_eq_of_kpair_mem hu₁).trans (value_eq_of_kpair_mem hu₂).symm)
  set g : V := converseGraph h with hg
  have hgf : g ∈ T ^ β := converseGraph_mem_function hhf hhinj
  have hginj : Injective g := converseGraph_injective h
  have hgrange : range g = T := by rw [hg, range_converseGraph, hhdom]
  have hcol : IsTransitiveCollapse (valueRelation g β) β T g :=
    isTransitiveCollapse_valueRelation hgf hginj hgrange
  have hEwf : IsInternallyWellFounded (valueRelation g β) β :=
    isInternallyWellFounded_of_collapse hcol
  have hEext : IsExtensionalOn (valueRelation g β) β := isExtensionalOn_of_collapse hcol
  have hgeq : g = mostowskiMap (valueRelation g β) β := by
    rw [mostowskiMap_of_wellFounded hEwf]
    exact (transitiveCollapse_unique hEwf hcol).1
  refine ⟨β, valueRelation g β, h ‘ x, hβord, valueRelation_subset _ _, hEwf, hEext, ?_, ?_⟩
  · exact mem_range_of_kpair_mem (kpair_value_mem (by rw [hhdom]; exact hxT))
  · rw [← hgeq]
    exact converseGraph_value_value hhf hhinj hxT

end ZFVP
