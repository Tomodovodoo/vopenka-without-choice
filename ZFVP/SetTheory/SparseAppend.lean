import ZFVP.SetTheory.FunctionUnion
import ZFVP.SetTheory.FiniteCodingClosure

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsSparseFunctionOn (A p : V) : Prop :=
  IsFunction p ∧ domain p ⊆ A ∧ ∀ x ∈ domain p, p ‘ x ≠ ∅

instance isSparseFunctionOn_definable : ℒₛₑₜ-relation[V] IsSparseFunctionOn := by
  unfold IsSparseFunctionOn
  definability

theorem isSparseFunctionOn_empty (A : V) : IsSparseFunctionOn A (∅ : V) := by
  refine ⟨inferInstance, ?_, ?_⟩ <;> simp

noncomputable def sparseAppend (a p τ : V) : V := by
  classical
  exact if τ = ∅ then p else insert ⟨a, τ⟩ₖ p

instance sparseAppend_definable : ℒₛₑₜ-function₃[V] sparseAppend := by
  classical
  have h : ℒₛₑₜ-relation₄[V] (fun q a p τ ↦
      (τ = ∅ ∧ q = p) ∨ (τ ≠ ∅ ∧ q = insert ⟨a, τ⟩ₖ p)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = sparseAppend (v 1) (v 2) (v 3) ↔ _
  unfold sparseAppend
  split_ifs <;> simp_all

@[simp] theorem sparseAppend_empty (a p : V) : sparseAppend a p ∅ = p := by
  simp only [sparseAppend, ite_true]

theorem sparseAppend_nonempty {a p τ : V} (hτ : τ ≠ ∅) :
    sparseAppend a p τ = insert ⟨a, τ⟩ₖ p := by
  simp only [sparseAppend, ite_eq_right hτ]

theorem sparseAppend_isFunction {a p τ : V} [IsFunction p] (hp : domain p ⊆ a) :
    IsFunction (sparseAppend a p τ) := by
  classical
  by_cases hτ : τ = ∅
  · rw [hτ, sparseAppend_empty]
    infer_instance
  · rw [sparseAppend_nonempty hτ]
    exact IsFunction.insert p a τ (fun ha ↦ mem_irrefl a (hp a ha))

theorem sparseAppend_domain (a p τ : V) :
    domain (sparseAppend a p τ) =
      @ite V (τ = ∅) (Classical.propDecidable _) (domain p) (insert a (domain p)) := by
  classical
  by_cases hτ : τ = ∅ <;> simp [sparseAppend, hτ]

theorem sparseAppend_domain_subset {a p τ : V} (hp : domain p ⊆ a) :
    domain (sparseAppend a p τ) ⊆ succ a := by
  classical
  rw [sparseAppend_domain]
  split_ifs
  · exact subset_trans hp (mem_subset_refl a)
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_succ_self x
    · exact mem_succ_iff.mpr (Or.inr (hp x hx))

theorem sparseAppend_restrict {a p τ : V} [IsFunction p] (hp : domain p ⊆ a) :
    (sparseAppend a p τ) ↾ a = p := by
  classical
  by_cases hτ : τ = ∅
  · rw [hτ, sparseAppend_empty]
    exact IsFunction.restrict_eq_self p a hp
  · rw [sparseAppend_nonempty hτ,
      restrict_insert_kpair_eq_restrict_of_not_mem (mem_irrefl a)]
    exact IsFunction.restrict_eq_self p a hp

theorem sparseAppend_value_new {a p τ : V} [IsFunction p] (hp : domain p ⊆ a) :
    (sparseAppend a p τ) ‘ a = τ := by
  classical
  by_cases hτ : τ = ∅
  · rw [hτ, sparseAppend_empty]
    exact value_eq_empty_of_not_mem_domain (fun ha ↦ mem_irrefl a (hp a ha))
  · have := sparseAppend_isFunction (τ := τ) hp
    exact value_eq_of_kpair_mem (by rw [sparseAppend_nonempty hτ]; simp)

theorem sparseAppend_value_old {a p τ x : V} [IsFunction p]
    (hp : domain p ⊆ a) (hx : x ∈ a) : (sparseAppend a p τ) ‘ x = p ‘ x := by
  classical
  have := sparseAppend_isFunction (τ := τ) hp
  by_cases hxp : x ∈ domain (sparseAppend a p τ)
  · rw [← value_restrict hxp hx, sparseAppend_restrict hp]
  · rw [value_eq_empty_of_not_mem_domain hxp]
    symm
    apply value_eq_empty_of_not_mem_domain
    intro hxp'
    apply hxp
    rw [sparseAppend_domain]
    split_ifs
    · exact hxp'
    · exact mem_insert.mpr (Or.inr hxp')

theorem sparseAppend_reconstruct {a q : V} (hq : IsSparseFunctionOn (succ a) q) :
    sparseAppend a (q ↾ a) (q ‘ a) = q := by
  classical
  have := hq.1
  by_cases ha : a ∈ domain q
  · rw [sparseAppend_nonempty (hq.2.2 a ha)]
    apply mem_ext
    intro z
    constructor
    · intro hz
      rcases mem_insert.mp hz with rfl | hz
      · exact kpair_value_mem ha
      · exact restrict_subset q a z hz
    · intro hz
      obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
      rcases mem_succ_iff.mp (hq.2.1 x (mem_domain_of_kpair_mem hz)) with rfl | hx
      · exact mem_insert.mpr (Or.inl (congrArg (fun y : V ↦ ⟨x, y⟩ₖ)
          (value_eq_of_kpair_mem hz).symm))
      · exact mem_insert.mpr (Or.inr (kpair_mem_restrict_iff.mpr ⟨hz, hx⟩))
  · rw [value_eq_empty_of_not_mem_domain ha, sparseAppend_empty]
    apply IsFunction.restrict_eq_self
    intro x hx
    rcases mem_succ_iff.mp (hq.2.1 x hx) with rfl | hx'
    · exact False.elim (ha hx)
    · exact hx'

theorem sparseAppend_injective {a p p' τ τ' : V} [IsFunction p] [IsFunction p']
    (hp : domain p ⊆ a) (hp' : domain p' ⊆ a)
    (he : sparseAppend a p τ = sparseAppend a p' τ') : p = p' ∧ τ = τ' := by
  constructor
  · simpa only [sparseAppend_restrict hp, sparseAppend_restrict hp'] using
      congrArg (fun q : V ↦ q ↾ a) he
  · simpa only [sparseAppend_value_new hp, sparseAppend_value_new hp'] using
      congrArg (fun q : V ↦ q ‘ a) he

theorem sparseAppend_eq_iff {a p p' τ τ' : V} [IsFunction p] [IsFunction p']
    (hp : domain p ⊆ a) (hp' : domain p' ⊆ a) :
    sparseAppend a p τ = sparseAppend a p' τ' ↔ p = p' ∧ τ = τ' := by
  constructor
  · exact sparseAppend_injective hp hp'
  · rintro ⟨rfl, rfl⟩
    rfl

theorem IsSparseFunctionOn.sparseAppend {a p τ : V} (hp : IsSparseFunctionOn a p) :
    IsSparseFunctionOn (succ a) (sparseAppend a p τ) := by
  classical
  have := hp.1
  refine ⟨sparseAppend_isFunction hp.2.1, sparseAppend_domain_subset hp.2.1, ?_⟩
  intro x hx
  by_cases hτ : τ = ∅
  · rw [hτ, sparseAppend_empty] at hx ⊢
    exact hp.2.2 x hx
  · rw [sparseAppend_domain, ite_eq_right hτ] at hx
    rcases mem_insert.mp hx with rfl | hx
    · rwa [sparseAppend_value_new hp.2.1]
    · rw [sparseAppend_value_old hp.2.1 (hp.2.1 x hx)]
      exact hp.2.2 x hx

theorem sparseAppend_mem_hierarchy_limit {κ a p τ : V} [IsOrdinal κ]
    (hκ : ∀ β ∈ κ, succ β ∈ κ) (ha : a ∈ hierarchy κ)
    (hp : p ∈ hierarchy κ) (hτ : τ ∈ hierarchy κ) :
    sparseAppend a p τ ∈ hierarchy κ := by
  classical
  by_cases ht : τ = ∅
  · rwa [ht, sparseAppend_empty]
  · rw [sparseAppend_nonempty ht]
    have hpair := kpair_mem_hierarchy_limit hκ ha hτ
    have hsing : ({⟨a, τ⟩ₖ} : V) ∈ hierarchy κ := by
      simpa using pair_mem_hierarchy_limit hκ hpair hpair
    have hu := sUnion_mem_hierarchy_limit hκ (pair_mem_hierarchy_limit hκ hsing hp)
    rw [pair_eq_doubleton ({⟨a, τ⟩ₖ} : V) p] at hu
    exact hu

end ZFVP
