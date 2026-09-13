import ZFVP.SetTheory.BoundedCodingSupport
import ZFVP.SetTheory.BoundedUnion

/-! Bounded support conditions for internally finite assignment graphs. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sequenceSupportFormula : SetTheorySemisentence 1 :=
  “U. !codingSupportFormula U ∧ ∀ x ∈ U, ∀ y ∈ U, ∃ z ∈ U, !boundedUnionFormula z x y”

theorem sequenceSupportFormula_bounded : IsBoundedSetFormula sequenceSupportFormula :=
  .and (codingSupportFormula_bounded.subst _) (.all (.bvar 0) (.all (.bvar 1)
    (.exs (.bvar 2) (boundedUnionFormula_bounded.subst _))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

class IsSequenceSupport (U : V) : Prop extends IsCodingSupport U where
  union_closed : ∀ x ∈ U, ∀ y ∈ U, x ∪ y ∈ U

theorem isSequenceSupport_iff (U : V) : IsSequenceSupport U ↔
    IsCodingSupport U ∧ ∀ x ∈ U, ∀ y ∈ U, x ∪ y ∈ U := by
  constructor
  · intro h
    exact ⟨h.toIsCodingSupport, h.union_closed⟩
  · rintro ⟨hc, hu⟩
    exact { toIsCodingSupport := hc, union_closed := hu }

instance sequenceSupportFormula_defined : ℒₛₑₜ-predicate[V] IsSequenceSupport via sequenceSupportFormula :=
  ⟨fun v ↦ by simp [sequenceSupportFormula, isSequenceSupport_iff]⟩

instance isSequenceSupport_definable : ℒₛₑₜ-predicate[V] IsSequenceSupport := sequenceSupportFormula_defined.to_definable

instance codingUniverse_isSequenceSupport (X : V) : IsSequenceSupport (codingUniverse X) where
  toIsCodingSupport := inferInstance
  union_closed := fun _ hx _ hy ↦ codingUniverse_union_closed hx hy

theorem sequenceSupport_containing (X : V) : ∃ U : V, IsSequenceSupport U ∧ X ∈ U :=
  ⟨codingUniverse X, inferInstance, self_mem_codingUniverse X⟩

theorem IsSequenceSupport.insert_closed {U a b : V} [hU : IsSequenceSupport U]
    (ha : a ∈ U) (hb : b ∈ U) : insert a b ∈ U :=
  hU.union_closed _ (IsCodingSupport.singleton_mem ha) b hb

theorem finiteSequences_subset_support {U A : V} [IsSequenceSupport U] (hA : A ⊆ U) : finiteSequences A ⊆ U := by
  apply finiteSequence_induction A (fun s : V ↦ s ∈ U) (by definability) IsCodingSupport.empty_mem
  intro n hn s _ x hx hs
  exact IsSequenceSupport.insert_closed
    (IsCodingSupport.kpair_closed _ (IsCodingSupport.natural_mem hn) _ (hA x hx)) hs

theorem function_mem_sequenceSupport {U A n b : V} [IsSequenceSupport U] (hA : A ⊆ U)
    (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n) : b ∈ U :=
  finiteSequences_subset_support hA b ((mem_finiteSequences_iff A b).mpr ⟨n, hn, hb⟩)

end ZFVP
