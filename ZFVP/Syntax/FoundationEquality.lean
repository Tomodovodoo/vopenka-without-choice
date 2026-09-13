import ZFVP.Syntax.FoundationSemantics

/-! The internal diagonal relation and the direct equality-symbol representation. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def equalityRelation (A : V) : V :=
  {s ∈ A ^ (2 : V) ; s ‘ (0 : V) = s ‘ (1 : V)}

theorem mem_equalityRelation_iff (A s : V) :
    s ∈ equalityRelation A ↔ s ∈ A ^ (2 : V) ∧ s ‘ (0 : V) = s ‘ (1 : V) := by
  simp [equalityRelation]

instance equalityRelation_definable : ℒₛₑₜ-function₁[V] equalityRelation := by
  have h : ℒₛₑₜ-relation (fun D A : V ↦ ∀ s,
      s ∈ D ↔ s ∈ A ^ (2 : V) ∧ s ‘ (0 : V) = s ‘ (1 : V)) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = equalityRelation (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_equalityRelation_iff]

theorem equalityRelation_subset (A : V) : equalityRelation A ⊆ A ^ (2 : V) :=
  fun s hs ↦ ((mem_equalityRelation_iff A s).mp hs).1

theorem standardTuple_mem_equalityRelation {A : V} (v : Fin 2 → V) (hv : ∀ i, v i ∈ A) :
    standardTuple v ∈ equalityRelation A ↔ v 0 = v 1 := by
  have hv' : standardTuple v ∈ A ^ (2 : V) := by simpa using standardTuple_mem_function v hv
  rw [mem_equalityRelation_iff, and_iff_right hv']
  simpa using (show (standardTuple v) ‘ (((0 : Fin 2).val : ℕ) : V) =
      (standardTuple v) ‘ (((1 : Fin 2).val : ℕ) : V) ↔ v 0 = v 1 by
    rw [value_standardTuple, value_standardTuple])

theorem atomicHolds_relation_equality {L Γ M E n b r args : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain M ^ n) (hE : E ∈ structureDomain M ^ Γ)
    (ha : args ∈ termSet L Γ n ^ (2 : V)) (hr : r ∈ relationSymbols L)
    (heq : (structureRelations M) ‘ r = equalityRelation (structureDomain M)) :
    AtomicHolds L Γ M E n b (relationToken r) args ↔
      AtomicHolds L Γ M E n b equalityToken args := by
  rw [atomicHolds_relation, and_iff_right hr, heq, mem_equalityRelation_iff,
    and_iff_right (evaluatedArguments_mem_function hM hn hb hE ha), atomicHolds_equality]

variable {Λ : Language} {L M : V}

theorem satisfies_relation_equality {L Γ M E n b r args : V}
    (hM : IsStructureCode L M) (hn : n ∈ (ω : V))
    (hb : b ∈ structureDomain M ^ n) (hE : E ∈ structureDomain M ^ Γ)
    (ha : args ∈ termSet L Γ n ^ (2 : V)) (hr : r ∈ relationSymbols L)
    (harity : (relationArities L) ‘ r = (2 : V))
    (heq : (structureRelations M) ‘ r = equalityRelation (structureDomain M)) :
    (Satisfies L Γ M E n (atomCode (relationToken r) args) b ↔
      Satisfies L Γ M E n (atomCode equalityToken args) b) ∧
    (Satisfies L Γ M E n (negAtomCode (relationToken r) args) b ↔
      Satisfies L Γ M E n (negAtomCode equalityToken args) b) := by
  have hrel : IsAtomicArguments L Γ n (relationToken r) args :=
    Or.inr ⟨r, hr, rfl, harity.symm ▸ ha⟩
  have hequal : IsAtomicArguments L Γ n equalityToken args := Or.inl ⟨rfl, ha⟩
  constructor
  · rw [satisfies_atom hM.language hn hrel hb, satisfies_atom hM.language hn hequal hb]
    exact atomicHolds_relation_equality hM hn hb hE ha hr heq
  · rw [satisfies_negAtom hM.language hn hrel hb, satisfies_negAtom hM.language hn hequal hb]
    exact not_congr (atomicHolds_relation_equality hM hn hb hE ha hr heq)

theorem codedFoundationStructure_equality (hM : IsStructureCode L M)
    (F : ∀ {k}, Λ.Func k → V) (R : ∀ {k}, Λ.Rel k → V)
    (hF : ∀ k (f : Λ.Func k), F f ∈ functionSymbols L ∧
      (functionArities L) ‘ (F f) = (k : V))
    (r : Λ.Rel 2)
    (heq : (structureRelations M) ‘ (R r) = equalityRelation (structureDomain M))
    (v : Fin 2 → CodedDomain M) :
    (codedFoundationStructure hM F R hF).rel r v ↔ v 0 = v 1 := by
  change standardTuple (fun i ↦ (v i).val) ∈ (structureRelations M) ‘ (R r) ↔ _
  rw [heq, standardTuple_mem_equalityRelation _ (fun i ↦ (v i).property)]
  exact Subtype.val_injective.eq_iff

end ZFVP
