import ZFVP.Syntax.CanonicalEqualityAxioms
import ZFVP.ModelTheory.CodedStructureSequentSoundness
import ZFVP.ModelTheory.InternalCodedProofSupport

/-! The internally finite open sequent checker with explicit canonical
equality axioms. These definitions strengthen consistency of raw syntax. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isEqualityCodedSequentProofFormula : SetTheorySemisentence 4 :=
  f“T p n Γ. !isOpenCodedSequentProofFormula (!union.dfn T (!canonicalEqualityOpenCodesFormula)) p n Γ”

def equalityCodedSequentConsistentFormula : SetTheorySemisentence 1 :=
  noRefutationFormula isEqualityCodedSequentProofFormula

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsEqualityCodedSequentProof (T p n Γ : V) : Prop :=
  IsOpenCodedSequentProof (T ∪ canonicalEqualityOpenCodes) p n Γ

def EqualityCodedSequentConsistent (T : V) : Prop :=
  OpenCodedSequentConsistent (T ∪ canonicalEqualityOpenCodes)

instance isEqualityCodedSequentProofFormula_defined :
    ℒₛₑₜ-relation₄[V] IsEqualityCodedSequentProof via isEqualityCodedSequentProofFormula :=
  ⟨fun v ↦ by simp [isEqualityCodedSequentProofFormula, IsEqualityCodedSequentProof]⟩

instance equalityCodedSequentConsistentFormula_defined :
    ℒₛₑₜ-predicate[V] EqualityCodedSequentConsistent via equalityCodedSequentConsistentFormula :=
  noRefutationFormula_defined IsEqualityCodedSequentProof isEqualityCodedSequentProofFormula

instance isEqualityCodedSequentProof_definable : ℒₛₑₜ-relation₄[V] IsEqualityCodedSequentProof :=
  isEqualityCodedSequentProofFormula_defined.to_definable

instance equalityCodedSequentConsistent_definable : ℒₛₑₜ-predicate[V] EqualityCodedSequentConsistent :=
  equalityCodedSequentConsistentFormula_defined.to_definable

theorem SatisfiesCodedOpenTheory.union {L M T U : V}
    (hT : SatisfiesCodedOpenTheory L M T) (hU : SatisfiesCodedOpenTheory L M U) :
    SatisfiesCodedOpenTheory L M (T ∪ U) := by
  refine ⟨hT.1, fun n φ hφ ↦ ?_⟩
  rcases mem_union_iff.mp hφ with hφ | hφ
  · exact hT.2 n φ hφ
  · exact hU.2 n φ hφ

theorem binaryRelationStructureCode_satisfies_canonicalEquality {D E : V} (hD : IsNonempty D) :
    SatisfiesCodedOpenTheory membershipLanguageCode (binaryRelationStructureCode D E)
      canonicalEqualityOpenCodes := by
  refine ⟨binaryRelationStructureCode_valid hD E, fun n φ hφ ↦ ?_⟩
  have hc := (mem_formulaSet_iff _ _ _ _).mpr (canonicalEqualityOpenCodes_valid _ hφ)
  refine ⟨hc, fun b hb ↦ ?_⟩
  have he : (n = 0 ∧ φ = encodeMembershipFormula equalityBasisSentence) ∨
      (n = 2 ∧ φ = rawEqualityBridgeCode) ∨ (n = 0 ∧ φ = encodeMembershipFormula nonemptyDomainSentence) := by
    simpa [canonicalEqualityOpenCodes] using hφ
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hb0 : b = (∅ : V) := function_eq_of_values hb
      (by simp [mem_function_iff, zero_def]) (fun i hi ↦ False.elim (not_mem_empty hi))
    subst b
    exact (satisfies_encodeBinaryRelationFormula hD equalityBasisSentence
      (![] : Fin 0 → BinaryRelationDomain D E)).mpr eval_equalityBasisSentence
  · exact rawEqualityBridgeCode_satisfies (by simpa only [binaryRelationStructureCode_domain] using hb)
  · have hb0 : b = (∅ : V) := function_eq_of_values hb
      (by simp [mem_function_iff, zero_def]) (fun i hi ↦ False.elim (not_mem_empty hi))
    subst b
    apply (satisfies_encodeBinaryRelationFormula hD nonemptyDomainSentence
      (![] : Fin 0 → BinaryRelationDomain D E)).mpr
    obtain ⟨x, hx⟩ := hD.nonempty
    exact ⟨(⟨x, hx⟩ : BinaryRelationDomain D E), True.intro⟩

theorem SatisfiesCodedOpenTheory.equalityCodedSequentConsistent {D E T : V} (hD : IsNonempty D)
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode (binaryRelationStructureCode D E) T) :
    EqualityCodedSequentConsistent T :=
  (hT.union (binaryRelationStructureCode_satisfies_canonicalEquality hD)).openCodedSequentConsistent

theorem IsEqualityCodedSequentProof.coded_structure_sound {D E T p n Γ : V}
    (hp : IsEqualityCodedSequentProof T p n Γ) (hD : IsNonempty D)
    (hT : SatisfiesCodedOpenTheory membershipLanguageCode (binaryRelationStructureCode D E) T) :
    CodedStructureSequentTrue (binaryRelationStructureCode D E) n Γ :=
  IsOpenCodedSequentProof.coded_structure_sound hp
    (hT.union (binaryRelationStructureCode_satisfies_canonicalEquality hD))

theorem IsEqualityCodedSequentProof.theory_mono {T U p n Γ : V}
    (hp : IsEqualityCodedSequentProof T p n Γ) (hTU : T ⊆ U) : IsEqualityCodedSequentProof U p n Γ := by
  apply IsOpenCodedSequentProof.theory_mono hp
  intro x hx
  exact (mem_union_iff.mp hx).elim (fun h ↦ mem_union_iff.mpr (Or.inl (hTU _ h)))
    (fun h ↦ mem_union_iff.mpr (Or.inr h))

theorem EqualityCodedSequentConsistent.subtheory {T U : V}
    (hU : EqualityCodedSequentConsistent U) (hTU : T ⊆ U) : EqualityCodedSequentConsistent T := by
  rintro ⟨p, hp⟩
  exact hU ⟨p, IsEqualityCodedSequentProof.theory_mono hp hTU⟩

theorem EqualityCodedSequentConsistent.openConsistent {T : V}
    (hT : EqualityCodedSequentConsistent T) : OpenCodedSequentConsistent T :=
  OpenCodedSequentConsistent.subtheory hT (fun _ hx ↦ mem_union_iff.mpr (Or.inl hx))

theorem IsEqualityCodedSequentProof.finite_subtheory {T p n Γ : V}
    (hp : IsEqualityCodedSequentProof T p n Γ) :
    ∃ A, A ⊆ T ∧ IsInternallyFinite A ∧ IsEqualityCodedSequentProof A p n Γ := by
  obtain ⟨A, hAT, hfin, hpA⟩ := IsOpenCodedSequentProof.finite_subtheory hp
  refine ⟨A ∩ T, fun _ hx ↦ (mem_inter_iff.mp hx).2,
    internallyFinite_subset hfin (fun _ hx ↦ (mem_inter_iff.mp hx).1), ?_⟩
  apply IsOpenCodedSequentProof.theory_mono hpA
  intro x hx
  rcases mem_union_iff.mp (hAT x hx) with hT | hE
  · exact mem_union_iff.mpr (Or.inl (mem_inter_iff.mpr ⟨hx, hT⟩))
  · exact mem_union_iff.mpr (Or.inr hE)

theorem equalityCodedSequentConsistent_iff_finite (T : V) : EqualityCodedSequentConsistent T ↔
    ∀ A, A ⊆ T → IsInternallyFinite A → EqualityCodedSequentConsistent A := by
  constructor
  · intro hT A hA _
    exact hT.subtheory hA
  · intro hall
    rintro ⟨p, hp⟩
    obtain ⟨A, hAT, hfin, hpA⟩ := IsEqualityCodedSequentProof.finite_subtheory hp
    exact hall A hAT hfin ⟨p, hpA⟩

namespace ElementaryMap

variable {W : Type*} [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_canonicalEqualityOpenCodes (j : ElementaryMap V W) :
    j canonicalEqualityOpenCodes = canonicalEqualityOpenCodes :=
  (j.map_defined canonicalEqualityOpenCodesFormula
    (fun v ↦ v 0 = (canonicalEqualityOpenCodes : V))
    (fun v ↦ v 0 = (canonicalEqualityOpenCodes : W)) ![canonicalEqualityOpenCodes]).mp rfl

theorem map_equalityCodedSequentProof_iff (j : ElementaryMap V W) (T p n Γ : V) :
    IsEqualityCodedSequentProof (j T) (j p) (j n) (j Γ) ↔ IsEqualityCodedSequentProof T p n Γ :=
  (j.map_defined isEqualityCodedSequentProofFormula
    (fun v ↦ IsEqualityCodedSequentProof (v 0) (v 1) (v 2) (v 3))
    (fun v ↦ IsEqualityCodedSequentProof (v 0) (v 1) (v 2) (v 3)) ![T, p, n, Γ]).symm

theorem map_equalityCodedSequentConsistent_iff (j : ElementaryMap V W) (T : V) :
    EqualityCodedSequentConsistent (j T) ↔ EqualityCodedSequentConsistent T :=
  (j.map_defined equalityCodedSequentConsistentFormula
    (fun v ↦ EqualityCodedSequentConsistent (v 0))
    (fun v ↦ EqualityCodedSequentConsistent (v 0)) ![T]).symm

end ElementaryMap

end ZFVP
