import ZFVP.ModelTheory.SchmerlCodedNamedLanguageTransport
import ZFVP.ModelTheory.SemanticStandardCodedZFModel
import ZFVP.Syntax.StandardOmegaMembershipSyntax

/-! A countable ground containing the fixed dead-end fragment and an exact
representation of any given countable set-language structure. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

noncomputable def namedDeadEndGroundUniverseFormula {n : ℕ}
    (φ : Infinitary.Formula namedDeadEndLanguage n) : Universe.{0} :=
  universeFormulaCode (fun {k} ↦ namedDeadEndFunctionSymbol (V := Universe.{0}) (k := k))
    namedDeadEndRelationSymbol φ

noncomputable def namedDeadEndGroundUniverseFragment
    (A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)) (hA : A.Countable) : Universe.{0} := by
  let := hA.to_subtype
  exact universeFragment (fun {k} ↦ namedDeadEndFunctionSymbol (V := Universe.{0}) (k := k))
    namedDeadEndRelationSymbol A

variable (M : Type*) [SetStructure M] [Countable M] (c : ℕ → M)
  (A : Set (Σ n, Infinitary.Formula namedDeadEndLanguage n)) (hA : A.Countable)

abbrev NamedDeadEndCodingGround :=
  NamedDeadEndCodingHull (namedDeadEndGroundUniverseFragment A hA)
    (fun {_} ↦ namedDeadEndGroundUniverseFormula) A
    {countableStructureCarrier M, countableStructureRelation M, universeSequence (fun n ↦ countableStructureNode M (c n))}

noncomputable def namedDeadEndCodingGroundMap :
    ZFVP.ElementaryMap (NamedDeadEndCodingGround M c A hA) Universe.{0} :=
  codingHullMap namedDeadEndLanguageCode (namedDeadEndGroundUniverseFragment A hA)
    (fun {k} ↦ namedDeadEndFunctionSymbol (V := Universe.{0}) (k := k)) namedDeadEndRelationSymbol
    (fun {_} ↦ namedDeadEndGroundUniverseFormula) A
    {countableStructureCarrier M, countableStructureRelation M, universeSequence (fun n ↦ countableStructureNode M (c n))}

instance namedDeadEndCodingGround_countable : Countable (NamedDeadEndCodingGround M c A hA) :=
  codingHull_countable _ _ _ _ _ _ _ hA (Set.to_countable _)

theorem namedDeadEndCodingGround_standardOmega : HasStandardOmega (NamedDeadEndCodingGround M c A hA) :=
  codingHull_standardOmega _ _ _ _ _ _ _ universe_standardOmega

theorem namedDeadEndCodingGround_choice : InternalChoice (NamedDeadEndCodingGround M c A hA) :=
  codingHull_choice _ _ _ _ _ _ _ (internalChoice_of_models_ac (V := Universe.{0}))

noncomputable def namedDeadEndCodingGroundFragment : NamedDeadEndCodingGround M c A hA :=
  codingHullFragment _ _ _ _ _ _ _

noncomputable def namedDeadEndCodingGroundFormula {n : ℕ}
    (φ : Infinitary.Formula namedDeadEndLanguage n) : NamedDeadEndCodingGround M c A hA :=
  codingHullFormula _ _ _ _ _ _ _ φ

theorem namedDeadEndCodingGroundFragment_countable :
    IsInternallyCountable (namedDeadEndCodingGroundFragment M c A hA) := by
  apply codingHullFragment_countable
  exact universeFragment_countable _ _ hA

theorem namedDeadEndCodingGround_coding (hclosed : SubformulaClosed A) :
    IsFragmentCoding (namedDeadEndLanguageCode : NamedDeadEndCodingGround M c A hA)
      (namedDeadEndCodingGroundFragment M c A hA)
      (fun {k} ↦ namedDeadEndFunctionSymbol (V := NamedDeadEndCodingGround M c A hA) (k := k))
      namedDeadEndRelationSymbol (fun {_} ↦ namedDeadEndCodingGroundFormula M c A hA) A := by
  apply namedDeadEndFragmentCoding_codingHull
  exact universeFragment_coding namedDeadEndLanguageCode_valid _ _
    (fun _ ↦ namedDeadEndFunctionSymbol_valid) (fun _ ↦ namedDeadEndRelationSymbol_valid) hclosed

noncomputable def namedDeadEndCodingGroundCarrier : NamedDeadEndCodingGround M c A hA :=
  ⟨countableStructureCarrier M, codingHull_seed _ _ _ _ _ _ _ (by simp)⟩

noncomputable def namedDeadEndCodingGroundRelation : NamedDeadEndCodingGround M c A hA :=
  ⟨countableStructureRelation M, codingHull_seed _ _ _ _ _ _ _ (by simp)⟩

noncomputable def namedDeadEndCodingGroundNode (x : M) : NamedDeadEndCodingGround M c A hA :=
  ((@Encodable.encode M (Encodable.ofCountable M) x : ℕ) : NamedDeadEndCodingGround M c A hA)

@[simp] theorem namedDeadEndCodingGroundMap_node (x : M) :
    namedDeadEndCodingGroundMap M c A hA (namedDeadEndCodingGroundNode M c A hA x) =
      countableStructureNode M x :=
  (namedDeadEndCodingGroundMap M c A hA).map_numeral _

@[simp] theorem namedDeadEndCodingGroundMap_carrier :
    namedDeadEndCodingGroundMap M c A hA (namedDeadEndCodingGroundCarrier M c A hA) =
      countableStructureCarrier M := rfl

@[simp] theorem namedDeadEndCodingGroundMap_relation :
    namedDeadEndCodingGroundMap M c A hA (namedDeadEndCodingGroundRelation M c A hA) =
      countableStructureRelation M := rfl

theorem namedDeadEndCodingGroundNode_mem (x : M) :
    namedDeadEndCodingGroundNode M c A hA x ∈ namedDeadEndCodingGroundCarrier M c A hA := by
  apply ((namedDeadEndCodingGroundMap M c A hA).map_mem_iff _ _).mp
  simpa only [namedDeadEndCodingGroundMap_node, namedDeadEndCodingGroundMap_carrier] using
    node_mem_countableStructureCarrier M x

theorem mem_namedDeadEndCodingGroundCarrier (z : NamedDeadEndCodingGround M c A hA) :
    z ∈ namedDeadEndCodingGroundCarrier M c A hA ↔ ∃ x : M, namedDeadEndCodingGroundNode M c A hA x = z := by
  constructor
  · intro hz
    have hh := ((namedDeadEndCodingGroundMap M c A hA).map_mem_iff _ _).mpr hz
    obtain ⟨x, hx⟩ := (mem_countableStructureCarrier M _).mp hh
    refine ⟨x, (namedDeadEndCodingGroundMap M c A hA).injective ?_⟩
    simpa only [namedDeadEndCodingGroundMap_node] using hx
  · rintro ⟨x, rfl⟩
    exact namedDeadEndCodingGroundNode_mem M c A hA x

theorem namedDeadEndCodingGroundNode_injective : Function.Injective (namedDeadEndCodingGroundNode M c A hA) := by
  intro x y hxy
  apply countableStructureNode_injective M
  simpa only [namedDeadEndCodingGroundMap_node] using congrArg (namedDeadEndCodingGroundMap M c A hA) hxy

theorem namedDeadEndCodingGroundCarrier_countable :
    IsInternallyCountable (namedDeadEndCodingGroundCarrier M c A hA) :=
  ((namedDeadEndCodingGroundMap M c A hA).map_internallyCountable_iff _).mp
    (countableStructureCarrier_countable M)

theorem namedDeadEndCodingGroundRelation_subset :
    namedDeadEndCodingGroundRelation M c A hA ⊆
      namedDeadEndCodingGroundCarrier M c A hA ×ˢ namedDeadEndCodingGroundCarrier M c A hA := by
  let j := namedDeadEndCodingGroundMap M c A hA
  have hprod : j (namedDeadEndCodingGroundCarrier M c A hA ×ˢ namedDeadEndCodingGroundCarrier M c A hA) =
      j (namedDeadEndCodingGroundCarrier M c A hA) ×ˢ j (namedDeadEndCodingGroundCarrier M c A hA) :=
    j.map_definedFunction prod.dfn (fun v ↦ v 0 ×ˢ v 1) (fun v ↦ v 0 ×ˢ v 1)
      ![namedDeadEndCodingGroundCarrier M c A hA, namedDeadEndCodingGroundCarrier M c A hA]
  intro z hz
  have hh := countableStructureRelation_subset M (j z) ((j.map_mem_iff _ _).mpr hz)
  apply (j.map_mem_iff _ _).mp
  simpa only [hprod, j, namedDeadEndCodingGroundMap_carrier] using hh

theorem pair_mem_namedDeadEndCodingGroundRelation (x y : M) :
    ⟨namedDeadEndCodingGroundNode M c A hA x, namedDeadEndCodingGroundNode M c A hA y⟩ₖ ∈
      namedDeadEndCodingGroundRelation M c A hA ↔ x ∈ y := by
  rw [← (namedDeadEndCodingGroundMap M c A hA).map_mem_iff]
  simpa only [(namedDeadEndCodingGroundMap M c A hA).map_kpair, namedDeadEndCodingGroundMap_node,
    namedDeadEndCodingGroundMap_relation] using pair_mem_countableStructureRelation M x y

noncomputable def namedDeadEndCodingGroundEquiv :
    M ≃ BinaryRelationDomain (namedDeadEndCodingGroundCarrier M c A hA) (namedDeadEndCodingGroundRelation M c A hA) :=
  Equiv.ofBijective (fun x ↦ ⟨namedDeadEndCodingGroundNode M c A hA x, namedDeadEndCodingGroundNode_mem M c A hA x⟩) (by
    constructor
    · intro x y hxy
      exact namedDeadEndCodingGroundNode_injective M c A hA (congrArg Subtype.val hxy)
    · intro z
      obtain ⟨x, hx⟩ := (mem_namedDeadEndCodingGroundCarrier M c A hA z.val).mp z.property
      exact ⟨x, Subtype.ext hx⟩)

/-- The entire enumeration table belongs to the same countable coding ground. -/
noncomputable def namedDeadEndCodingGroundNames : NamedDeadEndCodingGround M c A hA :=
  ⟨universeSequence (fun n ↦ countableStructureNode M (c n)),
    codingHull_seed _ _ _ _ _ _ _ (by simp)⟩

@[simp] theorem namedDeadEndCodingGroundMap_names :
    namedDeadEndCodingGroundMap M c A hA (namedDeadEndCodingGroundNames M c A hA) =
      universeSequence (fun n ↦ countableStructureNode M (c n)) := rfl

theorem namedDeadEndCodingGroundNames_value (n : ℕ) :
    (namedDeadEndCodingGroundNames M c A hA) ‘ (n : NamedDeadEndCodingGround M c A hA) =
      namedDeadEndCodingGroundNode M c A hA (c n) := by
  apply (namedDeadEndCodingGroundMap M c A hA).injective
  rw [(namedDeadEndCodingGroundMap M c A hA).map_value,
    (namedDeadEndCodingGroundMap M c A hA).map_numeral, namedDeadEndCodingGroundMap_node]
  rw [namedDeadEndCodingGroundMap_names]
  exact value_universeSequence (fun k ↦ countableStructureNode M (c k)) n

theorem namedDeadEndCodingGroundNames_function :
    namedDeadEndCodingGroundNames M c A hA ∈ namedDeadEndCodingGroundCarrier M c A hA ^
      (ω : NamedDeadEndCodingGround M c A hA) := by
  let j := namedDeadEndCodingGroundMap M c A hA
  have hf : j (namedDeadEndCodingGroundCarrier M c A hA ^
      (ω : NamedDeadEndCodingGround M c A hA)) = countableStructureCarrier M ^ (ω : Universe.{0}) := by
    have hh := j.map_definedFunction function.dfn (fun v ↦ v 0 ^ v 1) (fun v ↦ v 0 ^ v 1)
      ![namedDeadEndCodingGroundCarrier M c A hA, ω]
    simpa only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      j.map_omega, j, namedDeadEndCodingGroundMap_carrier] using hh
  apply (j.map_mem_iff _ _).mp
  rw [hf]
  exact universeGraph_mem_function _ (fun _ ↦ node_mem_countableStructureCarrier M _)

variable [Nonempty M]

theorem namedDeadEndCodingGroundCarrier_nonempty : IsNonempty (namedDeadEndCodingGroundCarrier M c A hA) :=
  ⟨⟨namedDeadEndCodingGroundNode M c A hA (Classical.arbitrary M), namedDeadEndCodingGroundNode_mem M c A hA _⟩⟩

noncomputable def namedDeadEndCodingGroundRepresentation :
    BinaryRelationRepresentation (V := NamedDeadEndCodingGround M c A hA) M where
  carrier := namedDeadEndCodingGroundCarrier M c A hA
  relation := namedDeadEndCodingGroundRelation M c A hA
  carrier_nonempty := namedDeadEndCodingGroundCarrier_nonempty M c A hA
  relation_subset := namedDeadEndCodingGroundRelation_subset M c A hA
  equiv := namedDeadEndCodingGroundEquiv M c A hA
  mem_iff := fun x y ↦ (pair_mem_namedDeadEndCodingGroundRelation M c A hA x y).symm

theorem namedDeadEndCodingGroundRepresentation_countable :
    IsInternallyCountable (namedDeadEndCodingGroundRepresentation M c A hA).carrier :=
  namedDeadEndCodingGroundCarrier_countable M c A hA

theorem namedDeadEndCodingGroundRepresentation_isCodedZFModel [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    IsCodedZFModel (namedDeadEndCodingGroundRepresentation M c A hA).code :=
  (namedDeadEndCodingGroundRepresentation M c A hA).isCodedZFModel_of_semanticStandardSyntax
    (semanticStandardMembershipSyntax_of_standardOmega (namedDeadEndCodingGround_standardOmega M c A hA))

end ZFVP.Schmerl




