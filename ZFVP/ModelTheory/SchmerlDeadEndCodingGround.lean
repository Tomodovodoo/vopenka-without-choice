import ZFVP.ModelTheory.SchmerlCodedDeadEndLanguageTransport
import ZFVP.ModelTheory.SemanticStandardCodedZFModel
import ZFVP.Syntax.StandardOmegaMembershipSyntax

/-! A countable ground containing the fixed dead-end fragment and an exact
representation of any given countable set-language structure. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

noncomputable def deadEndGroundUniverseFormula {n : ℕ}
    (φ : Infinitary.Formula deadEndLanguage n) : Universe.{0} :=
  universeFormulaCode (fun {k} ↦ deadEndFunctionSymbol (V := Universe.{0}) (k := k))
    deadEndRelationSymbol φ

noncomputable def deadEndGroundUniverseFragment
    (A : Set (Σ n, Infinitary.Formula deadEndLanguage n)) (hA : A.Countable) : Universe.{0} := by
  let := hA.to_subtype
  exact universeFragment (fun {k} ↦ deadEndFunctionSymbol (V := Universe.{0}) (k := k))
    deadEndRelationSymbol A

variable (M : Type*) [SetStructure M] [Countable M]
  (A : Set (Σ n, Infinitary.Formula deadEndLanguage n)) (hA : A.Countable)

abbrev DeadEndCodingGround :=
  DeadEndCodingHull (deadEndGroundUniverseFragment A hA)
    (fun {_} ↦ deadEndGroundUniverseFormula) A
    {countableStructureCarrier M, countableStructureRelation M}

noncomputable def deadEndCodingGroundMap :
    ZFVP.ElementaryMap (DeadEndCodingGround M A hA) Universe.{0} :=
  codingHullMap deadEndLanguageCode (deadEndGroundUniverseFragment A hA)
    (fun {k} ↦ deadEndFunctionSymbol (V := Universe.{0}) (k := k)) deadEndRelationSymbol
    (fun {_} ↦ deadEndGroundUniverseFormula) A
    {countableStructureCarrier M, countableStructureRelation M}

instance deadEndCodingGround_countable : Countable (DeadEndCodingGround M A hA) :=
  codingHull_countable _ _ _ _ _ _ _ hA (Set.to_countable _)

theorem deadEndCodingGround_standardOmega : HasStandardOmega (DeadEndCodingGround M A hA) :=
  codingHull_standardOmega _ _ _ _ _ _ _ universe_standardOmega

theorem deadEndCodingGround_choice : InternalChoice (DeadEndCodingGround M A hA) :=
  codingHull_choice _ _ _ _ _ _ _ (internalChoice_of_models_ac (V := Universe.{0}))

noncomputable def deadEndCodingGroundFragment : DeadEndCodingGround M A hA :=
  codingHullFragment _ _ _ _ _ _ _

noncomputable def deadEndCodingGroundFormula {n : ℕ}
    (φ : Infinitary.Formula deadEndLanguage n) : DeadEndCodingGround M A hA :=
  codingHullFormula _ _ _ _ _ _ _ φ

theorem deadEndCodingGroundFragment_countable :
    IsInternallyCountable (deadEndCodingGroundFragment M A hA) := by
  apply codingHullFragment_countable
  exact universeFragment_countable _ _ hA

theorem deadEndCodingGround_coding (hclosed : SubformulaClosed A) :
    IsFragmentCoding (deadEndLanguageCode : DeadEndCodingGround M A hA)
      (deadEndCodingGroundFragment M A hA)
      (fun {k} ↦ deadEndFunctionSymbol (V := DeadEndCodingGround M A hA) (k := k))
      deadEndRelationSymbol (fun {_} ↦ deadEndCodingGroundFormula M A hA) A := by
  apply deadEndFragmentCoding_codingHull
  exact universeFragment_coding deadEndLanguageCode_valid _ _
    (fun _ ↦ deadEndFunctionSymbol_valid) (fun _ ↦ deadEndRelationSymbol_valid) hclosed

noncomputable def deadEndCodingGroundCarrier : DeadEndCodingGround M A hA :=
  ⟨countableStructureCarrier M, codingHull_seed _ _ _ _ _ _ _ (by simp)⟩

noncomputable def deadEndCodingGroundRelation : DeadEndCodingGround M A hA :=
  ⟨countableStructureRelation M, codingHull_seed _ _ _ _ _ _ _ (by simp)⟩

noncomputable def deadEndCodingGroundNode (x : M) : DeadEndCodingGround M A hA :=
  ((@Encodable.encode M (Encodable.ofCountable M) x : ℕ) : DeadEndCodingGround M A hA)

@[simp] theorem deadEndCodingGroundMap_node (x : M) :
    deadEndCodingGroundMap M A hA (deadEndCodingGroundNode M A hA x) =
      countableStructureNode M x :=
  (deadEndCodingGroundMap M A hA).map_numeral _

@[simp] theorem deadEndCodingGroundMap_carrier :
    deadEndCodingGroundMap M A hA (deadEndCodingGroundCarrier M A hA) =
      countableStructureCarrier M := rfl

@[simp] theorem deadEndCodingGroundMap_relation :
    deadEndCodingGroundMap M A hA (deadEndCodingGroundRelation M A hA) =
      countableStructureRelation M := rfl

theorem deadEndCodingGroundNode_mem (x : M) :
    deadEndCodingGroundNode M A hA x ∈ deadEndCodingGroundCarrier M A hA := by
  apply ((deadEndCodingGroundMap M A hA).map_mem_iff _ _).mp
  simpa only [deadEndCodingGroundMap_node, deadEndCodingGroundMap_carrier] using
    node_mem_countableStructureCarrier M x

theorem mem_deadEndCodingGroundCarrier (z : DeadEndCodingGround M A hA) :
    z ∈ deadEndCodingGroundCarrier M A hA ↔ ∃ x : M, deadEndCodingGroundNode M A hA x = z := by
  constructor
  · intro hz
    have hh := ((deadEndCodingGroundMap M A hA).map_mem_iff _ _).mpr hz
    obtain ⟨x, hx⟩ := (mem_countableStructureCarrier M _).mp hh
    refine ⟨x, (deadEndCodingGroundMap M A hA).injective ?_⟩
    simpa only [deadEndCodingGroundMap_node] using hx
  · rintro ⟨x, rfl⟩
    exact deadEndCodingGroundNode_mem M A hA x

theorem deadEndCodingGroundNode_injective : Function.Injective (deadEndCodingGroundNode M A hA) := by
  intro x y hxy
  apply countableStructureNode_injective M
  simpa only [deadEndCodingGroundMap_node] using congrArg (deadEndCodingGroundMap M A hA) hxy

theorem deadEndCodingGroundCarrier_countable :
    IsInternallyCountable (deadEndCodingGroundCarrier M A hA) :=
  ((deadEndCodingGroundMap M A hA).map_internallyCountable_iff _).mp
    (countableStructureCarrier_countable M)

theorem deadEndCodingGroundRelation_subset :
    deadEndCodingGroundRelation M A hA ⊆
      deadEndCodingGroundCarrier M A hA ×ˢ deadEndCodingGroundCarrier M A hA := by
  let j := deadEndCodingGroundMap M A hA
  have hprod : j (deadEndCodingGroundCarrier M A hA ×ˢ deadEndCodingGroundCarrier M A hA) =
      j (deadEndCodingGroundCarrier M A hA) ×ˢ j (deadEndCodingGroundCarrier M A hA) :=
    j.map_definedFunction prod.dfn (fun v ↦ v 0 ×ˢ v 1) (fun v ↦ v 0 ×ˢ v 1)
      ![deadEndCodingGroundCarrier M A hA, deadEndCodingGroundCarrier M A hA]
  intro z hz
  have hh := countableStructureRelation_subset M (j z) ((j.map_mem_iff _ _).mpr hz)
  apply (j.map_mem_iff _ _).mp
  simpa only [hprod, j, deadEndCodingGroundMap_carrier] using hh

theorem pair_mem_deadEndCodingGroundRelation (x y : M) :
    ⟨deadEndCodingGroundNode M A hA x, deadEndCodingGroundNode M A hA y⟩ₖ ∈
      deadEndCodingGroundRelation M A hA ↔ x ∈ y := by
  rw [← (deadEndCodingGroundMap M A hA).map_mem_iff]
  simpa only [(deadEndCodingGroundMap M A hA).map_kpair, deadEndCodingGroundMap_node,
    deadEndCodingGroundMap_relation] using pair_mem_countableStructureRelation M x y

noncomputable def deadEndCodingGroundEquiv :
    M ≃ BinaryRelationDomain (deadEndCodingGroundCarrier M A hA) (deadEndCodingGroundRelation M A hA) :=
  Equiv.ofBijective (fun x ↦ ⟨deadEndCodingGroundNode M A hA x, deadEndCodingGroundNode_mem M A hA x⟩) (by
    constructor
    · intro x y hxy
      exact deadEndCodingGroundNode_injective M A hA (congrArg Subtype.val hxy)
    · intro z
      obtain ⟨x, hx⟩ := (mem_deadEndCodingGroundCarrier M A hA z.val).mp z.property
      exact ⟨x, Subtype.ext hx⟩)

variable [Nonempty M]

theorem deadEndCodingGroundCarrier_nonempty : IsNonempty (deadEndCodingGroundCarrier M A hA) :=
  ⟨⟨deadEndCodingGroundNode M A hA (Classical.arbitrary M), deadEndCodingGroundNode_mem M A hA _⟩⟩

noncomputable def deadEndCodingGroundRepresentation :
    BinaryRelationRepresentation (V := DeadEndCodingGround M A hA) M where
  carrier := deadEndCodingGroundCarrier M A hA
  relation := deadEndCodingGroundRelation M A hA
  carrier_nonempty := deadEndCodingGroundCarrier_nonempty M A hA
  relation_subset := deadEndCodingGroundRelation_subset M A hA
  equiv := deadEndCodingGroundEquiv M A hA
  mem_iff := fun x y ↦ (pair_mem_deadEndCodingGroundRelation M A hA x y).symm

theorem deadEndCodingGroundRepresentation_countable :
    IsInternallyCountable (deadEndCodingGroundRepresentation M A hA).carrier :=
  deadEndCodingGroundCarrier_countable M A hA

theorem deadEndCodingGroundRepresentation_isCodedZFModel [M↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    IsCodedZFModel (deadEndCodingGroundRepresentation M A hA).code :=
  (deadEndCodingGroundRepresentation M A hA).isCodedZFModel_of_semanticStandardSyntax
    (semanticStandardMembershipSyntax_of_standardOmega (deadEndCodingGround_standardOmega M A hA))

end ZFVP.Schmerl
