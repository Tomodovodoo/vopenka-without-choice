import ZFVP.ModelTheory.SchmerlCodedDeadEndExpansion

/-! The distinguished equality symbol has literal equality in the expansion. -/

set_option autoImplicit false

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open ZFVP.Infinitary.Internal

instance deadEndLanguage_eq : deadEndLanguage.Eq := ⟨.inl (.inl Language.Set.Rel.eq)⟩

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem codedDeadEndExpansion_structureEq {D : V} (hD : IsNonempty D) (E A g S G : V) :
    @Structure.Eq deadEndLanguage (CodedDomain (codedDeadEndExpansion D E A g S G))
      (codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
        (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
        (fun _ f ↦ deadEndFunctionSymbol_valid f)) inferInstance := by
  let : Structure deadEndLanguage (CodedDomain (codedDeadEndExpansion D E A g S G)) :=
    codedFoundationStructure (codedDeadEndExpansion_valid hD E A g S G)
      (fun {k} ↦ deadEndFunctionSymbol (V := V) (k := k)) deadEndRelationSymbol
      (fun _ f ↦ deadEndFunctionSymbol_valid f)
  constructor
  intro a b
  change standardTuple ![a.val, b.val] ∈
    (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (0 : V) ↔ a = b
  have h04 : (0 : V) ≠ 4 := natCast_injective.ne (by decide)
  have h05 : (0 : V) ≠ 5 := natCast_injective.ne (by decide)
  have hr := codedDeadEndExpansion_relation D E A g S G
    (Sum.inl (Sum.inl Language.Set.Rel.eq))
  change (structureRelations (codedDeadEndExpansion D E A g S G)) ‘ (0 : V) = _ at hr
  rw [hr]
  simp only [deadEndRelationSymbol, classRelationSymbol, membershipSymbol,
    deadEndRelationInterpretation, h04, h05, ite_false, classRelationInterpretation, ite_true]
  rw [standardTuple_mem_equalityRelation]
  · exact Subtype.val_injective.eq_iff
  · intro i
    fin_cases i
    · simpa using a.property
    · simpa using b.property

end ZFVP.Schmerl
