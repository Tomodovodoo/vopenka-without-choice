import ZFVP.ModelTheory.InternalNamedQueryContext

/-! Equality with one fixed name as a unary named query. -/

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def namedEqualityQuery (l : V) : V :=
  ⟨⟨(1 : V), standardEqualityCode⟩ₖ, standardTuple ![l]⟩ₖ

theorem namedEqualityQuery_valid {l : V} (hl : l ∈ (ω : V)) :
    namedEqualityQuery l ∈ (namedUnaryDefinitionQueries : V) := by
  apply pair_mem_namedUnaryDefinitionQueries.mpr
  refine ⟨by simp, ?_, standardTuple_mem_function _ (by simp [hl])⟩
  exact standardEqualityCode_mem membershipLanguageCode_valid ∅

@[simp] theorem namedEqualityQuery_instance (l r : V) :
    namedUnaryQueryInstance (namedEqualityQuery l) r = namedEqualityEntry r l := by
  simp only [namedUnaryQueryInstance, namedEqualityQuery, namedEqualityEntry, standardTuple,
    Schmerl.definitionParameterCount_pair, Schmerl.definitionFormula_pair, Schmerl.definitionTuple_pair,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  rfl

theorem namedEqualityQuery_holds {M f l r : V} (hM : IsStructureCode membershipLanguageCode M)
    (hf : f ∈ structureDomain M ^ (ω : V)) (hl : l ∈ (ω : V)) (hr : r ∈ (ω : V)) :
    NamedHolds membershipLanguageCode M f (namedUnaryQueryInstance (namedEqualityQuery l) r) ↔
      NamedHolds membershipLanguageCode M f (namedEqualityEntry l r) := by
  rw [namedEqualityQuery_instance, namedEqualityEntry_holds hM hf hr hl,
    namedEqualityEntry_holds hM hf hl hr]
  exact eq_comm

end ZFVP
