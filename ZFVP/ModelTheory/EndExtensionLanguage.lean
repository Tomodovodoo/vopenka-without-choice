import ZFVP.SetTheory.EndExtensionRelations
import ZFVP.ModelTheory.StructureCode

/-! Language and structure code components under membership end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension

variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_languageCode (j : MembershipEndExtension V W) (F R fa ra : V) :
    j (languageCode F R fa ra) = languageCode (j F) (j R) (j fa) (j ra) := by
  simp only [languageCode, j.map_kpair]

theorem map_functionSymbols (j : MembershipEndExtension V W) (L : V) :
    j (functionSymbols L) = functionSymbols (j L) := j.map_first L

theorem map_relationSymbols (j : MembershipEndExtension V W) (L : V) :
    j (relationSymbols L) = relationSymbols (j L) := by
  simp only [relationSymbols, j.map_first, j.map_second]

theorem map_functionArities (j : MembershipEndExtension V W) (L : V) :
    j (functionArities L) = functionArities (j L) := by
  simp only [functionArities, j.map_first, j.map_second]

theorem map_relationArities (j : MembershipEndExtension V W) (L : V) :
    j (relationArities L) = relationArities (j L) := by
  simp only [relationArities, j.map_second]

theorem languageCode_iff (j : MembershipEndExtension V W) (L : V) :
    IsLanguageCode (j L) ↔ IsLanguageCode L := by
  unfold IsLanguageCode
  rw [← j.map_functionSymbols, ← j.map_relationSymbols, ← j.map_functionArities,
    ← j.map_relationArities, ← j.map_languageCode, j.injective.eq_iff, ← j.map_omega,
    j.function_iff, j.function_iff]

theorem map_structureCode (j : MembershipEndExtension V W) (A FI RI : V) :
    j (structureCode A FI RI) = structureCode (j A) (j FI) (j RI) := by
  simp only [structureCode, j.map_kpair]

theorem map_structureDomain (j : MembershipEndExtension V W) (M : V) :
    j (structureDomain M) = structureDomain (j M) := j.map_first M

theorem map_structureFunctions (j : MembershipEndExtension V W) (M : V) :
    j (structureFunctions M) = structureFunctions (j M) := by
  simp only [structureFunctions, j.map_first, j.map_second]

theorem map_structureRelations (j : MembershipEndExtension V W) (M : V) :
    j (structureRelations M) = structureRelations (j M) := by
  simp only [structureRelations, j.map_second]

theorem map_functionArity (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L)
    {f : V} (hf : f ∈ functionSymbols L) :
    j ((functionArities L) ‘ f) = (functionArities (j L)) ‘ (j f) := by
  let := IsFunction.of_mem hL.2.1
  rw [j.map_value _ _ (by simpa only [domain_eq_of_mem_function hL.2.1] using hf), j.map_functionArities]

theorem map_relationArity (j : MembershipEndExtension V W) {L : V} (hL : IsLanguageCode L)
    {r : V} (hr : r ∈ relationSymbols L) :
    j ((relationArities L) ‘ r) = (relationArities (j L)) ‘ (j r) := by
  let := IsFunction.of_mem hL.2.2
  rw [j.map_value _ _ (by simpa only [domain_eq_of_mem_function hL.2.2] using hr), j.map_relationArities]

theorem structureCode_iff (j : MembershipEndExtension V W) (L M : V) :
    IsStructureCode (j L) (j M) ↔ IsStructureCode L M := by
  unfold IsStructureCode
  rw [j.languageCode_iff]
  apply and_congr_right
  intro hL
  rw [← j.map_structureDomain, ← j.map_structureFunctions, ← j.map_structureRelations,
    ← j.map_structureCode, j.injective.eq_iff, j.nonempty_iff,
    ← j.map_functionSymbols, ← j.map_relationSymbols]
  have hf := j.function_on_iff (structureFunctions M) (functionSymbols L)
  have hr := j.function_on_iff (structureRelations M) (relationSymbols L)
  have hfunc :
      (∀ f ∈ j (functionSymbols L),
        (j (structureFunctions M)) ‘ f ∈ j (structureDomain M) ^
          (j (structureDomain M) ^ ((functionArities (j L)) ‘ f))) ↔
      (∀ f ∈ functionSymbols L,
        (structureFunctions M) ‘ f ∈ structureDomain M ^
          (structureDomain M ^ ((functionArities L) ‘ f))) := by
    rw [j.forall_mem_iff]
    apply forall_congr'
    intro f
    apply forall_congr'
    intro hmem
    rw [← j.map_value_total, ← j.map_functionArity hL hmem,
      ← j.map_finiteFunctionSet _ (hL.function_arity_natural hmem), j.function_iff]
  have hrel :
      (∀ r ∈ j (relationSymbols L),
        (j (structureRelations M)) ‘ r ⊆ j (structureDomain M) ^ ((relationArities (j L)) ‘ r)) ↔
      (∀ r ∈ relationSymbols L,
        (structureRelations M) ‘ r ⊆ structureDomain M ^ ((relationArities L) ‘ r)) := by
    rw [j.forall_mem_iff]
    apply forall_congr'
    intro r
    apply forall_congr'
    intro hmem
    rw [← j.map_value_total, ← j.map_relationArity hL hmem,
      ← j.map_finiteFunctionSet _ (hL.relation_arity_natural hmem), j.subset_iff]
  tauto

end MembershipEndExtension
end ZFVP
