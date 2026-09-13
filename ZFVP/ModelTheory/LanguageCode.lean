import ZFVP.SetTheory.FunctionValue
import ZFVP.SetTheory.FiniteSequences

/-! Set-coded first-order languages. Symbol sets are arbitrary internal sets;
no enumeration or well-order of the symbols is part of the definition. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Function symbols, relation symbols, and their arity graphs. Equality is logical. -/
noncomputable def languageCode (F R fa ra : V) : V := ⟨F, ⟨R, ⟨fa, ra⟩ₖ⟩ₖ⟩ₖ

noncomputable def functionSymbols (L : V) : V := kpair.π₁ L
noncomputable def relationSymbols (L : V) : V := kpair.π₁ (kpair.π₂ L)
noncomputable def functionArities (L : V) : V := kpair.π₁ (kpair.π₂ (kpair.π₂ L))
noncomputable def relationArities (L : V) : V := kpair.π₂ (kpair.π₂ (kpair.π₂ L))

@[simp] theorem functionSymbols_code (F R fa ra : V) :
    functionSymbols (languageCode F R fa ra) = F := by simp [functionSymbols, languageCode]
@[simp] theorem relationSymbols_code (F R fa ra : V) :
    relationSymbols (languageCode F R fa ra) = R := by simp [relationSymbols, languageCode]
@[simp] theorem functionArities_code (F R fa ra : V) :
    functionArities (languageCode F R fa ra) = fa := by simp [functionArities, languageCode]
@[simp] theorem relationArities_code (F R fa ra : V) :
    relationArities (languageCode F R fa ra) = ra := by simp [relationArities, languageCode]

theorem languageCode_injective {F R fa ra F' R' fa' ra' : V} :
    languageCode F R fa ra = languageCode F' R' fa' ra' ↔
      F = F' ∧ R = R' ∧ fa = fa' ∧ ra = ra' := by
  simp [languageCode]

def IsLanguageCode (L : V) : Prop :=
  L = languageCode (functionSymbols L) (relationSymbols L) (functionArities L) (relationArities L) ∧
    functionArities L ∈ (ω : V) ^ functionSymbols L ∧
    relationArities L ∈ (ω : V) ^ relationSymbols L

theorem isLanguageCode_iff (F R fa ra : V) :
    IsLanguageCode (languageCode F R fa ra) ↔ fa ∈ (ω : V) ^ F ∧ ra ∈ (ω : V) ^ R := by
  simp [IsLanguageCode]

instance functionSymbols_definable : ℒₛₑₜ-function₁[V] functionSymbols := by
  unfold functionSymbols
  definability
instance relationSymbols_definable : ℒₛₑₜ-function₁[V] relationSymbols := by
  unfold relationSymbols
  definability
instance functionArities_definable : ℒₛₑₜ-function₁[V] functionArities := by
  unfold functionArities
  definability
instance relationArities_definable : ℒₛₑₜ-function₁[V] relationArities := by
  unfold relationArities
  definability
instance languageCode_definable : ℒₛₑₜ-function₄[V] languageCode := by
  unfold languageCode
  definability
instance isLanguageCode_definable : ℒₛₑₜ-predicate[V] IsLanguageCode := by
  unfold IsLanguageCode
  definability

theorem IsLanguageCode.function_arity_natural {L f : V} (hL : IsLanguageCode L)
    (hf : f ∈ functionSymbols L) : (functionArities L) ‘ f ∈ (ω : V) :=
  function_value_mem hL.2.1 hf

theorem IsLanguageCode.relation_arity_natural {L r : V} (hL : IsLanguageCode L)
    (hr : r ∈ relationSymbols L) : (relationArities L) ‘ r ∈ (ω : V) :=
  function_value_mem hL.2.2 hr

end ZFVP
