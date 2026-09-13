import ZFVP.SetTheory.BaireCore

/-! The manuscript's Baire-space convention, interpreted inside arbitrary ZF models.
The natural numbers, function graphs, trees and countable covers are all internal.
-/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def baireSpaceFormula : SetTheorySemisentence 1 :=
  f“B. B = !function.dfn (!isω) (!isω)”

def naturalSequencesFormula : SetTheorySemisentence 1 :=
  f“S. S = !finiteSequencesFormula (!isω)”

def baireTreeBodyFormula : SetTheorySemisentence 2 :=
  f“B T. ∀ x, x ∈ B ↔ x ∈ !baireSpaceFormula ∧ ∀ n ∈ !isω, !restrict.dfn x n ∈ T”

def baireOpenFromFormula : SetTheorySemisentence 2 :=
  f“U S. ∀ x, x ∈ U ↔ x ∈ !baireSpaceFormula ∧ ∃ s ∈ S, !restrict.dfn x (!domain.dfn s) = s”

def isBaireTreeFormula : SetTheorySemisentence 1 :=
  f“T. T ⊆ !naturalSequencesFormula ∧ ∀ s ∈ T, ∀ n ∈ !domain.dfn s, !restrict.dfn s n ∈ T”

def isPerfectBaireTreeFormula : SetTheorySemisentence 1 :=
  f“T. !isBaireTreeFormula T ∧ !isEmpty ∈ T ∧
    ∀ s ∈ T, ∃ t ∈ T, ∃ u ∈ T, s ⊆ t ∧ s ⊆ u ∧ !incompatibleFormula t u”

def bairePerfectSetPropertyFormula : SetTheorySemisentence 1 :=
  f“A. !CardLE.dfn A (!isω) ∨ ∃ T, !isPerfectBaireTreeFormula T ∧ !baireTreeBodyFormula T ⊆ A”

def isNowhereDenseBaireTreeFormula : SetTheorySemisentence 1 :=
  f“T. !isBaireTreeFormula T ∧
    ∀ s ∈ !naturalSequencesFormula, ∃ t ∈ !naturalSequencesFormula, s ⊆ t ∧ t ∉ T”

def isBaireMeagreFormula : SetTheorySemisentence 1 :=
  f“A. ∃ f ∈ !function.dfn (!power.dfn (!naturalSequencesFormula)) (!isω),
    (∀ n ∈ !isω, !isNowhereDenseBaireTreeFormula (!value.dfn f n)) ∧
    ∀ x ∈ A, ∃ n ∈ !isω, x ∈ !baireTreeBodyFormula (!value.dfn f n)”

def isBaireOpenFormula : SetTheorySemisentence 1 :=
  f“U. ∃ S, S ⊆ !naturalSequencesFormula ∧ U = !baireOpenFromFormula S”

def baireSpacePropertyFormula : SetTheorySemisentence 1 :=
  f“A. ∃ U, !isBaireOpenFormula U ∧ !isBaireMeagreFormula (!union.dfn (!sdiff.dfn A U) (!sdiff.dfn U A))”

def bairePerfectSetPropertySentence : SetTheorySentence :=
  f“∀ A, A ⊆ !baireSpaceFormula → !bairePerfectSetPropertyFormula A”

def baireSpacePropertySentence : SetTheorySentence :=
  f“∀ A, A ⊆ !baireSpaceFormula → !baireSpacePropertyFormula A”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def baireSpace (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := (ω : V) ^ (ω : V)

noncomputable def naturalSequences (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := finiteSequences (ω : V)

instance baireSpaceFormula_defined : ℒₛₑₜ-function₀[V] (baireSpace V) via baireSpaceFormula :=
  ⟨fun v ↦ by simp [baireSpaceFormula, baireSpace]⟩

instance naturalSequencesFormula_defined :
    ℒₛₑₜ-function₀[V] (naturalSequences V) via naturalSequencesFormula :=
  ⟨fun v ↦ by simp [naturalSequencesFormula, naturalSequences]⟩

theorem mem_naturalSequences_iff (s : V) :
    s ∈ naturalSequences V ↔ ∃ n ∈ (ω : V), s ∈ (ω : V) ^ n :=
  mem_finiteSequences_iff _ _

theorem restrict_mem_naturalSequences {x n : V} (hx : x ∈ baireSpace V) (hn : n ∈ (ω : V)) :
    x ↾ n ∈ naturalSequences V :=
  (mem_naturalSequences_iff _).mpr ⟨n, hn, function_restrict_mem hx (IsTransitive.transitive _ hn)⟩

noncomputable def baireTreeBody (T : V) : V :=
  {x ∈ baireSpace V ; ∀ n ∈ (ω : V), x ↾ n ∈ T}

theorem mem_baireTreeBody_iff (T x : V) :
    x ∈ baireTreeBody T ↔ x ∈ baireSpace V ∧ ∀ n ∈ (ω : V), x ↾ n ∈ T := by
  simp [baireTreeBody]

instance baireTreeBodyFormula_defined :
    ℒₛₑₜ-function₁[V] baireTreeBody via baireTreeBodyFormula :=
  ⟨fun v ↦ by simp [baireTreeBodyFormula, mem_ext_iff (y := baireTreeBody _), mem_baireTreeBody_iff]⟩

instance baireTreeBody_definable : ℒₛₑₜ-function₁[V] baireTreeBody :=
  baireTreeBodyFormula_defined.to_definable

noncomputable def baireOpenFrom (S : V) : V :=
  {x ∈ baireSpace V ; ∃ s ∈ S, x ↾ (domain s) = s}

theorem mem_baireOpenFrom_iff (S x : V) :
    x ∈ baireOpenFrom S ↔ x ∈ baireSpace V ∧ ∃ s ∈ S, x ↾ (domain s) = s := by
  simp [baireOpenFrom]

instance baireOpenFromFormula_defined :
    ℒₛₑₜ-function₁[V] baireOpenFrom via baireOpenFromFormula :=
  ⟨fun v ↦ by simp [baireOpenFromFormula, mem_ext_iff (y := baireOpenFrom _), mem_baireOpenFrom_iff]⟩

instance baireOpenFrom_definable : ℒₛₑₜ-function₁[V] baireOpenFrom :=
  baireOpenFromFormula_defined.to_definable

def IsBaireTree (T : V) : Prop :=
  T ⊆ naturalSequences V ∧ ∀ s ∈ T, ∀ n ∈ domain s, s ↾ n ∈ T

instance isBaireTreeFormula_defined : ℒₛₑₜ-predicate[V] IsBaireTree via isBaireTreeFormula :=
  ⟨fun v ↦ by simp [isBaireTreeFormula, IsBaireTree]⟩

instance isBaireTree_definable : ℒₛₑₜ-predicate[V] IsBaireTree :=
  isBaireTreeFormula_defined.to_definable

def IsPerfectBaireTree (T : V) : Prop :=
  IsBaireTree T ∧ (∅ : V) ∈ T ∧ ∀ s ∈ T, ∃ t ∈ T, ∃ u ∈ T, s ⊆ t ∧ s ⊆ u ∧ Incompatible t u

instance isPerfectBaireTreeFormula_defined :
    ℒₛₑₜ-predicate[V] IsPerfectBaireTree via isPerfectBaireTreeFormula :=
  ⟨fun v ↦ by simp [isPerfectBaireTreeFormula, IsPerfectBaireTree]⟩

instance isPerfectBaireTree_definable : ℒₛₑₜ-predicate[V] IsPerfectBaireTree :=
  isPerfectBaireTreeFormula_defined.to_definable

def BairePerfectSetProperty (A : V) : Prop :=
  IsInternallyCountable A ∨ ∃ T, IsPerfectBaireTree T ∧ baireTreeBody T ⊆ A

instance bairePerfectSetPropertyFormula_defined :
    ℒₛₑₜ-predicate[V] BairePerfectSetProperty via bairePerfectSetPropertyFormula :=
  ⟨fun v ↦ by simp [bairePerfectSetPropertyFormula, BairePerfectSetProperty, IsInternallyCountable]⟩

def IsNowhereDenseBaireTree (T : V) : Prop :=
  IsBaireTree T ∧ ∀ s ∈ naturalSequences V, ∃ t ∈ naturalSequences V, s ⊆ t ∧ t ∉ T

instance isNowhereDenseBaireTreeFormula_defined :
    ℒₛₑₜ-predicate[V] IsNowhereDenseBaireTree via isNowhereDenseBaireTreeFormula :=
  ⟨fun v ↦ by simp [isNowhereDenseBaireTreeFormula, IsNowhereDenseBaireTree]⟩

def IsBaireMeagre (A : V) : Prop :=
  ∃ f ∈ (℘ (naturalSequences V)) ^ (ω : V),
    (∀ n ∈ (ω : V), IsNowhereDenseBaireTree (f ‘ n)) ∧
    ∀ x ∈ A, ∃ n ∈ (ω : V), x ∈ baireTreeBody (f ‘ n)

instance isBaireMeagreFormula_defined : ℒₛₑₜ-predicate[V] IsBaireMeagre via isBaireMeagreFormula :=
  ⟨fun v ↦ by simp [isBaireMeagreFormula, IsBaireMeagre]⟩

def IsBaireOpen (U : V) : Prop := ∃ S, S ⊆ naturalSequences V ∧ U = baireOpenFrom S

instance isBaireOpenFormula_defined : ℒₛₑₜ-predicate[V] IsBaireOpen via isBaireOpenFormula :=
  ⟨fun v ↦ by simp [isBaireOpenFormula, IsBaireOpen]⟩

def BaireSpaceProperty (A : V) : Prop :=
  ∃ U, IsBaireOpen U ∧ IsBaireMeagre ((A \ U) ∪ (U \ A))

instance baireSpacePropertyFormula_defined :
    ℒₛₑₜ-predicate[V] BaireSpaceProperty via baireSpacePropertyFormula :=
  ⟨fun v ↦ by simp [baireSpacePropertyFormula, BaireSpaceProperty]⟩

instance bairePerfectSetPropertySentence_defined :
    Defined (fun _ : Fin 0 → V ↦ ∀ A : V, A ⊆ baireSpace V → BairePerfectSetProperty A)
      bairePerfectSetPropertySentence :=
  ⟨fun v ↦ by simp [bairePerfectSetPropertySentence]⟩

instance baireSpacePropertySentence_defined :
    Defined (fun _ : Fin 0 → V ↦ ∀ A : V, A ⊆ baireSpace V → BaireSpaceProperty A)
      baireSpacePropertySentence :=
  ⟨fun v ↦ by simp [baireSpacePropertySentence]⟩

end ZFVP
