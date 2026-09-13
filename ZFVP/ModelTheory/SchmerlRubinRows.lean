import ZFVP.ModelTheory.SchmerlCodedInclusionLaws
import ZFVP.ModelTheory.SchmerlAcceptedGuessFamily
import ZFVP.ModelTheory.SchmerlBoundedRubinSuccessor
import ZFVP.SetTheory.TransfiniteIteration

/-! Definable rows for the actual bounded Rubin recursion. Each row records
the inclusions and preservation obligations from every earlier stage. -/

namespace ZFVP.Schmerl
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

attribute [local irreducible] binaryRelationStructureCode codedChainCarrier codedChainEdges

noncomputable def codedBinaryChainUnion (θ C : V) : V :=
  binaryRelationStructureCode (codedChainCarrier θ C) (codedChainEdges θ C)

instance codedBinaryChainUnion_definable : ℒₛₑₜ-function₂[V] codedBinaryChainUnion := by
  unfold codedBinaryChainUnion
  definability

theorem codedBinaryChainUnion_congr {θ C H : V} (he : ∀ β ∈ θ, C ‘ β = H ‘ β) :
    codedBinaryChainUnion θ C = codedBinaryChainUnion θ H := by
  have hD : codedChainCarrier θ C = codedChainCarrier θ H := by
    apply mem_ext
    intro x
    simp only [mem_codedChainCarrier]
    exact exists_congr (fun β ↦ and_congr_right (fun hβ ↦ by rw [he β hβ]))
  have hE : codedChainEdges θ C = codedChainEdges θ H := by
    apply mem_ext
    intro p
    simp only [mem_codedChainEdges, mem_codedChainRelation]
    apply exists_congr
    intro s
    apply and_congr_left
    intro _
    exact exists_congr (fun β ↦ and_congr_right (fun hβ ↦ by rw [he β hβ]))
  simp only [codedBinaryChainUnion, hD, hE]

structure RubinRow (A M₀ α C M : V) : Prop where
  bounded : M ∈ boundedBinaryModelCodes (hartogsNumber (ω : V))
  model : IsCodedZFModel M
  countable : IsInternallyCountable (structureDomain M)
  initial : α = ∅ → M = M₀
  elementary : ∀ β ∈ α, IsCodedElementaryInclusion (C ‘ β) M
  finite : ∀ β ∈ α, IsCodedFiniteEndExtension (C ‘ β) M
  guesses : ∀ β ∈ α,
    IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) →
      IsCodedInseparable M (guessedU A C β) (guessedW A C β)
  successor : ∀ β ∈ α, α = succ β → β ∈ structureDomain M ∧
    ∃ c, IsCodedCofinalBounds (C ‘ β) M (SetTheory.identity (structureDomain (C ‘ β))) c
  limit : IsLimitOrdinal α → M = codedBinaryChainUnion α C

theorem rubinRow_iff (A M₀ α C M : V) : RubinRow A M₀ α C M ↔
    M ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ∧ IsCodedZFModel M ∧
    IsInternallyCountable (structureDomain M) ∧ (α = ∅ → M = M₀) ∧
    (∀ β ∈ α, IsCodedElementaryInclusion (C ‘ β) M) ∧
    (∀ β ∈ α, IsCodedFiniteEndExtension (C ‘ β) M) ∧
    (∀ β ∈ α, IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) →
      IsCodedInseparable M (guessedU A C β) (guessedW A C β)) ∧
    (∀ β ∈ α, α = succ β → β ∈ structureDomain M ∧
      ∃ c, IsCodedCofinalBounds (C ‘ β) M (SetTheory.identity (structureDomain (C ‘ β))) c) ∧
    (IsLimitOrdinal α → M = codedBinaryChainUnion α C) := by
  constructor
  · intro h
    exact ⟨h.bounded, h.model, h.countable, h.initial, h.elementary, h.finite, h.guesses, h.successor, h.limit⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩

attribute [local irreducible] boundedBinaryModelCodes IsCodedZFModel IsInternallyCountable
  IsCodedElementaryEmbedding IsCodedFiniteEndExtension IsCodedInseparable guessedU guessedW
  IsCodedCofinalBounds codedBinaryChainUnion hartogsNumber

theorem rubinRow_definable (A M₀ : V) : ℒₛₑₜ-relation₃[V] (RubinRow A M₀) := by
  apply Language.Definable.of_iff (show ℒₛₑₜ-relation₃[V] (fun α C M ↦
    M ∈ boundedBinaryModelCodes (hartogsNumber (ω : V)) ∧ IsCodedZFModel M ∧
    IsInternallyCountable (structureDomain M) ∧ (α = ∅ → M = M₀) ∧
    (∀ β ∈ α, IsCodedElementaryInclusion (C ‘ β) M) ∧
    (∀ β ∈ α, IsCodedFiniteEndExtension (C ‘ β) M) ∧
    (∀ β ∈ α, IsCodedInseparable (C ‘ β) (guessedU A C β) (guessedW A C β) →
      IsCodedInseparable M (guessedU A C β) (guessedW A C β)) ∧
    (∀ β ∈ α, α = succ β → β ∈ structureDomain M ∧
      ∃ c, IsCodedCofinalBounds (C ‘ β) M (SetTheory.identity (structureDomain (C ‘ β))) c) ∧
    (IsLimitOrdinal α → M = codedBinaryChainUnion α C)) from by
      unfold IsLimitOrdinal IsCodedElementaryInclusion
      definability)
  intro v
  exact rubinRow_iff _ _ _ _ _

theorem RubinRow.congr {A M₀ α C H M : V} (h : RubinRow A M₀ α C M)
    (he : ∀ β ∈ α, C ‘ β = H ‘ β) : RubinRow A M₀ α H M := by
  have hU (β : V) (hβ : β ∈ α) : guessedU A C β = guessedU A H β := by
    simp only [guessedU, he β hβ]
  have hW (β : V) (hβ : β ∈ α) : guessedW A C β = guessedW A H β := by
    simp only [guessedW, he β hβ, hU β hβ]
  refine ⟨h.bounded, h.model, h.countable, h.initial, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    simpa only [he β hβ] using h.elementary β hβ
  · intro β hβ
    simpa only [he β hβ] using h.finite β hβ
  · intro β hβ
    simpa only [he β hβ, hU β hβ, hW β hβ] using h.guesses β hβ
  · intro β hβ
    simpa only [he β hβ] using h.successor β hβ
  · intro hlim
    exact (h.limit hlim).trans (codedBinaryChainUnion_congr he)

theorem rubinRows_chain {A M₀ θ C : V} (hθ : IsOrdinal θ) (hne : IsNonempty θ)
    (hf : IsFunction C) (hd : domain C = θ)
    (hrows : ∀ α ∈ θ, RubinRow A M₀ α C (C ‘ α)) :
    IsInternalRelationalChain membershipLanguageCode θ C := by
  let : IsOrdinal θ := hθ
  have hel : ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedElementaryInclusion (C ‘ i) (C ‘ j) := by
    intro i hi j hj hij
    let : IsOrdinal i := IsOrdinal.of_mem hi
    let : IsOrdinal j := IsOrdinal.of_mem hj
    rcases IsOrdinal.subset_iff.mp hij with rfl | hij
    · exact IsCodedElementaryEmbedding.identity (hrows i hi).model.valid
    · exact (hrows j hj).elementary i hij
  exact ⟨hθ, hne, hf, hd, by simp [membershipLanguageCode],
    fun i hi ↦ (hrows i hi).model.valid,
    fun i hi j hj hij ↦ (hel i hi j hj hij).subset,
    fun i hi j hj hij _ hr _ hs ↦ (hel i hi j hj hij).binary_coherent
      (hrows i hi).bounded (hrows j hj).bounded hr hs,
    hel⟩

theorem rubinRows_finite {A M₀ θ C : V} (hθ : IsOrdinal θ)
    (hrows : ∀ α ∈ θ, RubinRow A M₀ α C (C ‘ α)) :
    ∀ i ∈ θ, ∀ j ∈ θ, i ⊆ j → IsCodedFiniteEndExtension (C ‘ i) (C ‘ j) := by
  let : IsOrdinal θ := hθ
  intro i hi j hj hij
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · exact IsCodedFiniteEndExtension.refl _
  · exact (hrows j hj).finite i hij

theorem rubinRows_guesses {A M₀ θ C : V} (hθ : IsOrdinal θ)
    (hrows : ∀ α ∈ θ, RubinRow A M₀ α C (C ‘ α)) : PreservesAcceptedGuesses θ C A := by
  let : IsOrdinal θ := hθ
  intro i hi j hj hij hacc
  let : IsOrdinal i := IsOrdinal.of_mem hi
  let : IsOrdinal j := IsOrdinal.of_mem hj
  rcases IsOrdinal.subset_iff.mp hij with rfl | hij
  · exact hacc
  · exact (hrows j hj).guesses i hij hacc

end ZFVP.Schmerl
