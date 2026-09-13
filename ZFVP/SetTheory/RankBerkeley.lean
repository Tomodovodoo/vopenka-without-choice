import ZFVP.SetTheory.ProtoRankBerkeley

/-! The literal rank-Berkeley clause and its explicit nonzero convention.
The universal clause alone includes zero. Descent uses the nonzero version. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def rankBerkeleyClauseFormula : SetTheorySemisentence 1 :=
  “δ. !initialOrdinalFormula δ ∧ ∀ ζ ∈ δ, !protoRankBerkeleyFormula ζ δ”

def nonzeroRankBerkeleyFormula : SetTheorySemisentence 1 :=
  “δ. !isNonempty δ ∧ !rankBerkeleyClauseFormula δ”

def nonzeroRankBerkeleyExistenceSentence : SetTheorySentence :=
  “∃ δ, !nonzeroRankBerkeleyFormula δ”

def literalRankBerkeleyExistenceSentence : SetTheorySentence :=
  “∃ δ, !rankBerkeleyClauseFormula δ”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def RankBerkeleyClause (δ : V) : Prop :=
  IsInitialOrdinal δ ∧ ∀ ζ ∈ δ, IsProtoRankBerkeley ζ δ

def IsNonzeroRankBerkeley (δ : V) : Prop := IsNonempty δ ∧ RankBerkeleyClause δ

instance rankBerkeleyClauseFormula_defined :
    ℒₛₑₜ-predicate[V] RankBerkeleyClause via rankBerkeleyClauseFormula :=
  ⟨fun v ↦ by simp [rankBerkeleyClauseFormula, RankBerkeleyClause]⟩

instance rankBerkeleyClause_definable : ℒₛₑₜ-predicate[V] RankBerkeleyClause :=
  rankBerkeleyClauseFormula_defined.to_definable

instance nonzeroRankBerkeleyFormula_defined :
    ℒₛₑₜ-predicate[V] IsNonzeroRankBerkeley via nonzeroRankBerkeleyFormula :=
  ⟨fun v ↦ by simp [nonzeroRankBerkeleyFormula, IsNonzeroRankBerkeley]⟩

instance nonzeroRankBerkeley_definable : ℒₛₑₜ-predicate[V] IsNonzeroRankBerkeley :=
  nonzeroRankBerkeleyFormula_defined.to_definable

@[simp] theorem eval_nonzeroRankBerkeleyExistenceSentence :
    nonzeroRankBerkeleyExistenceSentence.Evalb (![] : Fin 0 → V) ↔
      ∃ δ : V, IsNonzeroRankBerkeley δ := by
  simp [nonzeroRankBerkeleyExistenceSentence]

theorem rankBerkeleyClause_zero : RankBerkeleyClause (0 : V) := by
  simp [RankBerkeleyClause, IsInitialOrdinal, zero_def]

theorem models_literalRankBerkeleyExistenceSentence :
    V↓[ℒₛₑₜ] ⊧ literalRankBerkeleyExistenceSentence := by
  simpa [models_iff, literalRankBerkeleyExistenceSentence] using
    (show ∃ δ : V, RankBerkeleyClause δ from ⟨0, rankBerkeleyClause_zero⟩)

theorem zf_proves_literalRankBerkeleyExistence : 𝗭𝗙 ⊢ literalRankBerkeleyExistenceSentence :=
  provable_of_models 𝗭𝗙 literalRankBerkeleyExistenceSentence
    (fun (M : Type) _ _ _ ↦ models_literalRankBerkeleyExistenceSentence (V := M))

theorem rankBerkeleyClause_iff_zero_or_nonzero (δ : V) :
    RankBerkeleyClause δ ↔ δ = 0 ∨ IsNonzeroRankBerkeley δ := by
  constructor
  · intro hδ
    rcases eq_empty_or_isNonempty δ with he | hn
    · exact Or.inl he
    · exact Or.inr ⟨hn, hδ⟩
  · rintro (rfl | hδ)
    · exact rankBerkeleyClause_zero
    · exact hδ.2

theorem RankBerkeleyClause.succ_closed {δ ζ : V} (hδ : RankBerkeleyClause δ) (hζ : ζ ∈ δ) :
    succ ζ ∈ δ := by
  let := hδ.1.1
  let := IsOrdinal.of_mem hζ
  obtain ⟨f, κ, _, _, hζκ, hκδ, _⟩ := (hδ.2 ζ hζ).2.2 (succ δ) inferInstance (by simp)
  let := IsOrdinal.of_mem hκδ
  have hsub : succ ζ ⊆ κ := by
    intro x hx
    rcases mem_succ_iff.mp hx with rfl | hx
    · exact hζκ
    · exact IsOrdinal.toIsTransitive.mem_trans hx hζκ
  rcases IsOrdinal.subset_iff.mp hsub with he | hm
  · exact he ▸ hκδ
  · exact IsOrdinal.toIsTransitive.mem_trans hm hκδ

theorem IsNonzeroRankBerkeley.zero_mem {δ : V} (hδ : IsNonzeroRankBerkeley δ) : (0 : V) ∈ δ := by
  let := hδ.2.1.1
  exact IsOrdinal.empty_mem_iff_nonempty.mpr hδ.1

theorem IsNonzeroRankBerkeley.omega_subset {δ : V} (hδ : IsNonzeroRankBerkeley δ) : (ω : V) ⊆ δ :=
  IsInductive.ω_subset ⟨hδ.zero_mem, fun _ h ↦ hδ.2.succ_closed h⟩

theorem nonzeroRankBerkeley_iff_infinite_clause (δ : V) :
    IsNonzeroRankBerkeley δ ↔ (ω : V) ⊆ δ ∧ RankBerkeleyClause δ := by
  constructor
  · intro hδ
    exact ⟨hδ.omega_subset, hδ.2⟩
  · rintro ⟨hω, hδ⟩
    exact ⟨⟨⟨0, hω 0 (by simp)⟩⟩, hδ⟩

theorem IsNonzeroRankBerkeley.proto {δ ζ : V} (hδ : IsNonzeroRankBerkeley δ) (hζ : ζ ∈ δ) :
    IsProtoRankBerkeley ζ δ := hδ.2.2 ζ hζ

theorem IsNonzeroRankBerkeley.proto_zero {δ : V} (hδ : IsNonzeroRankBerkeley δ) :
    IsProtoRankBerkeley 0 δ := hδ.proto hδ.zero_mem

end ZFVP
