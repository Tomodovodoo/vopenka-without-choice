import ZFVP.ModelTheory.PrunedUnboundedExtendibility

/-! Exact dictionary for the literal rank-Berkeley definition in V13, line 481.
The paper's universal clause includes the zero initial ordinal. Consequently its
literal no-rank-Berkeley extension is inconsistent. The proved nonzero pruning
theorem instead says that zero is the only cardinal satisfying that clause. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory Entailment

section Dictionary

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The quantified definition at V13 line 481, without a positivity convention. -/
def V13RankBerkeley (δ : V) : Prop :=
  IsInitialOrdinal δ ∧ ∀ ζ ∈ δ, ∀ Θ, IsOrdinal Θ → δ ∈ Θ → ∃ f κ,
    IsCodedMembershipEmbedding (hierarchy Θ) (hierarchy Θ) f ∧
    IsCriticalPoint (hierarchy Θ) f κ ∧ ζ ∈ κ ∧ κ ∈ δ ∧ f ‘ δ = δ

theorem v13RankBerkeley_iff_clause (δ : V) :
    V13RankBerkeley δ ↔ RankBerkeleyClause δ := by
  constructor
  · rintro ⟨hδ, h⟩
    exact ⟨hδ, fun ζ hζ ↦ ⟨hδ, hζ, h ζ hζ⟩⟩
  · rintro ⟨hδ, h⟩
    exact ⟨hδ, fun ζ hζ ↦ (h ζ hζ).2.2⟩

theorem v13RankBerkeley_iff_zero_or_nonzero (δ : V) :
    V13RankBerkeley δ ↔ δ = 0 ∨ IsNonzeroRankBerkeley δ :=
  (v13RankBerkeley_iff_clause δ).trans (rankBerkeleyClause_iff_zero_or_nonzero δ)

theorem v13RankBerkeley_zero : V13RankBerkeley (0 : V) :=
  (v13RankBerkeley_iff_clause 0).mpr rankBerkeleyClause_zero

/-- What the nonzero pruning conclusion says in terms of the literal paper clause. -/
theorem no_nonzeroRankBerkeley_iff_v13_only_zero :
    (∀ δ : V, ¬IsNonzeroRankBerkeley δ) ↔
      ∀ δ : V, V13RankBerkeley δ → δ = 0 := by
  constructor
  · intro h δ hδ
    exact (v13RankBerkeley_iff_zero_or_nonzero δ).mp hδ |>.resolve_right (h δ)
  · intro h δ hδ
    have he := h δ ((v13RankBerkeley_iff_clause δ).mpr hδ.2)
    have hz := hδ.zero_mem
    simp [he] at hz

end Dictionary

/-- The literal theory stated by V13 Proposition OH-pruning, lines 534-539. -/
def zfUEVPNoLiteralRankBerkeleyTheory : Theory ℒₛₑₜ :=
  insert (∼literalRankBerkeleyExistenceSentence) zfUEVPTheory

theorem not_consistent_no_literalRankBerkeley {T : Theory ℒₛₑₜ}
    (hZF : 𝗭𝗙 ⪯ T) :
    ¬Consistent (insert (∼literalRankBerkeleyExistenceSentence) T) := by
  let := hZF
  intro h
  exact (unprovable_iff_consistent_adjoin.mpr h)
    (WeakerThan.pbl zf_proves_literalRankBerkeleyExistence)

theorem not_consistent_v13_literal_pruned_UE :
    ¬Consistent zfUEVPNoLiteralRankBerkeleyTheory :=
  not_consistent_no_literalRankBerkeley
    (WeakerThan.ofSubset (fun _ hφ ↦ Or.inl (Or.inl hφ)))

/-- Under the very premise of the paper's pruning implication, its literal
conclusion fails. This does not assume consistency of ZF+VP unconditionally. -/
theorem v13_literal_pruning_implication_fails (h : Consistent zfVPTheory) :
    ¬(Consistent zfVPTheory → Consistent zfUEVPNoLiteralRankBerkeleyTheory) :=
  fun hp ↦ not_consistent_v13_literal_pruned_UE (hp h)

end ZFVP
