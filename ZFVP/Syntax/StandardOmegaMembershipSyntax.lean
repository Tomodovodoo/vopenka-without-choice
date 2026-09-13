import ZFVP.Syntax.BinaryRelationSemanticStandardness
import ZFVP.SetTheory.FormulaFamilyRank

/-! Omega standardness suffices to decode every internal membership formula.
Only the finite rank of syntax is used, not external well-foundedness of V. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem binary_formula_representable_of_standardOmega (hω : Schmerl.HasStandardOmega V)
    {k : ℕ} {φ : V} (hφ : IsMembershipFormulaCode (k : V) φ) :
    ∃ ψ : SetTheorySemisentence k, BinaryFormulaRepresents φ ψ := by
  have hbounded : ∀ m : ℕ, ∀ (k : ℕ) (φ : V), rank φ ∈ (m : V) →
      IsMembershipFormulaCode (k : V) φ → ∃ ψ : SetTheorySemisentence k, BinaryFormulaRepresents φ ψ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k φ hm hφ
      obtain ⟨j, hj⟩ := (mem_natCast_iff (rank φ) m).mp hm
      have ihφ {χ : V} {l : ℕ} (hχ : rank χ ∈ rank φ)
          (hc : IsMembershipFormulaCode (l : V) χ) :
          ∃ ψ : SetTheorySemisentence l, BinaryFormulaRepresents χ ψ :=
        ih j.val j.isLt l χ (hj ▸ hχ) hc
      rcases formulaSet_cases membershipLanguageCode_valid hφ.valid with
        rfl | rfl | ⟨r, args, ha, he⟩ | ⟨χ, θ, hχ, hθ, he⟩ | ⟨χ, hχ, he⟩
      · exact ⟨⊤, BinaryFormulaRepresents.truth k⟩
      · exact ⟨⊥, BinaryFormulaRepresents.falsity k⟩
      · obtain ⟨ψ, hp, hn⟩ := binary_atoms_representable ha
        rcases he with rfl | rfl
        · exact ⟨ψ, hp⟩
        · exact ⟨∼ψ, hn⟩
      · have hc : IsMembershipFormulaCode (k : V) χ := (mem_formulaSet_iff _ _ _ _).mp hχ
        have ht : IsMembershipFormulaCode (k : V) θ := (mem_formulaSet_iff _ _ _ _).mp hθ
        have hχφ : rank χ ∈ rank φ := by
          rcases he with rfl | rfl
          · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt χ θ) (rank_kpair_right_lt (4 : V) _)
          · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_left_lt χ θ) (rank_kpair_right_lt (5 : V) _)
        have hθφ : rank θ ∈ rank φ := by
          rcases he with rfl | rfl
          · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt χ θ) (rank_kpair_right_lt (4 : V) _)
          · exact IsOrdinal.toIsTransitive.mem_trans (rank_kpair_right_lt χ θ) (rank_kpair_right_lt (5 : V) _)
        obtain ⟨ψ, hψ⟩ := ihφ hχφ hc
        obtain ⟨ρ, hρ⟩ := ihφ hθφ ht
        rcases he with rfl | rfl
        · exact ⟨ψ ⋏ ρ, hψ.conj hc ht hρ⟩
        · exact ⟨ψ ⋎ ρ, hψ.disj hc ht hρ⟩
      · have hc : IsMembershipFormulaCode ((k + 1 : ℕ) : V) χ := by
          simpa only [IsMembershipFormulaCode, num_succ_def] using (mem_formulaSet_iff _ _ _ _).mp hχ
        have hχφ : rank χ ∈ rank φ := by
          rcases he with rfl | rfl
          · exact rank_kpair_right_lt (6 : V) χ
          · exact rank_kpair_right_lt (7 : V) χ
        obtain ⟨ψ, hψ⟩ := ihφ hχφ hc
        rcases he with rfl | rfl
        · exact ⟨∀¹ ψ, hψ.all hc⟩
        · exact ⟨∃¹ ψ, hψ.exs hc⟩
  let := hierarchy_transitive (ω : V)
  have hhf : φ ∈ hierarchy (ω : V) :=
    (kpair_components_mem_transitive (formulaFamily_subset_hierarchy_omega _ hφ)).2
  have hr : rank φ ∈ (ω : V) := by rwa [mem_hierarchy_iff_rank_mem] at hhf
  obtain ⟨m, hm⟩ := hω (rank φ) hr
  apply hbounded (m + 1) k φ _ hφ
  rw [hm, num_succ_def]
  simp

theorem semanticStandardMembershipSyntax_of_standardOmega (hω : Schmerl.HasStandardOmega V) :
    SemanticStandardMembershipSyntax V :=
  ⟨hω, fun _ _ hφ ↦ binary_formula_representable_of_standardOmega hω hφ⟩

end ZFVP
