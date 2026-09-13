import ZFVP.Syntax.EndExtensionFormulas
import ZFVP.Syntax.MembershipTruthTables
import ZFVP.Syntax.EndExtensionAssignments

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_constantGraph (j : MembershipEndExtension V W) (A a : V) :
    j (constantGraph A a) = constantGraph (j A) (j a) := by
  exact j.map_definableGraph A (fun _ ↦ a) (fun _ ↦ j a)
    (by definability) (by definability) (fun _ _ ↦ rfl)

theorem map_membershipLanguageCode (j : MembershipEndExtension V W) :
    j (membershipLanguageCode : V) = (membershipLanguageCode : W) := by
  unfold membershipLanguageCode languageCode
  simp only [j.map_kpair, j.map_constantGraph, j.map_empty, show j (2 : V) = (2 : W) from j.map_numeral 2]

theorem map_membershipFormulaFamily (j : MembershipEndExtension V W) :
    j (formulaFamily membershipLanguageCode ∅) = formulaFamily membershipLanguageCode ∅ := by
  rw [j.map_formulaFamily membershipLanguageCode_valid, j.map_membershipLanguageCode, j.map_empty]

theorem membershipFormulaCode_iff (j : MembershipEndExtension V W) (n φ : V) :
    IsMembershipFormulaCode (j n) (j φ) ↔ IsMembershipFormulaCode n φ := by
  unfold IsMembershipFormulaCode
  rw [← j.map_membershipFormulaFamily, ← j.map_kpair, j.mem_iff]

theorem membershipFormulaCode_preimages (j : MembershipEndExtension V W) {n φ : W}
    (hφ : IsMembershipFormulaCode n φ) :
    ∃ m ψ : V, n = j m ∧ φ = j ψ ∧ IsMembershipFormulaCode m ψ := by
  unfold IsMembershipFormulaCode at hφ
  rw [← j.map_membershipFormulaFamily, j.pair_mem_image_iff] at hφ
  obtain ⟨m, ψ, hψ, hn, hφ⟩ := hφ
  exact ⟨m, ψ, hn, hφ, hψ⟩

theorem map_boundPairArguments (j : MembershipEndExtension V W) (a b : V) :
    j (boundPairArguments a b) = boundPairArguments (j a) (j b) := by
  unfold boundPairArguments
  rw [j.map_standardTuple]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun k ↦ Fin.elim0 k) i) i
  · exact j.map_boundVarCode a
  · exact j.map_boundVarCode b

theorem membershipAtomicArguments_map (j : MembershipEndExtension V W) {n r args : V}
    (ha : IsMembershipAtomicArguments n r args) :
    IsMembershipAtomicArguments (j n) (j r) (j args) := by
  obtain ⟨hr, a, ha, b, hb, rfl⟩ := ha
  refine ⟨?_, j a, (j.mem_iff _ _).mpr ha, j b, (j.mem_iff _ _).mpr hb,
    j.map_boundPairArguments a b⟩
  rcases hr with rfl | rfl | rfl
  · exact Or.inl j.map_equalityToken
  · exact Or.inr (Or.inl (by rw [j.map_relationToken, show j (0 : V) = (0 : W) from j.map_numeral 0]))
  · exact Or.inr (Or.inr (by rw [j.map_relationToken, show j (1 : V) = (1 : W) from j.map_numeral 1]))

end MembershipEndExtension
end ZFVP
