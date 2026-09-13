import ZFVP.Syntax.EndExtensionMembershipPreimages
import ZFVP.Syntax.PiOneBoundedCodes
import ZFVP.SetTheory.EndExtensionLevy

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem boundedFormulaCode_iff (j : MembershipEndExtension V W) (n φ : V) :
    IsBoundedFormulaCode n φ ↔ IsBoundedFormulaCode (j n) (j φ) :=
  j.deltaOne_defined sigmaOneBoundedCodeFormula_sigmaOne piOneBoundedCodeFormula_piOne
    (fun v ↦ IsBoundedFormulaCode (v 0) (v 1))
    (fun v ↦ IsBoundedFormulaCode (v 0) (v 1)) ![n, φ]

theorem boundedFormulaCode_preimages (j : MembershipEndExtension V W) {n φ : W}
    (hφ : IsBoundedFormulaCode n φ) :
    ∃ m ψ : V, n = j m ∧ φ = j ψ ∧ IsBoundedFormulaCode m ψ := by
  obtain ⟨m, ψ, rfl, rfl, _⟩ := j.membershipFormulaCode_preimages (boundedFormulaFamily_subset _ hφ)
  exact ⟨m, ψ, rfl, rfl, (j.boundedFormulaCode_iff m ψ).mpr hφ⟩

theorem map_boundedFormulaFamily (j : MembershipEndExtension V W) :
    j (boundedFormulaFamily : V) = (boundedFormulaFamily : W) := by
  apply mem_ext
  intro q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := j.endExtension _ q hq
    obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ (boundedFormulaFamily_subset _ hp)
    rw [j.map_kpair]
    exact (j.boundedFormulaCode_iff n φ).mp hp
  · intro hq
    obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ (boundedFormulaFamily_subset _ hq)
    obtain ⟨m, ψ, rfl, rfl, hψ⟩ := j.boundedFormulaCode_preimages hq
    rw [← j.map_kpair]
    exact (j.mem_iff _ _).mpr hψ

end MembershipEndExtension
end ZFVP
