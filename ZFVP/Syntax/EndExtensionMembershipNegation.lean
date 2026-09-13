import ZFVP.Syntax.EndExtensionDefinableInduction
import ZFVP.Syntax.FormulaNegation

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
namespace MembershipEndExtension
variable {V W : Type*} [SetStructure V] [SetStructure W]
  [Nonempty V] [Nonempty W] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem map_membershipNegation (j : MembershipEndExtension V W) {n φ : V}
    (hφ : IsMembershipFormulaCode n φ) :
    j (negateFormula membershipLanguageCode ∅ n φ) =
      negateFormula membershipLanguageCode ∅ (j n) (j φ) := by
  let P : V → V → Prop := fun n φ ↦ j (negateFormula membershipLanguageCode ∅ n φ) =
    negateFormula membershipLanguageCode ∅ (j n) (j φ)
  let Q : W → Prop := fun q ↦ (j (formulaNegationGraph membershipLanguageCode ∅)) ‘ q =
    negateFormula membershipLanguageCode ∅ (kpair.π₁ q) (kpair.π₂ q)
  apply j.membershipFormula_induction_via P Q (by dsimp [Q]; definability) ?_ ?_ ?_ ?_ ?_ n φ hφ
  · intro n φ _
    dsimp [P, Q, negateFormula]
    rw [j.map_kpair, kpair.π₁_kpair, kpair.π₂_kpair, j.map_value_total, j.map_kpair]
  · intro n hn
    have hn' := (j.natural_iff n).mpr hn
    dsimp [P]
    rw [negateFormula_truth membershipLanguageCode_valid hn, negateFormula_falsity membershipLanguageCode_valid hn,
      j.map_truthCode, j.map_falsityCode, negateFormula_truth membershipLanguageCode_valid hn',
      negateFormula_falsity membershipLanguageCode_valid hn']
    exact ⟨rfl, rfl⟩
  · intro n hn r args ha
    have hn' := (j.natural_iff n).mpr hn
    have ha' := (membershipAtomicArguments_iff hn').mpr
      (j.membershipAtomicArguments_map ((membershipAtomicArguments_iff hn).mp ha))
    dsimp [P]
    rw [negateFormula_atom membershipLanguageCode_valid hn ha, negateFormula_negAtom membershipLanguageCode_valid hn ha,
      j.map_atomCode, j.map_negAtomCode, negateFormula_atom membershipLanguageCode_valid hn' ha',
      negateFormula_negAtom membershipLanguageCode_valid hn' ha']
    exact ⟨rfl, rfl⟩
  · intro n hn φ ψ hφ hψ ihφ ihψ
    have hn' := (j.natural_iff n).mpr hn
    have hφ' := ((j.membershipFormulaCode_iff n φ).mpr hφ).valid
    have hψ' := ((j.membershipFormulaCode_iff n ψ).mpr hψ).valid
    dsimp [P] at ihφ ihψ ⊢
    rw [negateFormula_and membershipLanguageCode_valid hn hφ.valid hψ.valid,
      negateFormula_or membershipLanguageCode_valid hn hφ.valid hψ.valid,
      j.map_andCode, j.map_orCode, j.map_andCode, j.map_orCode,
      negateFormula_and membershipLanguageCode_valid hn' hφ' hψ',
      negateFormula_or membershipLanguageCode_valid hn' hφ' hψ', ihφ, ihψ]
    exact ⟨rfl, rfl⟩
  · intro n hn φ hφ ihφ
    have hn' := (j.natural_iff n).mpr hn
    have hφ' : j φ ∈ formulaSet membershipLanguageCode ∅ (succ (j n)) := by
      rw [← j.map_succ]
      exact ((j.membershipFormulaCode_iff (succ n) φ).mpr hφ).valid
    dsimp [P] at ihφ ⊢
    rw [negateFormula_all membershipLanguageCode_valid hn hφ.valid,
      negateFormula_exists membershipLanguageCode_valid hn hφ.valid,
      j.map_allCode, j.map_existsCode, j.map_allCode, j.map_existsCode,
      negateFormula_all membershipLanguageCode_valid hn' hφ',
      negateFormula_exists membershipLanguageCode_valid hn' hφ', ihφ, j.map_succ]
    exact ⟨rfl, rfl⟩

end MembershipEndExtension
end ZFVP
