import ZFVP.SetTheory.CorrectDomains
import ZFVP.Syntax.LevyCodeAbsoluteness

/-! Upward and downward preservation at every standard Levy level. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem correctDomain_code_absolute {k : ℕ} {p : LevyPolarity} {A B n φ b : V}
    (hA : CorrectDomain k A) (hB : CorrectDomain k B) (hφ : IsLevyFormulaCode p k n φ)
    (hbA : b ∈ A ^ n) (hbB : b ∈ B ^ n) :
    MembershipSatisfies A n φ b ↔ MembershipSatisfies B n φ b := by
  let := hA.support
  let := hB.support
  cases k with
  | zero => exact boundedFormulaCode_absolute hφ A B inferInstance inferInstance hA.nonempty hB.nonempty b hbA hbB
  | succ k =>
    cases p with
    | sigma => exact (hA.sigmaTruth_iff hφ hbA).symm.trans (hB.sigmaTruth_iff hφ hbB)
    | pi =>
      have hn := (hA.sigmaTruth_iff hφ.neg hbA).symm.trans (hB.sigmaTruth_iff hφ.neg hbB)
      have hbA' : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hbA
      have hbB' : b ∈ structureDomain (membershipStructureCode B) ^ n := by simpa using hbB
      have he : ¬MembershipSatisfies A n φ b ↔ ¬MembershipSatisfies B n φ b :=
        (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbA').symm.trans
          (hn.trans (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbB'))
      exact not_iff_not.mp he

def CorrectSatisfactionUpward (k : ℕ) (n φ : V) : Prop :=
  ∀ A B : V, CorrectDomain k A → CorrectDomain k B → A ⊆ B →
    ∀ b ∈ A ^ n, MembershipSatisfies A n φ b → MembershipSatisfies B n φ b

instance correctSatisfactionUpward_definable (k : ℕ) : ℒₛₑₜ-relation[V] (CorrectSatisfactionUpward k) := by
  unfold CorrectSatisfactionUpward
  definability

theorem correctDomainCode_upward (k : ℕ) {n φ : V} (hφ : IsLevyFormulaCode .sigma (k + 1) n φ) :
    CorrectSatisfactionUpward k n φ := by
  refine levyFormulaCode_successor_induction k .sigma (CorrectSatisfactionUpward k)
    (by definability) ?_ ?_ ?_ ?_ n φ hφ
  · intro p n φ hφ A B hA hB hAB b hb hs
    exact (correctDomain_code_absolute hA hB hφ hb (mem_function_of_mem_function_of_subset hb hAB)).mp hs
  · intro n hn φ ψ hφ hψ ihφ ihψ
    constructor
    · intro A B hA hB hAB b hb hs
      let hAt := hA.support.toIsTransitive
      let hBt := hB.support.toIsTransitive
      have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
      have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
        simpa using mem_function_of_mem_function_of_subset hb hAB
      obtain ⟨hsφ, hsψ⟩ := (satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hbA).mp hs
      exact (satisfies_and membershipLanguageCode_valid hn hφ.valid hψ.valid hbB).mpr
        ⟨ihφ A B hA hB hAB b hb hsφ, ihψ A B hA hB hAB b hb hsψ⟩
    · intro A B hA hB hAB b hb hs
      let hAt := hA.support.toIsTransitive
      let hBt := hB.support.toIsTransitive
      have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
      have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
        simpa using mem_function_of_mem_function_of_subset hb hAB
      apply (satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hbB).mpr
      exact ((satisfies_or membershipLanguageCode_valid hn hφ.valid hψ.valid hbA).mp hs).elim
        (fun h ↦ Or.inl (ihφ A B hA hB hAB b hb h))
        (fun h ↦ Or.inr (ihψ A B hA hB hAB b hb h))
  · intro n hn i hi φ hφ ih
    constructor
    · intro A B hA hB hAB b hb hs
      let hAt := hA.support.toIsTransitive
      let hBt := hB.support.toIsTransitive
      let := hAt
      let := hBt
      have hbB := mem_function_of_mem_function_of_subset hb hAB
      apply (membershipSatisfies_boundedAll hn hi hφ.valid hbB).mpr
      intro x hx
      have hxA := hAt.transitive _ (function_value_mem hb hi) x hx
      exact ih A B hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA)
        ((membershipSatisfies_boundedAll hn hi hφ.valid hb).mp hs x hx)
    · intro A B hA hB hAB b hb hs
      let hAt := hA.support.toIsTransitive
      let hBt := hB.support.toIsTransitive
      let := hAt
      let := hBt
      have hbB := mem_function_of_mem_function_of_subset hb hAB
      obtain ⟨x, hx, hsx⟩ := (membershipSatisfies_boundedExists hn hi hφ.valid hb).mp hs
      have hxA := hAt.transitive _ (function_value_mem hb hi) x hx
      exact (membershipSatisfies_boundedExists hn hi hφ.valid hbB).mpr
        ⟨x, hx, ih A B hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA) hsx⟩
  · intro n hn φ hφ ih A B hA hB hAB b hb hs
    have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
    have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
      simpa using mem_function_of_mem_function_of_subset hb hAB
    obtain ⟨x, hx, hsx⟩ := (satisfies_exists membershipLanguageCode_valid hn hφ.valid hbA).mp hs
    have hxA : x ∈ A := by simpa using hx
    exact (satisfies_exists membershipLanguageCode_valid hn hφ.valid hbB).mpr
      ⟨x, by simpa using hAB x hxA,
        ih A B hA hB hAB _ (assignmentPrepend_mem_function hn hb hxA) hsx⟩

theorem correctDomainCode_downward (k : ℕ) {A B n φ b : V}
    (hφ : IsLevyFormulaCode .pi (k + 1) n φ) (hA : CorrectDomain k A) (hB : CorrectDomain k B)
    (hAB : A ⊆ B) (hb : b ∈ A ^ n) :
    MembershipSatisfies B n φ b → MembershipSatisfies A n φ b := by
  intro hs
  by_contra hn
  have hbA : b ∈ structureDomain (membershipStructureCode A) ^ n := by simpa using hb
  have hbB : b ∈ structureDomain (membershipStructureCode B) ^ n := by
    simpa using mem_function_of_mem_function_of_subset hb hAB
  have hnegA := (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbA).mpr hn
  have hnegB := correctDomainCode_upward k hφ.neg A B hA hB hAB b hb hnegA
  exact (satisfies_negateFormula membershipLanguageCode_valid hφ.valid hbB).mp hnegB hs

end ZFVP
