import ZFVP.ModelTheory.CodedMembershipEmbedding
import ZFVP.Syntax.DirectMembershipAtoms
import ZFVP.Syntax.MembershipSwap
import ZFVP.SetTheory.InverseFunction

/-! Internal membership isomorphisms preserve all internally finite
formulas, by definable induction over the coded formula family. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem membershipAtomicHolds_isomorphism {A B f n b r args : V}
    (hf : f ∈ B ^ A) (hi : Injective f)
    (hm : ∀ x ∈ A, ∀ y ∈ A, f ‘ x ∈ f ‘ y ↔ x ∈ y)
    (hn : n ∈ (ω : V)) (hb : b ∈ A ^ n)
    (ha : IsAtomicArguments membershipLanguageCode ∅ n r args) :
    AtomicHolds membershipLanguageCode ∅ (membershipStructureCode A) ∅ n b r args ↔
      AtomicHolds membershipLanguageCode ∅ (membershipStructureCode B) ∅ n (compose b f) r args := by
  obtain ⟨hr, i, hi', j, hj, rfl⟩ := (membershipAtomicArguments_iff hn).mp ha
  have heq : (b ‘ i = b ‘ j) ↔ f ‘ (b ‘ i) = f ‘ (b ‘ j) :=
    ⟨congrArg (fun x ↦ f ‘ x), injective_value_eq hf hi
      (function_value_mem hb hi') (function_value_mem hb hj)⟩
  rcases hr with rfl | rfl | rfl
  · rw [membershipAtomic_logicalEquality hn hi' hj,
      membershipAtomic_logicalEquality hn hi' hj,
      value_compose_of_mem_function hb hf hi', value_compose_of_mem_function hb hf hj]
    exact heq
  · rw [membershipAtomic_relationEquality hn hi' hj hb,
      membershipAtomic_relationEquality hn hi' hj (compose_function hb hf),
      value_compose_of_mem_function hb hf hi', value_compose_of_mem_function hb hf hj]
    exact heq
  · rw [membershipAtomic_membership hn hi' hj hb,
      membershipAtomic_membership hn hi' hj (compose_function hb hf),
      value_compose_of_mem_function hb hf hi', value_compose_of_mem_function hb hf hj]
    exact (hm _ (function_value_mem hb hi') _ (function_value_mem hb hj)).symm

theorem codedMembershipEmbedding_of_isomorphism {A B f : V}
    (hA : IsNonempty A) (hf : f ∈ B ^ A) (hi : Injective f) (hr : range f = B)
    (hm : ∀ x ∈ A, ∀ y ∈ A, f ‘ x ∈ f ‘ y ↔ x ∈ y) :
    IsCodedMembershipEmbedding A B f := by
  let := IsFunction.of_mem hf
  have hB : IsNonempty B := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨f ‘ x, function_value_mem hf hx⟩
  refine ⟨membershipStructureCode_valid hA, membershipStructureCode_valid hB,
    by simpa using hf, ?_⟩
  have hall : ∀ n φ, φ ∈ formulaSet membershipLanguageCode ∅ n → ∀ b ∈ A ^ n,
      (Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n φ b ↔
       Satisfies membershipLanguageCode ∅ (membershipStructureCode B) ∅ n φ (compose b f)) := by
    apply formulaSet_induction membershipLanguageCode_valid ∅
      (fun n φ ↦ ∀ b ∈ A ^ n,
        (Satisfies membershipLanguageCode ∅ (membershipStructureCode A) ∅ n φ b ↔
         Satisfies membershipLanguageCode ∅ (membershipStructureCode B) ∅ n φ (compose b f)))
      (by unfold Satisfies; definability)
    · intro n hn
      constructor
      · intro b hb
        rw [satisfies_truth membershipLanguageCode_valid hn,
          satisfies_truth membershipLanguageCode_valid hn]
        exact iff_of_true (by simpa using hb) (by simpa using compose_function hb hf)
      · intro b _
        exact iff_of_false (not_satisfies_falsity membershipLanguageCode_valid hn)
          (not_satisfies_falsity membershipLanguageCode_valid hn)
    · intro n hn r args ha
      constructor
      · intro b hb
        rw [satisfies_atom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_atom membershipLanguageCode_valid hn ha (by simpa using compose_function hb hf)]
        exact membershipAtomicHolds_isomorphism hf hi hm hn hb ha
      · intro b hb
        rw [satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using hb),
          satisfies_negAtom membershipLanguageCode_valid hn ha (by simpa using compose_function hb hf)]
        exact not_congr (membershipAtomicHolds_isomorphism hf hi hm hn hb ha)
    · intro n hn φ ψ hφ hψ ihφ ihψ
      constructor
      · intro b hb
        rw [satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_and membershipLanguageCode_valid hn hφ hψ (by simpa using compose_function hb hf)]
        exact and_congr (ihφ b hb) (ihψ b hb)
      · intro b hb
        rw [satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using hb),
          satisfies_or membershipLanguageCode_valid hn hφ hψ (by simpa using compose_function hb hf)]
        exact or_congr (ihφ b hb) (ihψ b hb)
    · intro n hn φ hφ ih
      have hbody (b : V) (hb : b ∈ A ^ n) (x : V) (hx : x ∈ A) :=
        ih (assignmentPrepend n b x) (assignmentPrepend_mem_function hn hb hx)
      have honto (y : V) (hy : y ∈ B) : ∃ x ∈ A, f ‘ x = y := by
        obtain ⟨x, hxy⟩ := mem_range_iff.mp (hr.symm ▸ hy)
        exact ⟨x, (mem_of_mem_functions hf hxy).1, value_eq_of_kpair_mem hxy⟩
      constructor
      · intro b hb
        rw [satisfies_all membershipLanguageCode_valid hn hφ (by simpa using hb),
          satisfies_all membershipLanguageCode_valid hn hφ (by simpa using compose_function hb hf)]
        simp only [membershipStructureCode_domain]
        constructor
        · intro hs y hy
          obtain ⟨x, hx, rfl⟩ := honto y hy
          have hh := (hbody b hb x hx).mp (hs x hx)
          rwa [compose_assignmentPrepend hn hb hf hx] at hh
        · intro hs x hx
          apply (hbody b hb x hx).mpr
          rw [compose_assignmentPrepend hn hb hf hx]
          exact hs _ (function_value_mem hf hx)
      · intro b hb
        rw [satisfies_exists membershipLanguageCode_valid hn hφ (by simpa using hb),
          satisfies_exists membershipLanguageCode_valid hn hφ (by simpa using compose_function hb hf)]
        simp only [membershipStructureCode_domain]
        constructor
        · rintro ⟨x, hx, hs⟩
          refine ⟨f ‘ x, function_value_mem hf hx, ?_⟩
          have hh := (hbody b hb x hx).mp hs
          rwa [compose_assignmentPrepend hn hb hf hx] at hh
        · rintro ⟨y, hy, hs⟩
          obtain ⟨x, hx, rfl⟩ := honto y hy
          refine ⟨x, hx, (hbody b hb x hx).mpr ?_⟩
          rwa [compose_assignmentPrepend hn hb hf hx]
  intro n _ φ hφ b hb
  exact hall n φ hφ b (by simpa using hb)

end ZFVP
