import ZFVP.Syntax.PrimitiveProgramRequirementCharacterization
import ZFVP.Syntax.PrimitiveProgramRequirementsStandard
import ZFVP.Syntax.RawFormulaCoding

/-! Every accepted standard term and atomic argument vector is a canonical typed encoding. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

namespace PrimitiveProgram

theorem listLength_two_cases {xs : ℕ} (hl : listLength.evalArithmetic xs = (2 : ℕ)) :
    ∃ a b : ℕ, xs = Nat.pair a (Nat.pair b 0 + 1) + 1 := by
  rcases listCode_cases xs with rfl | ⟨a, t, rfl⟩
  · simp at hl
  rw [evalArithmetic_listLength_cons] at hl
  rcases listCode_cases t with rfl | ⟨b, rest, rfl⟩
  · simp at hl
  rw [evalArithmetic_listLength_cons] at hl
  have hz : listLength.evalArithmetic rest = 0 := by change _ + 1 + 1 = 2 at hl; omega
  have hr := (evalArithmetic_listLength_eq_zero rest).mp hz
  subst rest
  exact ⟨a, b, by simp only [arithmeticPair_nat]⟩

theorem termRequirement_raw {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hdec : ∀ i : ℕ, allowFree = true → ∃ x : ξ, Encodable.encode x = i) {c n : ℕ}
    (hv : (termRequirement allowFree).evalArithmetic c ≠ 0 ∧
      (termRequirement allowFree).evalArithmetic c ≤ n + 1) :
    ∃ t : Semiterm ℒₛₑₜ ξ n, c = Encodable.encode t := by
  have h := termRequirement_valid_iff allowFree c n
  simp only [arithmeticLE_nat] at h
  rcases h.mp hv with ⟨i, hi, rfl⟩ | ⟨hf, i, rfl⟩
  · exact ⟨.bvar ⟨i, hi⟩, by rw [arithmeticPair_nat]; rfl⟩
  · obtain ⟨x, rfl⟩ := hdec i hf
    exact ⟨.fvar x, by rw [arithmeticPair_nat]; rfl⟩

theorem atomicRequirement_raw {ξ : Type*} [Encodable ξ] (allowFree : Bool)
    (hdec : ∀ i : ℕ, allowFree = true → ∃ x : ξ, Encodable.encode x = i) {c n : ℕ}
    (hv : (atomicRequirement allowFree).evalArithmetic c ≠ 0 ∧
      (atomicRequirement allowFree).evalArithmetic c ≤ n + 1) :
    ∃ (k : ℕ) (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ ξ n),
      c = Nat.pair k (Nat.pair (Encodable.encode r) (Matrix.vecToNat (fun i ↦ Encodable.encode (ts i)))) := by
  obtain ⟨⟨k, rest⟩, rfl⟩ := Nat.pairEquiv.surjective c
  obtain ⟨⟨r, args⟩, rfl⟩ := Nat.pairEquiv.surjective rest
  have h := atomicRequirement_valid_iff allowFree k r args n
  simp only [arithmeticPair_nat, arithmeticLE_nat, OfNat.ofNat, One.one, Zero.zero,
    Arithmetic.natCast_nat] at h
  obtain ⟨rfl, hr, hlen, ha, hb⟩ := h.mp hv
  obtain ⟨a, b, rfl⟩ := listLength_two_cases hlen
  simp only [← arithmeticPair_nat, evalArithmetic_listHead_cons, evalArithmetic_listTail_cons] at ha hb
  obtain ⟨ta, hta⟩ := termRequirement_raw allowFree hdec ha
  obtain ⟨tb, htb⟩ := termRequirement_raw allowFree hdec hb
  have hr' : r = 0 ∨ r = 1 := by change r ≤ (1 : ℕ) at hr; omega
  rcases hr' with rfl | rfl
  · refine ⟨2, Language.Set.Rel.eq, ![ta, tb], ?_⟩
    rw [hta, htb]
    rfl
  · refine ⟨2, Language.Set.Rel.mem, ![ta, tb], ?_⟩
    rw [hta, htb]
    rfl

end PrimitiveProgram
end ZFVP
