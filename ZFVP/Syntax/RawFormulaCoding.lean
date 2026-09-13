import ZFVP.Syntax.MembershipPrimcoding

/-! The standard formula-code relation allows arbitrary payloads for truth and falsity. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {ξ : Type*} [Encodable ξ]

inductive RawFormulaCode : {n : ℕ} → ℕ → Semiformula ℒₛₑₜ ξ n → Prop where
  | rel {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ ξ n) :
      RawFormulaCode (Encodable.encode (Semiformula.rel r ts)) (.rel r ts)
  | nrel {n k : ℕ} (r : Language.Set.Rel k) (ts : Fin k → Semiterm ℒₛₑₜ ξ n) :
      RawFormulaCode (Encodable.encode (Semiformula.nrel r ts)) (.nrel r ts)
  | verum {n : ℕ} (a : ℕ) : RawFormulaCode (n := n) (Nat.pair 2 a + 1) ⊤
  | falsum {n : ℕ} (a : ℕ) : RawFormulaCode (n := n) (Nat.pair 3 a + 1) ⊥
  | and {n a b : ℕ} {φ ψ : Semiformula ℒₛₑₜ ξ n} :
      RawFormulaCode a φ → RawFormulaCode b ψ → RawFormulaCode (Nat.pair 4 (Nat.pair a b) + 1) (φ ⋏ ψ)
  | or {n a b : ℕ} {φ ψ : Semiformula ℒₛₑₜ ξ n} :
      RawFormulaCode a φ → RawFormulaCode b ψ → RawFormulaCode (Nat.pair 5 (Nat.pair a b) + 1) (φ ⋎ ψ)
  | all {n a : ℕ} {φ : Semiformula ℒₛₑₜ ξ (n + 1)} :
      RawFormulaCode a φ → RawFormulaCode (Nat.pair 6 a + 1) (∀¹ φ)
  | exs {n a : ℕ} {φ : Semiformula ℒₛₑₜ ξ (n + 1)} :
      RawFormulaCode a φ → RawFormulaCode (Nat.pair 7 a + 1) (∃¹ φ)

theorem RawFormulaCode.encode {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) : RawFormulaCode (Encodable.encode φ) φ := by
  induction φ with
  | rel r ts => exact .rel r ts
  | nrel r ts => exact .nrel r ts
  | verum => exact .verum 0
  | falsum => exact .falsum 0
  | and φ ψ ihφ ihψ => exact .and ihφ ihψ
  | or φ ψ ihφ ihψ => exact .or ihφ ihψ
  | all φ ih => exact .all ih
  | exs φ ih => exact .exs ih

theorem RawFormulaCode.ofNat {n c : ℕ} {φ : Semiformula ℒₛₑₜ ξ n} (h : RawFormulaCode c φ) :
    Semiformula.ofNat n c = some φ := by
  induction h with
  | rel r ts => exact Semiformula.ofNat_toNat (Semiformula.rel r ts)
  | nrel r ts => exact Semiformula.ofNat_toNat (Semiformula.nrel r ts)
  | verum a => simp [Semiformula.ofNat]
  | falsum a => simp [Semiformula.ofNat]
  | and ha hb iha ihb => simp [Semiformula.ofNat, iha, ihb]
  | or ha hb iha ihb => simp [Semiformula.ofNat, iha, ihb]
  | all ha ih => simp [Semiformula.ofNat, ih]
  | exs ha ih => simp [Semiformula.ofNat, ih]

theorem RawFormulaCode.unique {n c : ℕ} {φ ψ : Semiformula ℒₛₑₜ ξ n}
    (hφ : RawFormulaCode c φ) (hψ : RawFormulaCode c ψ) : φ = ψ :=
  Option.some.inj (hφ.ofNat.symm.trans hψ.ofNat)

end ZFVP
