import ZFVP.Syntax.NaturalLKRulePrimrec

/-! Finite LK certificates with no forward references or circular premises. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev LKCertificateData := List (Sequent ℒₛₑₜ × LKRuleWitness)

def LKCertificate : LKCertificateData → Prop
  | [] => True
  | (C, w) :: p => LKRuleCheck (p.map Prod.fst) C w ∧ LKCertificate p

theorem LKCertificate.sound {p : LKCertificateData} (hp : LKCertificate p) :
    ∀ C ∈ p.map Prod.fst, Nonempty (Derivation C) := by
  induction p with
  | nil => simp
  | cons row p ih =>
    rcases row with ⟨C, w⟩
    intro Γ hΓ
    simp only [List.map_cons, List.mem_cons] at hΓ
    rcases hΓ with rfl | hΓ
    · exact hp.1.sound (ih hp.2)
    · exact ih hp.2 Γ hΓ

theorem LKCertificate.append {p q : LKCertificateData}
    (hp : LKCertificate p) (hq : LKCertificate q) : LKCertificate (p ++ q) := by
  induction p with
  | nil => exact hq
  | cons row p ih =>
    rcases row with ⟨C, w⟩
    exact ⟨hp.1.mono (by simp), ih hp.2⟩

def lkCertificateRun (p : LKCertificateData) : List (Sequent ℒₛₑₜ) × Bool :=
  p.foldr (fun row st ↦ (row.1 :: st.1, decide (LKRuleCheck st.1 row.1 row.2 ∧ st.2 = true))) ([], true)

theorem lkCertificateRun_fst (p : LKCertificateData) : (lkCertificateRun p).1 = p.map Prod.fst := by
  induction p with
  | nil => rfl
  | cons row p ih => exact congrArg (List.cons row.1) ih

theorem lkCertificateRun_iff (p : LKCertificateData) : (lkCertificateRun p).2 = true ↔ LKCertificate p := by
  induction p with
  | nil => simp [lkCertificateRun, LKCertificate]
  | cons row p ih =>
    rcases row with ⟨C, w⟩
    simp only [lkCertificateRun, List.foldr_cons, decide_eq_true_eq]
    change (LKRuleCheck (lkCertificateRun p).1 C w ∧ (lkCertificateRun p).2 = true) ↔ _
    rw [lkCertificateRun_fst, ih]
    rfl

instance (p : LKCertificateData) : Decidable (LKCertificate p) :=
  decidable_of_iff ((lkCertificateRun p).2 = true) (lkCertificateRun_iff p)

theorem lkCertificateRun_primrec : Primrec lkCertificateRun := by
  open Primrec in
  have hstep : Primrec (fun p : (Sequent ℒₛₑₜ × LKRuleWitness) × (List (Sequent ℒₛₑₜ) × Bool) ↦
      (p.1.1 :: p.2.1, decide (LKRuleCheck p.2.1 p.1.1 p.1.2 ∧ p.2.2 = true))) := by
    have hC := fst.comp (fst (α := Sequent ℒₛₑₜ × LKRuleWitness) (β := List (Sequent ℒₛₑₜ) × Bool))
    have hS : Primrec (fun p : (Sequent ℒₛₑₜ × LKRuleWitness) × (List (Sequent ℒₛₑₜ) × Bool) ↦ p.2.1) := fst.comp snd
    have hcheck := lkRuleCheck_primrec.comp (Primrec₂.pair.comp hS
      (Primrec₂.pair.comp hC (snd.comp fst)))
    exact Primrec₂.pair.comp (list_cons.comp hC hS)
      (hcheck.and (Primrec.eq.comp (snd.comp snd) (const true))).decide
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([], true))
    (hstep.comp Primrec.snd).to₂).of_eq (fun _ ↦ rfl)

theorem lkCertificate_primrec : PrimrecPred LKCertificate :=
  (Primrec.eq.comp (Primrec.snd.comp lkCertificateRun_primrec) (Primrec.const true)).of_eq lkCertificateRun_iff

def LKCertified (C : Sequent ℒₛₑₜ) : Prop :=
  ∃ p, LKCertificate p ∧ C ∈ p.map Prod.fst

theorem LKCertified.sound {C : Sequent ℒₛₑₜ} (h : LKCertified C) : Nonempty (Derivation C) := by
  obtain ⟨p, hp, hC⟩ := h
  exact hp.sound C hC

theorem LKCertified.of_rule {p : LKCertificateData} (hp : LKCertificate p) {C w}
    (h : LKRuleCheck (p.map Prod.fst) C w) : LKCertified C :=
  ⟨(C, w) :: p, ⟨h, hp⟩, by simp⟩

end ZFVP
