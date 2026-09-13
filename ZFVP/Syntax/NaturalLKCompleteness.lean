import ZFVP.Syntax.NaturalLKCertificate

/-! The finite certificate checker accepts exactly the derivable LK sequents. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

theorem LKCertified.identity (φ : SetTheoryProposition) : LKCertified [φ, ∼φ] :=
  LKCertified.of_rule (p := []) trivial (w := ⟨0, φ, ⊤, ⊤, 0, [], []⟩) rfl

theorem LKCertified.cut {φ : SetTheoryProposition} {Γ Δ : Sequent ℒₛₑₜ}
    (hp : LKCertified (φ :: Γ)) (hn : LKCertified (∼φ :: Δ)) : LKCertified (Γ ++ Δ) := by
  obtain ⟨p, hp, hpm⟩ := hp
  obtain ⟨q, hq, hqm⟩ := hn
  apply LKCertified.of_rule (hp.append hq) (w := ⟨1, φ, ⊤, ⊤, 0, Γ, Δ⟩)
  exact ⟨by simp [hpm], by simp [hqm], rfl⟩

theorem LKCertified.contraction {Γ Δ : Sequent ℒₛₑₜ}
    (h : LKCertified Δ) (hΔ : Δ ⊆ Γ) : LKCertified Γ := by
  obtain ⟨p, hp, hpm⟩ := h
  exact LKCertified.of_rule hp (w := ⟨2, ⊤, ⊤, ⊤, 0, [], Δ⟩) ⟨hpm, hΔ⟩

theorem LKCertified.verum : LKCertified ([⊤] : Sequent ℒₛₑₜ) :=
  LKCertified.of_rule (p := []) trivial (w := ⟨3, ⊤, ⊤, ⊤, 0, [], []⟩) rfl

theorem LKCertified.or {φ ψ : SetTheoryProposition} {Γ : Sequent ℒₛₑₜ}
    (h : LKCertified (φ :: ψ :: Γ)) : LKCertified ((φ ⋎ ψ) :: Γ) := by
  obtain ⟨p, hp, hpm⟩ := h
  exact LKCertified.of_rule hp (w := ⟨4, φ, ψ, ⊤, 0, Γ, []⟩) ⟨hpm, rfl⟩

theorem LKCertified.and {φ ψ : SetTheoryProposition} {Γ : Sequent ℒₛₑₜ}
    (hp : LKCertified (φ :: Γ)) (hq : LKCertified (ψ :: Γ)) : LKCertified ((φ ⋏ ψ) :: Γ) := by
  obtain ⟨p, hp, hpm⟩ := hp
  obtain ⟨q, hq, hqm⟩ := hq
  apply LKCertified.of_rule (hp.append hq) (w := ⟨5, φ, ψ, ⊤, 0, Γ, []⟩)
  exact ⟨by simp [hpm], by simp [hqm], rfl⟩

theorem LKCertified.all {φ : Semiproposition ℒₛₑₜ 1} {Γ : Sequent ℒₛₑₜ}
    (h : LKCertified (φ.free :: Γ.map Semiformula.shift)) : LKCertified ((∀¹ φ) :: Γ) := by
  obtain ⟨p, hp, hpm⟩ := h
  exact LKCertified.of_rule hp (w := ⟨6, ⊤, ⊤, φ, 0, Γ, []⟩) ⟨hpm, rfl⟩

theorem LKCertified.exs {φ : Semiproposition ℒₛₑₜ 1} {Γ : Sequent ℒₛₑₜ}
    {t : SyntacticTerm ℒₛₑₜ} (h : LKCertified (φ/[t] :: Γ)) : LKCertified ((∃¹ φ) :: Γ) := by
  cases t with
  | bvar i => exact i.elim0
  | func f _ => exact Empty.elim f
  | fvar k =>
    obtain ⟨p, hp, hpm⟩ := h
    exact LKCertified.of_rule hp (w := ⟨7, ⊤, ⊤, φ, k, Γ, []⟩) ⟨hpm, rfl⟩

theorem lkCertified_of_derivation {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) : LKCertified Γ := by
  induction d with
  | identity r v => exact LKCertified.identity (.rel r v)
  | cut _ _ ihp ihn => exact ihp.cut ihn
  | contraction _ h ih => exact ih.contraction h
  | verum => exact LKCertified.verum
  | or _ ih => exact ih.or
  | and _ _ ihp ihq => exact ihp.and ihq
  | all _ ih => exact ih.all
  | exs _ ih => exact ih.exs

theorem lkCertified_iff (Γ : Sequent ℒₛₑₜ) : LKCertified Γ ↔ Nonempty (Derivation Γ) :=
  ⟨LKCertified.sound, fun ⟨d⟩ ↦ lkCertified_of_derivation d⟩

def LKProofCertificate (Γ : Sequent ℒₛₑₜ) (p : LKCertificateData) : Prop :=
  LKCertificate p ∧ Γ ∈ p.map Prod.fst

theorem lkProofCertificate_primrec :
    PrimrecPred (fun p : Sequent ℒₛₑₜ × LKCertificateData ↦ LKProofCertificate p.1 p.2) := by
  have hm : Primrec (fun p : Sequent ℒₛₑₜ × LKCertificateData ↦ p.2.map Prod.fst) := Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd).to₂
  exact (lkCertificate_primrec.comp Primrec.snd).and (primrec_list_mem.comp Primrec.fst hm)

theorem lkDerivable_re : REPred (fun Γ : Sequent ℒₛₑₜ ↦ Nonempty (Derivation Γ)) :=
  lkProofCertificate_primrec.computablePred.to_re.projection.of_eq lkCertified_iff

end ZFVP
