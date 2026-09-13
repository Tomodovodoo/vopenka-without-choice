import ZFVP.SetTheory.ForcingSaturatedName
import ZFVP.SetTheory.DeltaOneAtomicForcing
import ZFVP.SetTheory.DeltaOneForcingNames

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def sigmaOneSaturatedEntryFormula : SetTheorySemisentence 5 :=
  “P R τ Q p. !sigmaOneForcingNameFormula P τ ∧ !(sigmaOneAtomicMembershipFormula true) P R τ Q p”

def piOneSaturatedEntryFormula : SetTheorySemisentence 5 :=
  “P R τ Q p. !piOneForcingNameFormula P τ ∧ !piOneAtomicMembershipFormula P R τ Q p”

theorem sigmaOneSaturatedEntryFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSaturatedEntryFormula :=
  .and (sigmaOneForcingNameFormula_sigmaOne.subst _)
    ((sigmaOneAtomicMembershipFormula_sigmaOne true).subst _)

theorem piOneSaturatedEntryFormula_piOne : IsPiFormula 1 piOneSaturatedEntryFormula :=
  .and (piOneForcingNameFormula_piOne.subst _)
    (piOneAtomicMembershipFormula_piOne.subst _)

def saturatedNameGraphFormula (pos neg : SetTheorySemisentence 5) : SetTheorySemisentence 5 :=
  “N P R U Q. (∀ z ∈ N, ∃ τ ∈ U, ∃ p ∈ P,
    !boundedKpairFormula z τ p ∧ !pos P R τ Q p) ∧
    ∀ τ ∈ U, ∀ p ∈ P, !neg P R τ Q p → !boundedPairMemberFormula N τ p”

theorem saturatedNameGraphFormula_levy {s : LevyPolarity} {k : ℕ}
    {pos neg : SetTheorySemisentence 5}
    (hp : IsLevyFormula s k pos) (hn : IsLevyFormula s.dual k neg) :
    IsLevyFormula s k (saturatedNameGraphFormula pos neg) := by
  cases s <;> exact
  .and (.boundedAll (.bvar 0) (.boundedExs (.bvar 4) (.boundedExs (.bvar 3)
    (.and (.bounded (boundedKpairFormula_bounded.subst _)) (hp.subst _)))))
    (.boundedAll (.bvar 3) (.boundedAll (.bvar 2) (.or (hn.subst _).neg
      (.bounded (boundedPairMemberFormula_bounded.subst _)))))

def sigmaOneSaturatedNameFormula : SetTheorySemisentence 5 :=
  saturatedNameGraphFormula sigmaOneSaturatedEntryFormula piOneSaturatedEntryFormula

def piOneSaturatedNameFormula : SetTheorySemisentence 5 :=
  saturatedNameGraphFormula piOneSaturatedEntryFormula sigmaOneSaturatedEntryFormula

theorem sigmaOneSaturatedNameFormula_sigmaOne : IsSigmaFormula 1 sigmaOneSaturatedNameFormula :=
  saturatedNameGraphFormula_levy sigmaOneSaturatedEntryFormula_sigmaOne piOneSaturatedEntryFormula_piOne

theorem piOneSaturatedNameFormula_piOne : IsPiFormula 1 piOneSaturatedNameFormula :=
  saturatedNameGraphFormula_levy piOneSaturatedEntryFormula_piOne sigmaOneSaturatedEntryFormula_sigmaOne

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_sigmaOneSaturatedEntryFormula (P R τ Q p : V) :
    sigmaOneSaturatedEntryFormula.Evalb ![P, R, τ, Q, p] ↔
      IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q := by
  simp [sigmaOneSaturatedEntryFormula,
    TruthAnswer, Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_piOneSaturatedEntryFormula (P R τ Q p : V) :
    piOneSaturatedEntryFormula.Evalb ![P, R, τ, Q, p] ↔
      IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q := by
  simp [piOneSaturatedEntryFormula,
    Semiformula.eval_substs, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton, Function.comp_def]

theorem eval_saturatedNameGraphFormula (pos neg : SetTheorySemisentence 5) (N P R U Q : V)
    (hp : ∀ τ p : V, pos.Evalb ![P, R, τ, Q, p] ↔ IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q)
    (hn : ∀ τ p : V, neg.Evalb ![P, R, τ, Q, p] ↔ IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q) :
    (saturatedNameGraphFormula pos neg).Evalb ![N, P, R, U, Q] ↔ N = forcingSaturatedName P R U Q := by
  have he : (saturatedNameGraphFormula pos neg).Evalb ![N, P, R, U, Q] ↔
      (∀ z ∈ N, ∃ τ ∈ U, ∃ p ∈ P, z = ⟨τ, p⟩ₖ ∧ IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q) ∧
      ∀ τ ∈ U, ∀ p ∈ P, (IsForcingName P τ ∧ p ∈ atomicMembership P R τ Q) → ⟨τ, p⟩ₖ ∈ N := by
    simp [saturatedNameGraphFormula, hp, hn, Semiformula.eval_substs,
      Matrix.comp_vecCons', Matrix.constant_eq_singleton, Function.comp_def]
  rw [he]
  constructor
  · rintro ⟨hf, hb⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨τ, hτ, p, hp, rfl, hname, hmem⟩ := hf z hz
      exact (pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr ⟨hτ, hp, hname, hmem⟩
    · intro hz
      obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp (forcingSaturatedName_subset P R U Q z hz)
      have h := (pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hz
      exact hb τ hτ p hp h.2.2
  · rintro rfl
    constructor
    · intro z hz
      obtain ⟨τ, hτ, p, hp, rfl⟩ := mem_prod_iff.mp (forcingSaturatedName_subset P R U Q z hz)
      exact ⟨τ, hτ, p, hp, rfl, ((pair_mem_forcingSaturatedName _ _ _ _ _ _).mp hz).2.2⟩
    · intro τ hτ p hp h
      exact (pair_mem_forcingSaturatedName _ _ _ _ _ _).mpr ⟨hτ, hp, h⟩

theorem eval_sigmaOneSaturatedNameFormula (N P R U Q : V) :
    sigmaOneSaturatedNameFormula.Evalb ![N, P, R, U, Q] ↔ N = forcingSaturatedName P R U Q :=
  eval_saturatedNameGraphFormula _ _ _ _ _ _ _
    (fun τ p ↦ eval_sigmaOneSaturatedEntryFormula P R τ Q p)
    (fun τ p ↦ eval_piOneSaturatedEntryFormula P R τ Q p)

theorem eval_piOneSaturatedNameFormula (N P R U Q : V) :
    piOneSaturatedNameFormula.Evalb ![N, P, R, U, Q] ↔ N = forcingSaturatedName P R U Q :=
  eval_saturatedNameGraphFormula _ _ _ _ _ _ _
    (fun τ p ↦ eval_piOneSaturatedEntryFormula P R τ Q p)
    (fun τ p ↦ eval_sigmaOneSaturatedEntryFormula P R τ Q p)

end ZFVP





