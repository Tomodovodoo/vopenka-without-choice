import ZFVP.ModelTheory.SymmetricDCCountableCandidates
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.SetTheory.SymmetricSystemDictionary
import ZFVP.SetTheory.ElementaryForcing

/-! The local candidate laws are first-order ZF statements. Their countable-model proofs
therefore transfer to every ground, while the subsequent DC construction stays unchanged. -/
namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def symmetricDCCandidateLawFormula : SetTheorySemisentence 7 :=
  f“P R o Γ F A p. !forcingPosetFormula P R ∧ !forcingTopFormula P R o ∧
    !symmetricGroupFormula P R Γ ∧ !symmetricNormalFilterFormula P Γ F ∧
    !hereditarilySymmetricNameFormula P Γ F A ∧ p ∈ P ∧
    !(symmetricForcingTranslation boundedNonemptyFormula) P R Γ F p (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) A) → ∃ r ∈ P, ∃ σ ∈ !domain.dfn A, !kpair.dfn r p ∈ R ∧ !(symmetricForcingTranslation symmetricDCMemberFormula) P R Γ F r (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) A) σ)”

def symmetricDCSerialLawFormula : SetTheorySemisentence 9 :=
  f“P R o Γ F A B p σ. !forcingPosetFormula P R ∧ !forcingTopFormula P R o ∧
    !symmetricGroupFormula P R Γ ∧ !symmetricNormalFilterFormula P Γ F ∧
    !hereditarilySymmetricNameFormula P Γ F A ∧ !hereditarilySymmetricNameFormula P Γ F B ∧
    p ∈ P ∧ σ ∈ !domain.dfn A ∧ !(symmetricForcingTranslation serialFormula) P R Γ F p (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) B) A) ∧ !(symmetricForcingTranslation symmetricDCMemberFormula) P R Γ F p (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) A) σ) →
    ∃ r ∈ P, ∃ ν ∈ !domain.dfn A, !kpair.dfn r p ∈ R ∧ !(symmetricForcingTranslation symmetricDCMemberFormula) P R Γ F r (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) A) ν) ∧ !(symmetricForcingTranslation dependentChoiceNextFormula) P R Γ F r (!assignmentPrependFormula (!(numeralFormula 3)) (!assignmentPrependFormula (!(numeralFormula 2)) (!assignmentPrependFormula (!(numeralFormula 1)) (!assignmentPrependFormula (!(numeralFormula 0)) (!isEmpty) B) A) ν) σ)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

private theorem symmetricDC_forall_eq3 {α : Type*} (a₀ b₀ c₀ : α) (R : α → α → α → Prop) :
    (∀ a b c, a = a₀ → b = b₀ → c = c₀ → R a b c) ↔ R a₀ b₀ c₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ rfl rfl rfl
  · rintro h a b c rfl rfl rfl; exact h
private theorem symmetricDC_forall_eq6 {α : Type*} (a₀ b₀ c₀ d₀ e₀ f₀ : α)
    (R : α → α → α → α → α → α → Prop) :
    (∀ a b c d e f, a = a₀ → b = b₀ → c = c₀ → d = d₀ → e = e₀ → f = f₀ → R a b c d e f) ↔
      R a₀ b₀ c₀ d₀ e₀ f₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ d₀ e₀ f₀ rfl rfl rfl rfl rfl rfl
  · rintro h a b c d e f rfl rfl rfl rfl rfl rfl; exact h
private theorem symmetricDC_forall_eq4 {α : Type*} (a₀ b₀ c₀ d₀ : α) (R : α → α → α → α → Prop) :
    (∀ a b c d, a = a₀ → b = b₀ → c = c₀ → d = d₀ → R a b c d) ↔ R a₀ b₀ c₀ d₀ := by
  constructor
  · intro h; exact h a₀ b₀ c₀ d₀ rfl rfl rfl rfl
  · rintro h a b c d rfl rfl rfl rfl; exact h
attribute [local simp] symmetricDC_forall_eq3 symmetricDC_forall_eq4 symmetricDC_forall_eq6

theorem eval_symmetricDCCandidateLawFormula (v : Fin 7 → V) :
    symmetricDCCandidateLawFormula.Evalb v ↔
      (IsForcingPoset (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingAutomorphismGroup (v 0) (v 1) (v 3) → IsNormalSubgroupFilter (v 0) (v 3) (v 4) →
      IsHereditarilySymmetricName (v 0) (v 3) (v 4) (v 5) → v 6 ∈ v 0 →
      v 6 ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) boundedNonemptyFormula (standardTuple ![v 5]) →
      ∃ r ∈ v 0, ∃ σ ∈ domain (v 5), ⟨r, v 6⟩ₖ ∈ v 1 ∧
        r ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) symmetricDCMemberFormula (standardTuple ![σ, v 5])) := by
  simp [symmetricDCCandidateLawFormula, standardTuple, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]

theorem eval_symmetricDCSerialLawFormula (v : Fin 9 → V) :
    symmetricDCSerialLawFormula.Evalb v ↔
      (IsForcingPoset (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingAutomorphismGroup (v 0) (v 1) (v 3) → IsNormalSubgroupFilter (v 0) (v 3) (v 4) →
      IsHereditarilySymmetricName (v 0) (v 3) (v 4) (v 5) →
      IsHereditarilySymmetricName (v 0) (v 3) (v 4) (v 6) → v 7 ∈ v 0 → v 8 ∈ domain (v 5) →
      v 7 ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) serialFormula (standardTuple ![v 5, v 6]) →
      v 7 ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) symmetricDCMemberFormula (standardTuple ![v 8, v 5]) →
      ∃ r ∈ v 0, ∃ ν ∈ domain (v 5), ⟨r, v 7⟩ₖ ∈ v 1 ∧
        r ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) symmetricDCMemberFormula (standardTuple ![ν, v 5]) ∧
        r ∈ symmetricForcingFormula (v 0) (v 1) (v 3) (v 4) dependentChoiceNextFormula
          (standardTuple ![v 8, ν, v 5, v 6])) := by
  simp [symmetricDCSerialLawFormula, standardTuple, Semiformula.eval_nestFormulae,
    Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]

namespace SymmetricContext
variable (S : SymmetricContext V)

theorem chainCandidates_nonempty (τA : S.Name) {p q : V}
    (hne : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F boundedNonemptyFormula (standardTuple ![τA.val]))
    (hq : q ∈ S.P) (hqp : ⟨q, p⟩ₖ ∈ S.R) : IsNonempty (S.chainCandidates τA.val q) := by
  have hall := eval_of_countable_zf symmetricDCCandidateLawFormula (by
    intro W _ _ _ _ v
    apply (eval_symmetricDCCandidateLawFormula v).mpr
    intro hpos ht hΓ hF hA hp hne
    obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric hpos.1 ht.1
    let T : SymmetricContext W := ⟨⟨v 0, v 1, v 2, G, hpos.1, ht, hG⟩, v 3, v 4, hpos, hΓ, hF⟩
    obtain ⟨z, hz⟩ := T.chainCandidates_nonempty_countable ⟨v 5, hA⟩ hne hp (hpos.1.2.1 _ hp)
    obtain ⟨r, hr, σ, hσ, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hz).1
    have hc := (T.pair_mem_chainCandidates _ _ _ _).mp hz
    exact ⟨r, hr, σ, hσ, hc.2.2⟩) ![S.P, S.R, S.one, S.Γ, S.F, τA.val, q]
  have hqne := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 p hne q hq hqp
  obtain ⟨r, hr, σ, hσ, hrq, hf⟩ := (eval_symmetricDCCandidateLawFormula _).mp hall
    S.poset S.top S.group S.normal τA.property hq hqne
  exact ⟨⟨r, σ⟩ₖ, (S.pair_mem_chainCandidates _ _ _ _).mpr ⟨hr, hσ, hrq, hf⟩⟩

theorem chainRelation_serial (τA τB : S.Name) {p q : V}
    (hser : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F serialFormula (standardTuple ![τA.val, τB.val]))
    (hq : q ∈ S.P) (hqp : ⟨q, p⟩ₖ ∈ S.R) :
    ∀ z ∈ S.chainCandidates τA.val q, ∃ w ∈ S.chainCandidates τA.val q,
      ⟨z, w⟩ₖ ∈ S.chainRelation τA.val τB.val q := by
  intro z hz
  obtain ⟨hr, hσ, hrq, hmem⟩ := S.mem_chainCandidates hz
  have hall := eval_of_countable_zf symmetricDCSerialLawFormula (by
    intro W _ _ _ _ v
    apply (eval_symmetricDCSerialLawFormula v).mpr
    intro hpos ht hΓ hF hA hB hp hσ hser hm
    obtain ⟨G, hG, _⟩ := exists_externalForcingGeneric hpos.1 ht.1
    let T : SymmetricContext W := ⟨⟨v 0, v 1, v 2, G, hpos.1, ht, hG⟩, v 3, v 4, hpos, hΓ, hF⟩
    have hz : ⟨v 7, v 8⟩ₖ ∈ T.chainCandidates (v 5) (v 7) :=
      (T.pair_mem_chainCandidates _ _ _ _).mpr ⟨hp, hσ, hpos.1.2.1 _ hp, hm⟩
    obtain ⟨w, hw, hrel⟩ := T.chainRelation_serial_countable ⟨v 5, hA⟩ ⟨v 6, hB⟩ hser hp
      (hpos.1.2.1 _ hp) _ hz
    obtain ⟨r, hr, ν, hν, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hw).1
    have hc := (T.pair_mem_chainCandidates _ _ _ _).mp hw
    have hn := ((T.pair_mem_chainRelation _ _ _ _ _).mp hrel).2.2.2
    exact ⟨r, hr, ν, hν, hc.2.2.1, hc.2.2.2, by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hn⟩)
      ![S.P, S.R, S.one, S.Γ, S.F, τA.val, τB.val, kpair.π₁ z, kpair.π₂ z]
  have hpP := (symmetricForcingFormula_regular S.order _ _ _ _).1 p hser
  have hrp := S.order.2.2 _ hr q hq p hpP hrq hqp
  have hrser := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 p hser _ hr hrp
  obtain ⟨s, hs, ν, hν, hsr, hνmem, hnext⟩ := (eval_symmetricDCSerialLawFormula _).mp hall
    S.poset S.top S.group S.normal τA.property τB.property hr hσ hrser hmem
  have hw : ⟨s, ν⟩ₖ ∈ S.chainCandidates τA.val q :=
    (S.pair_mem_chainCandidates _ _ _ _).mpr ⟨hs, hν, S.order.2.2 s hs _ hr q hq hsr hrq, hνmem⟩
  exact ⟨⟨s, ν⟩ₖ, hw, (S.pair_mem_chainRelation _ _ _ _ _).mpr ⟨hz, hw,
    by simpa using hsr,
    by simpa using hnext⟩⟩

end SymmetricContext
end ZFVP
