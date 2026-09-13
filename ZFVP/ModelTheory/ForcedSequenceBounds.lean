import ZFVP.ModelTheory.ForcingModelSequences
import ZFVP.SetTheory.TwoStepForcing
import ZFVP.SetTheory.ForcingClosure

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def forcingClosedAtFormula : SetTheorySemisentence 3 :=
  f“P R α. ∀ s, (s ∈ !function.dfn P α ∧ ∀ i ∈ α, ∀ j ∈ i,
    !kpair.dfn (!value.dfn s i) (!value.dfn s j) ∈ R) →
    ∃ p ∈ P, ∀ i ∈ α, !kpair.dfn p (!value.dfn s i) ∈ R”

def sequenceBoundFormula : SetTheorySemisentence 3 :=
  f“R s p. ∀ i ∈ !domain.dfn s, !kpair.dfn p (!value.dfn s i) ∈ R”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance forcingClosedAtFormula_defined :
    ℒₛₑₜ-relation₃[V] IsForcingClosedAt via forcingClosedAtFormula :=
  ⟨fun v ↦ by simp [forcingClosedAtFormula, IsForcingClosedAt, IsForcingDescending]⟩

instance sequenceBoundFormula_defined :
    ℒₛₑₜ-relation₃[V] (fun R s p ↦ ∀ i ∈ domain s, ⟨p, s ‘ i⟩ₖ ∈ R)
      via sequenceBoundFormula :=
  ⟨fun v ↦ by simp [sequenceBoundFormula]⟩

theorem forced_sequence_bound_coordinate_countable [Countable V] {P R one p s : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (S τ : ForcingName P) (hs : IsNameSequence P s) (hp : p ∈ P)
    (hbound : p ∈ forcingFormula P R sequenceBoundFormula
      (standardTuple ![S.val, sequenceName one s, τ.val])) {i : V} (hi : i ∈ domain s) :
    p ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, τ.val, s ‘ i]) := by
  let σ : ForcingName P := ⟨s ‘ i, hs i hi⟩
  let sn : ForcingName P := ⟨sequenceName one s, sequenceName_isName htop.1 hs⟩
  apply forcingFormula_of_all_generics hR htop hp boundedPairMemberFormula ![S, τ, σ]
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hb : ∀ j ∈ domain (A.sequenceValue s hs),
      ⟨A.ofName τ, (A.sequenceValue s hs) ‘ j⟩ₖ ∈ A.ofName S :=
    (Defined.eval_iff _).mp ((A.formula_truth sequenceBoundFormula ![S, sn, τ]).mpr ⟨p, hpG, hbound⟩)
  have hiA : A.check i ∈ domain (A.sequenceValue s hs) := by
    rw [A.sequenceValue_domain]
    exact (A.check_mem_iff _ _).mpr hi
  have hb' := hb (A.check i) hiA
  rw [A.sequenceValue_value s hs hi] at hb'
  exact (Defined.eval_iff _).mpr hb'

theorem forced_sequence_lowerBound_of_generics_countable [Countable V] {P R one p s : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (Q S : ForcingName P) (hs : IsNameSequence P s) (hp : p ∈ P)
    (hex : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      ∃ x ∈ A.ofName Q, ∀ i ∈ A.check (domain s),
        ⟨x, (A.sequenceValue s hs) ‘ i⟩ₖ ∈ A.ofName S) :
    ∃ r ∈ P, ∃ τ ∈ domain Q.val, ⟨r, p⟩ₖ ∈ R ∧
      r ∈ atomicMembership P R τ Q.val ∧
      ∀ i ∈ domain s, r ∈ forcingFormula P R boundedPairMemberFormula
        (standardTuple ![S.val, τ, s ‘ i]) := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let sn : ForcingName P := ⟨sequenceName one s, sequenceName_isName htop.1 hs⟩
  obtain ⟨x, hx, hb⟩ := hex G hG hpG
  obtain ⟨τ, q, hqG, hτq, rfl⟩ := (A.mem_ofName_iff Q x).mp hx
  have he : sequenceBoundFormula.Evalb (fun i ↦ A.ofName (![S, sn, τ] i)) := by
    apply (Defined.eval_iff _).mpr
    change ∀ i ∈ domain (A.sequenceValue s hs), ⟨A.ofName τ, (A.sequenceValue s hs) ‘ i⟩ₖ ∈ A.ofName S
    rwa [A.sequenceValue_domain]
  obtain ⟨u, huG, hu⟩ := (A.formula_truth sequenceBoundFormula ![S, sn, τ]).mp he
  obtain ⟨v, hvG, hvp, hvq⟩ := hG.1.2.2.2 p hpG q hqG
  obtain ⟨r, hrG, hrv, hru⟩ := hG.1.2.2.2 v hvG u huG
  have hr := hG.1.1 r hrG
  have hv := hG.1.1 v hvG
  have hbound : r ∈ forcingFormula P R sequenceBoundFormula
      (standardTuple ![S.val, sequenceName one s, τ.val]) :=
    (forcingFormula_regular hR sequenceBoundFormula _).2.1 u hu r hr hru
  exact ⟨r, hr, τ.val, mem_domain_of_kpair_mem hτq,
    hR.2.2 r hr v hv p hp hrv hvp,
    atomicMembership_mono hR (atomicMembership_of_pair hR (hG.1.1 q hqG) hτq) hr
      (hR.2.2 r hr v hv q (hG.1.1 q hqG) hrv hvq),
    fun i hi ↦ forced_sequence_bound_coordinate_countable hR htop S τ hs hr hbound hi⟩

theorem forced_sequence_lowerBound_countable [Countable V] {P R one p s : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (Q S : ForcingName P) (hs : IsNameSequence P s) (hp : p ∈ P)
    (hclosed : p ∈ forcingFormula P R forcingClosedAtFormula
      (standardTuple ![Q.val, S.val, checkName one (domain s)]))
    (hdesc : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G), p ∈ G →
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      IsForcingDescending (A.ofName Q) (A.ofName S) (A.check (domain s)) (A.sequenceValue s hs)) :
    ∃ r ∈ P, ∃ τ ∈ domain Q.val, ⟨r, p⟩ₖ ∈ R ∧
      r ∈ atomicMembership P R τ Q.val ∧
      ∀ i ∈ domain s, r ∈ forcingFormula P R boundedPairMemberFormula
        (standardTuple ![S.val, τ, s ‘ i]) := by
  apply forced_sequence_lowerBound_of_generics_countable hR htop Q S hs hp
  intro G hG hpG
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let c : ForcingName P := ⟨checkName one (domain s), checkName_isName htop.1 _⟩
  have hc : IsForcingClosedAt (A.ofName Q) (A.ofName S) (A.check (domain s)) :=
    (Defined.eval_iff _).mp ((A.formula_truth forcingClosedAtFormula ![Q, S, c]).mpr ⟨p, hpG, hclosed⟩)
  exact hc (A.sequenceValue s hs) (hdesc G hG hpG)

end ZFVP

