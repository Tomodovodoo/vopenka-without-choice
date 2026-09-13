import ZFVP.ModelTheory.InternalHenkinContextExtension

/-! A definable Henkin step decides one coded formula and supplies a fresh
witness whenever the chosen literal is existential. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem henkinLiftCode_valid {n φ k : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hk : k ∈ (ω : V)) :
    kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k) ∈
      formulaSet membershipLanguageCode ∅ (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k)) := by
  apply naturalNumber_induction (fun k ↦
    kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k) ∈
      formulaSet membershipLanguageCode ∅ (kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k)))
    (by definability) ?_ ?_ k hk
  · simpa only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair] using hφ
  · intro k hk ih
    rw [henkinLiftCode_succ _ hk, henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair]
    exact henkinShiftFormula_valid (formulaSet_context membershipLanguageCode_valid ih) ih

theorem henkinLiftCode_pair (n φ : V) {k : V} (hk : k ∈ (ω : V)) :
    henkinLiftCode ⟨n, φ⟩ₖ k =
      ⟨kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k), kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k)⟩ₖ := by
  apply naturalNumber_induction (fun k ↦
    henkinLiftCode ⟨n, φ⟩ₖ k =
      ⟨kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ k), kpair.π₂ (henkinLiftCode ⟨n, φ⟩ₖ k)⟩ₖ)
    (by definability) ?_ ?_ k hk
  · simp only [henkinLiftCode_zero, kpair.π₁_kpair, kpair.π₂_kpair]
  · intro k hk _
    simp only [henkinLiftCode_succ _ hk, henkinShiftCode, kpair.π₁_kpair, kpair.π₂_kpair]

noncomputable def henkinConditions (T : V) : V :=
  {p ∈ formulaFamily membershipLanguageCode ∅ ;
    (0 : V) ∈ kpair.π₁ p ∧ IsConsistentCodedFormula T (kpair.π₁ p) (kpair.π₂ p)}

instance henkinConditions_definable : ℒₛₑₜ-function₁[V] henkinConditions := by
  have he : ℒₛₑₜ-relation[V] (fun A T ↦ ∀ p, p ∈ A ↔
      p ∈ formulaFamily (membershipLanguageCode : V) (∅ : V) ∧
        (0 : V) ∈ kpair.π₁ p ∧ IsConsistentCodedFormula T (kpair.π₁ p) (kpair.π₂ p)) := by
    definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinConditions (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [henkinConditions, mem_sep_iff]

theorem pair_mem_henkinConditions_iff (T n φ : V) :
    ⟨n, φ⟩ₖ ∈ henkinConditions T ↔ (0 : V) ∈ n ∧ IsConsistentCodedFormula T n φ := by
  simp only [henkinConditions, mem_sep_iff, kpair.π₁_kpair, kpair.π₂_kpair]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨(mem_formulaSet_iff _ _ _ _).mp h.2.1, h⟩

theorem henkinConditions_cases {T p : V} (hp : p ∈ henkinConditions T) :
    ∃ n φ, p = ⟨n, φ⟩ₖ ∧ (0 : V) ∈ n ∧ IsConsistentCodedFormula T n φ := by
  obtain ⟨n, _, φ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ (mem_sep_iff.mp hp).1
  exact ⟨n, φ, rfl, (pair_mem_henkinConditions_iff T n φ).mp hp⟩

noncomputable def henkinDecisionLiteral (T n φ ψ : V) : V := by
  classical
  exact if IsConsistentCodedFormula T n (andCode φ ψ) then ψ
    else negateFormula membershipLanguageCode ∅ n ψ

instance henkinDecisionLiteral_definable : ℒₛₑₜ-function₄[V] henkinDecisionLiteral := by
  classical
  have he : ℒₛₑₜ-relation₅[V] (fun y T n φ ψ ↦
      (IsConsistentCodedFormula T n (andCode φ ψ) ∧ y = ψ) ∨
      (¬IsConsistentCodedFormula T n (andCode φ ψ) ∧ y = negateFormula membershipLanguageCode ∅ n ψ)) := by
    definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinDecisionLiteral (v 1) (v 2) (v 3) (v 4) ↔ _
  unfold henkinDecisionLiteral
  split <;> simp_all

theorem henkinDecisionLiteral_valid {T n φ ψ : V}
    (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    henkinDecisionLiteral T n φ ψ ∈ formulaSet membershipLanguageCode ∅ n := by
  classical
  unfold henkinDecisionLiteral
  split
  · exact hψ
  · exact negateFormula_mem membershipLanguageCode_valid hψ

theorem henkinDecisionLiteral_consistent (hω : Schmerl.HasStandardOmega V) {T n φ ψ : V}
    (h : IsConsistentCodedFormula T n φ) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    IsConsistentCodedFormula T n (andCode (henkinDecisionLiteral T n φ ψ) φ) := by
  classical
  have hc : IsConsistentCodedFormula T n (andCode φ (henkinDecisionLiteral T n φ ψ)) := by
    unfold henkinDecisionLiteral
    split
    · assumption
    · exact (h.decide hω hψ).resolve_left ‹_›
  exact hc.conj_swap hω h.1 (henkinDecisionLiteral_valid hψ)

noncomputable def henkinWitnessCode (n φ χ : V) : V := by
  classical
  exact if χ = existsCode (kpair.π₂ χ) then
    ⟨succ n, andCode (kpair.π₂ χ) (henkinShiftFormula n φ)⟩ₖ
  else ⟨n, andCode χ φ⟩ₖ

instance henkinWitnessCode_definable : ℒₛₑₜ-function₃[V] henkinWitnessCode := by
  classical
  have he : ℒₛₑₜ-relation₄[V] (fun y n φ χ ↦
      (χ = existsCode (kpair.π₂ χ) ∧ y = ⟨succ n, andCode (kpair.π₂ χ) (henkinShiftFormula n φ)⟩ₖ) ∨
      (χ ≠ existsCode (kpair.π₂ χ) ∧ y = ⟨n, andCode χ φ⟩ₖ)) := by definability
  apply Language.Definable.of_iff he
  intro v
  change v 0 = henkinWitnessCode (v 1) (v 2) (v 3) ↔ _
  unfold henkinWitnessCode
  split
  · rename_i h
    constructor
    · exact fun he ↦ Or.inl ⟨h, he⟩
    · rintro (⟨_, he⟩ | ⟨hn, _⟩)
      · exact he
      · exact (hn h).elim
  · rename_i h
    constructor
    · exact fun he ↦ Or.inr ⟨h, he⟩
    · rintro (⟨hp, _⟩ | ⟨_, he⟩)
      · exact (h hp).elim
      · exact he

theorem henkinWitnessCode_consistent (hω : Schmerl.HasStandardOmega V) {T n φ χ : V}
    (hzero : (0 : V) ∈ n) (h : IsConsistentCodedFormula T n (andCode χ φ)) :
    henkinWitnessCode n φ χ ∈ henkinConditions T := by
  classical
  have hv := (andCode_mem_iff membershipLanguageCode_valid).mp h.1
  unfold henkinWitnessCode
  split
  · rename_i he
    rw [pair_mem_henkinConditions_iff]
    have hχ := hv.2.1
    rw [he] at hχ
    have hbody := (existsCode_mem_iff membershipLanguageCode_valid).mp hχ
    have hc : IsConsistentCodedFormula T n (andCode (existsCode (kpair.π₂ χ)) φ) := by
      simpa only [← he] using h
    exact ⟨zero_mem_succ_natural hv.1, hc.witness hω hv.1 hbody.2 hv.2.2⟩
  · exact (pair_mem_henkinConditions_iff T n _).mpr ⟨hzero, h⟩

noncomputable def henkinNextCode (T p q : V) : V :=
  let a := henkinLiftCode p (succ (kpair.π₁ q))
  let b := henkinLiftCode q (succ (kpair.π₁ p))
  henkinWitnessCode (kpair.π₁ a) (kpair.π₂ a)
    (henkinDecisionLiteral T (kpair.π₁ a) (kpair.π₂ a) (kpair.π₂ b))

instance henkinNextCode_definable : ℒₛₑₜ-function₃[V] henkinNextCode := by
  change Language.DefinableFunction ℒₛₑₜ (fun v : Fin 3 → V ↦
    henkinWitnessCode (kpair.π₁ (henkinLiftCode (v 1) (succ (kpair.π₁ (v 2)))))
      (kpair.π₂ (henkinLiftCode (v 1) (succ (kpair.π₁ (v 2)))))
      (henkinDecisionLiteral (v 0) (kpair.π₁ (henkinLiftCode (v 1) (succ (kpair.π₁ (v 2)))))
        (kpair.π₂ (henkinLiftCode (v 1) (succ (kpair.π₁ (v 2)))))
        (kpair.π₂ (henkinLiftCode (v 2) (succ (kpair.π₁ (v 1)))))))
  apply Language.DefinableFunction₃.comp (F := henkinWitnessCode)
  · definability
  · definability
  · exact Language.DefinableFunction₄.comp (by definability) (by definability)
      (by definability) (by definability)

theorem henkinNextCode_consistent (hω : Schmerl.HasStandardOmega V) {T p q : V}
    (hp : p ∈ henkinConditions T) (hq : q ∈ formulaFamily (membershipLanguageCode : V) (∅ : V)) :
    henkinNextCode T p q ∈ henkinConditions T := by
  obtain ⟨n, φ, rfl, hzero, hφ⟩ := henkinConditions_cases hp
  obtain ⟨m, hm, ψ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ hq
  have hψ := (mem_formulaSet_iff _ _ _ _).mpr hq
  have hn := hφ.context
  have ha := henkinLiftCode_consistent hω hφ hzero (ω_succ_closed hm)
  have hb := henkinLiftCode_valid hψ (ω_succ_closed hn)
  have he : kpair.π₁ (henkinLiftCode ⟨m, ψ⟩ₖ (succ n)) =
      kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ (succ m)) := by
    rw [henkinLiftCode_context hm (ω_succ_closed hn), henkinLiftCode_context hn (ω_succ_closed hm)]
    have := IsOrdinal.of_mem hn
    have := IsOrdinal.of_mem hm
    rw [ordinalAdd_succ, ordinalAdd_succ, ordinalAdd_comm_natural hm hn]
  rw [he] at hb
  simp only [henkinNextCode, kpair.π₁_kpair]
  exact henkinWitnessCode_consistent hω ha.1 (henkinDecisionLiteral_consistent hω ha.2 hb)

theorem henkinNextCode_context_grows {T p q : V}
    (hp : p ∈ henkinConditions T) (hq : q ∈ formulaFamily (membershipLanguageCode : V) (∅ : V)) :
    kpair.π₁ p ∈ kpair.π₁ (henkinNextCode T p q) := by
  classical
  obtain ⟨n, φ, rfl, _, hφ⟩ := henkinConditions_cases hp
  obtain ⟨m, hm, ψ, rfl⟩ := formulaFamily_context membershipLanguageCode_valid ∅ hq
  have hn := hφ.context
  have : IsOrdinal m := IsOrdinal.of_mem hm
  have hlt : n ∈ kpair.π₁ (henkinLiftCode ⟨n, φ⟩ₖ (succ m)) := by
    rw [henkinLiftCode_context hn (ω_succ_closed hm)]
    have hh := ordinalAdd_mem (α := n) (zero_mem_succ_natural hm)
    simpa only [zero_def, ordinalAdd_zero] using hh
  simp only [henkinNextCode, kpair.π₁_kpair, henkinWitnessCode]
  split
  · simpa only [kpair.π₁_kpair] using mem_succ_iff.mpr (Or.inr hlt)
  · simpa only [kpair.π₁_kpair] using hlt

end ZFVP
