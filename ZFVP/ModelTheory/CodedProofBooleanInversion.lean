import ZFVP.ModelTheory.StandardOmegaCodedProofs

/-! Boolean inversion for finite coded proofs. These proofs treat each raw
formula code as a formula; exact encoding by external syntax is unnecessary. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem isCodedSequent_empty {n : V} (hn : n ∈ (ω : V)) : IsCodedSequent n (∅ : V) :=
  ⟨hn, internallyFinite_empty, by simp⟩

theorem IsCodedSequent.insert {n Γ φ : V} (hΓ : IsCodedSequent n Γ)
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) : IsCodedSequent n (insert φ Γ) := by
  refine ⟨hΓ.1, internallyFinite_insert hΓ.2.1 φ, fun x hx ↦ ?_⟩
  rcases mem_insert.mp hx with rfl | hx
  · exact hφ
  · exact hΓ.2.2 x hx

theorem isCodedSequent_singleton {n φ : V} (hn : n ∈ (ω : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) : IsCodedSequent n ({φ} : V) := by
  simpa only [SetTheory.insert_empty_eq] using (isCodedSequent_empty hn).insert hφ

namespace StandardCodedProvable

theorem refute_conj_of_left {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n φ}) :
    StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n (andCode φ ψ)} := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hp : StandardCodedProvable T n (insert (negateFormula membershipLanguageCode ∅ n φ)
      (insert (negateFormula membershipLanguageCode ∅ n ψ) (∅ : V))) :=
    h.weaken (((isCodedSequent_empty hn).insert hng).insert hnf) (by intro x hx; simp only [mem_singleton_iff] at hx; simp [hx])
  have hc := hp.disj ((isCodedSequent_empty hn).insert (formulaSet_binary membershipLanguageCode_valid hn hnf hng).2) hnf hng
  rw [negateFormula_and membershipLanguageCode_valid hn hφ hψ]
  simpa only [SetTheory.insert_empty_eq] using hc

theorem refute_conj_of_right {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (h : StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n ψ}) :
    StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n (andCode φ ψ)} := by
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hp : StandardCodedProvable T n (insert (negateFormula membershipLanguageCode ∅ n φ)
      (insert (negateFormula membershipLanguageCode ∅ n ψ) (∅ : V))) :=
    h.weaken (((isCodedSequent_empty hn).insert hng).insert hnf) (by intro x hx; simp only [mem_singleton_iff] at hx; simp [hx])
  have hc := hp.disj ((isCodedSequent_empty hn).insert (formulaSet_binary membershipLanguageCode_valid hn hnf hng).2) hnf hng
  rw [negateFormula_and membershipLanguageCode_valid hn hφ hψ]
  simpa only [SetTheory.insert_empty_eq] using hc

theorem invert_or {T n Γ φ ψ : V} (h : StandardCodedProvable T n (insert (orCode φ ψ) Γ))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓ : IsCodedSequent n Γ) : StandardCodedProvable T n (insert φ (insert ψ Γ)) := by
  let N := negateFormula membershipLanguageCode ∅ n
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hΔ : IsCodedSequent n ({φ, ψ} : V) := (isCodedSequent_singleton hΓ.1 hψ).insert hφ
  have hf : StandardCodedProvable T n (insert (N φ) ({φ, ψ} : V)) :=
    (identity T hΓ.1 hφ).weaken (hΔ.insert hnf) (by intro x hx; simp only [mem_insert, mem_singleton_iff] at hx ⊢; tauto)
  have hg : StandardCodedProvable T n (insert (N ψ) ({φ, ψ} : V)) :=
    (identity T hΓ.1 hψ).weaken (hΔ.insert hng) (by intro x hx; simp only [mem_insert, mem_singleton_iff] at hx ⊢; tauto)
  have hneg : StandardCodedProvable T n (insert (N (orCode φ ψ)) ({φ, ψ} : V)) := by
    rw [show N (orCode φ ψ) = andCode (N φ) (N ψ) from negateFormula_or membershipLanguageCode_valid hΓ.1 hφ hψ]
    exact hf.conj hg (hΔ.insert (formulaSet_binary membershipLanguageCode_valid hΓ.1 hnf hng).1) hnf hng
  have hv : IsCodedSequent n (Γ ∪ ({φ, ψ} : V)) := by
    have he : Γ ∪ ({φ, ψ} : V) = insert φ (insert ψ Γ) := by ext x; simp; tauto
    rw [he]
    exact (hΓ.insert hψ).insert hφ
  have hc := h.cut hneg hv (formulaSet_binary membershipLanguageCode_valid hΓ.1 hφ hψ).2
  have he : Γ ∪ ({φ, ψ} : V) = insert φ (insert ψ Γ) := by ext x; simp; tauto
  rwa [he] at hc

theorem invert_or_singleton {T n φ ψ : V} (h : StandardCodedProvable T n ({orCode φ ψ} : V))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n) :
    StandardCodedProvable T n ({φ, ψ} : V) := by
  have hp : StandardCodedProvable T n (insert (orCode φ ψ) (∅ : V)) := by
    simpa only [SetTheory.insert_empty_eq] using h
  simpa only [SetTheory.insert_empty_eq] using hp.invert_or hφ hψ (isCodedSequent_empty h.valid.1)

theorem invert_and_left {T n Γ φ ψ : V} (h : StandardCodedProvable T n (insert (andCode φ ψ) Γ))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓ : IsCodedSequent n Γ) : StandardCodedProvable T n (insert φ Γ) := by
  let N := negateFormula membershipLanguageCode ∅ n
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hv : IsCodedSequent n (insert (N φ) (insert (N ψ) ({φ} : V))) :=
    ((isCodedSequent_singleton hΓ.1 hφ).insert hng).insert hnf
  have hf : StandardCodedProvable T n (insert (N φ) (insert (N ψ) ({φ} : V))) :=
    (identity T hΓ.1 hφ).weaken hv (by intro x hx; simp only [mem_insert, mem_singleton_iff] at hx ⊢; tauto)
  have hneg : StandardCodedProvable T n (insert (N (andCode φ ψ)) ({φ} : V)) := by
    rw [show N (andCode φ ψ) = orCode (N φ) (N ψ) from negateFormula_and membershipLanguageCode_valid hΓ.1 hφ hψ]
    exact hf.disj ((isCodedSequent_singleton hΓ.1 hφ).insert
      (formulaSet_binary membershipLanguageCode_valid hΓ.1 hnf hng).2) hnf hng
  have he : Γ ∪ ({φ} : V) = insert φ Γ := by ext x; simp; tauto
  have hc := h.cut hneg (he.symm ▸ hΓ.insert hφ) (formulaSet_binary membershipLanguageCode_valid hΓ.1 hφ hψ).1
  rwa [he] at hc

theorem invert_and_right {T n Γ φ ψ : V} (h : StandardCodedProvable T n (insert (andCode φ ψ) Γ))
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hΓ : IsCodedSequent n Γ) : StandardCodedProvable T n (insert ψ Γ) := by
  let N := negateFormula membershipLanguageCode ∅ n
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  have hv : IsCodedSequent n (insert (N φ) (insert (N ψ) ({ψ} : V))) :=
    ((isCodedSequent_singleton hΓ.1 hψ).insert hng).insert hnf
  have hf : StandardCodedProvable T n (insert (N φ) (insert (N ψ) ({ψ} : V))) :=
    (identity T hΓ.1 hψ).weaken hv (by intro x hx; simp only [mem_insert, mem_singleton_iff] at hx ⊢; tauto)
  have hneg : StandardCodedProvable T n (insert (N (andCode φ ψ)) ({ψ} : V)) := by
    rw [show N (andCode φ ψ) = orCode (N φ) (N ψ) from negateFormula_and membershipLanguageCode_valid hΓ.1 hφ hψ]
    exact hf.disj ((isCodedSequent_singleton hΓ.1 hψ).insert
      (formulaSet_binary membershipLanguageCode_valid hΓ.1 hnf hng).2) hnf hng
  have he : Γ ∪ ({ψ} : V) = insert ψ Γ := by ext x; simp; tauto
  have hc := h.cut hneg (he.symm ▸ hΓ.insert hψ) (formulaSet_binary membershipLanguageCode_valid hΓ.1 hφ hψ).1
  rwa [he] at hc

theorem refute_of_refute_conj_both {T n φ ψ : V}
    (hφ : φ ∈ formulaSet membershipLanguageCode ∅ n) (hψ : ψ ∈ formulaSet membershipLanguageCode ∅ n)
    (hp : StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n (andCode φ ψ)})
    (hq : StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n
      (andCode φ (negateFormula membershipLanguageCode ∅ n ψ))}) :
    StandardCodedProvable T n {negateFormula membershipLanguageCode ∅ n φ} := by
  let N := negateFormula membershipLanguageCode ∅ n
  have hn := formulaSet_context membershipLanguageCode_valid hφ
  have hnf := negateFormula_mem membershipLanguageCode_valid hφ
  have hng := negateFormula_mem membershipLanguageCode_valid hψ
  rw [negateFormula_and membershipLanguageCode_valid hn hφ hψ] at hp
  rw [negateFormula_and membershipLanguageCode_valid hn hφ hng,
    negateFormula_involutive membershipLanguageCode_valid hψ] at hq
  have hp' := hp.invert_or_singleton hnf hng
  have hq' := hq.invert_or_singleton hnf hψ
  have hp'' : StandardCodedProvable T n (insert (N ψ) ({N φ} : V)) := by
    have he : ({N φ, N ψ} : V) = insert (N ψ) ({N φ} : V) := by ext x; simp; tauto
    rwa [← he]
  have hq'' : StandardCodedProvable T n (insert ψ ({N φ} : V)) := by
    have he : ({N φ, ψ} : V) = insert ψ ({N φ} : V) := by ext x; simp; tauto
    rwa [← he]
  have hc := hq''.cut hp'' (by simpa using isCodedSequent_singleton hn hnf) hψ
  simpa using hc

end StandardCodedProvable

end ZFVP
