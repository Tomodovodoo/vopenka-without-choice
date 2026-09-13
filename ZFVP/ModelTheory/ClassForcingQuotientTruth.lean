import ZFVP.ModelTheory.ClassForcingQuotient

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace ClassForcingQuotient

theorem formula_truth (P R : V) (G : Set V) (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G)
    (N : V → Prop) (hN : ℒₛₑₜ-predicate N) (hnames : ∀ x, N x → IsForcingName P x) {n : ℕ} (φ : SetTheorySemisentence n)
    (v : Fin n → {x : V // N x}) :
    φ.Evalb (assignment P R G hR hG.1 N hnames v) ↔
      GenericMeets G (classForcingFormula P R N hN φ (standardTuple (fun i ↦ (v i).val))) := by
  unfold IsExternalForcingGeneric at hG
  induction φ with
  | verum =>
    change True ↔ GenericMeets G P
    constructor
    · intro _
      obtain ⟨p, hpG⟩ := hG.1.2.1
      exact ⟨p, hpG, hG.1.1 p hpG⟩
    · intro _
      trivial
  | falsum =>
    change False ↔ GenericMeets G ∅
    simp [GenericMeets]
  | rel r ts => exact atomic_truth P R G hR hG.1 N hnames r ts v
  | nrel r ts =>
    rw [classForcingFormula_nrel, genericMeets_negation hR hG
      (forcingAtomic_regular hR r ts _).1 (forcingAtomic_regular hR r ts _).2.1]
    exact not_congr (atomic_truth P R G hR hG.1 N hnames r ts v)
  | and φ ψ ihφ ihψ =>
    rw [classForcingFormula_and, genericMeets_inter hG.1
      (classForcingFormula_regular N hN hR φ _).2.1 (classForcingFormula_regular N hN hR ψ _).2.1]
    exact and_congr (ihφ v) (ihψ v)
  | or φ ψ ihφ ihψ =>
    have hAP : classForcingFormula P R N hN φ (standardTuple (fun i ↦ (v i).val)) ∪
        classForcingFormula P R N hN ψ (standardTuple (fun i ↦ (v i).val)) ⊆ P := by
      intro p hp
      rcases mem_union_iff.mp hp with hφ | hψ
      · exact (classForcingFormula_regular N hN hR φ _).1 p hφ
      · exact (classForcingFormula_regular N hN hR ψ _).1 p hψ
    have hd : IsForcingDownwardClosed P R (classForcingFormula P R N hN φ (standardTuple (fun i ↦ (v i).val)) ∪
        classForcingFormula P R N hN ψ (standardTuple (fun i ↦ (v i).val))) := by
      intro p hp q hq hqp
      rcases mem_union_iff.mp hp with hφ | hψ
      · exact mem_union_iff.mpr (Or.inl ((classForcingFormula_regular N hN hR φ _).2.1 p hφ q hq hqp))
      · exact mem_union_iff.mpr (Or.inr ((classForcingFormula_regular N hN hR ψ _).2.1 p hψ q hq hqp))
    rw [classForcingFormula_or, genericMeets_closure hR hG hAP hd, genericMeets_union]
    exact or_congr (ihφ v) (ihψ v)
  | @all n φ ih =>
    change (∀ q : ClassForcingQuotient P R G hR hG.1 N hnames,
      φ.Evalb (q :> assignment P R G hR hG.1 N hnames v)) ↔ _
    rw [classForcingFormula_all, genericMeets_classIntersection hR hG
      N hN _ (by definability)
      (fun x _ ↦ classForcingFormula_regular N hN hR φ _)]
    constructor
    · intro hall x hx
      let σ : {x : V // N x} := ⟨x, hx⟩
      have hv := (ih (σ :> v)).mp (by
        rw [assignment_cons]
        exact hall (ofName P R G hR hG.1 N hnames σ))
      simpa only [nameTuple_cons] using hv
    · intro hall q
      obtain ⟨σ, rfl⟩ := ofName_surjective P R G hR hG.1 N hnames q
      have hv := (ih (σ :> v)).mpr (by
        simpa only [nameTuple_cons] using hall σ.val σ.property)
      simpa only [assignment_cons] using hv
  | @exs n φ ih =>
    change (∃ q : ClassForcingQuotient P R G hR hG.1 N hnames,
      φ.Evalb (q :> assignment P R G hR hG.1 N hnames v)) ↔ _
    rw [classForcingFormula_exs, genericMeets_existential hR hG
      N hN _ (by definability)
      (fun x _ ↦ (classForcingFormula_regular N hN hR φ _).2.1)]
    constructor
    · rintro ⟨q, hq⟩
      obtain ⟨σ, rfl⟩ := ofName_surjective P R G hR hG.1 N hnames q
      refine ⟨σ.val, σ.property, ?_⟩
      have hv := (ih (σ :> v)).mp (by simpa only [assignment_cons] using hq)
      simpa only [nameTuple_cons] using hv
    · rintro ⟨x, hx, hF⟩
      let σ : {x : V // N x} := ⟨x, hx⟩
      refine ⟨ofName P R G hR hG.1 N hnames σ, ?_⟩
      have hv := (ih (σ :> v)).mpr (by simpa only [nameTuple_cons] using hF)
      simpa only [assignment_cons] using hv

end ClassForcingQuotient
end ZFVP
