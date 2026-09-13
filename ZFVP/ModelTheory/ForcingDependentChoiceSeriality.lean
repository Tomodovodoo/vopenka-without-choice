import ZFVP.ModelTheory.ForcingDependentChoicePathValues

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem dependentChoiceForcing_candidates_nonempty [Countable V] {P R one p γ : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (τA τB : ForcingName P)
    (hf : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one γ, τA.val, τB.val])) : IsNonempty (P ×ˢ domain τA.val) := by
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  let c : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 γ⟩
  have he := (S.formula_truth dependentChoiceSerialFormula ![c, τA, τB]).mpr ⟨p, hpG, hf⟩
  obtain ⟨x, hx⟩ := ((eval_dependentChoiceSerialFormula _).mp he).1
  obtain ⟨σ, q, _, hσq, _⟩ := (S.mem_ofName_iff τA x).mp hx
  exact ⟨⟨p, σ.val⟩ₖ, kpair_mem_iff.mpr ⟨hp, mem_domain_of_kpair_mem hσq⟩⟩

theorem dependentChoiceForcingRelation_serial [Countable V] {P R one p γ s : V} [IsOrdinal γ]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P)
    (τA τB : ForcingName P)
    (hf : p ∈ forcingFormula P R dependentChoiceSerialFormula
      (standardTuple ![checkName one γ, τA.val, τB.val]))
    (hclosed : ∀ α, IsOrdinal α → α ⊆ γ → IsForcingClosedAt P R α)
    (hs : s ∈ shorterSequences γ (P ×ˢ domain τA.val))
    (hpath : IsDependentChoicePath (P ×ˢ domain τA.val)
      (dependentChoiceForcingRelation P R one τA.val τB.val p γ) (domain s) s) :
    ∃ z ∈ P ×ˢ domain τA.val, ⟨s, z⟩ₖ ∈ dependentChoiceForcingRelation P R one τA.val τB.val p γ := by
  have hβ : domain s ∈ γ := ((mem_shorterSequences_domain _ _ _).mp hs).1
  let := IsOrdinal.of_mem hβ
  let := IsFunction.of_mem hpath.1
  have hb := dependentChoiceForcingPath_bounds hpath
  obtain ⟨q, hq, hqp, hbound⟩ := forcingClosedAt_lowerBound_below hR
    (hclosed _ inferInstance (IsOrdinal.toIsTransitive.transitive _ hβ)) hb.1 hp hb.2
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let S : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hpG := hG.1.2.2.1 q hqG p hp hqp
  have hconds (i : V) (hi : i ∈ domain s) : kpair.π₁ (s ‘ i) ∈ G := by
    have hci := function_value_mem hb.1.1 hi
    have hh := hbound i hi
    rw [conditionSequence_value hi] at hci hh
    exact hG.1.2.2.1 q hqG _ hci hh
  have hN := subnameSequence_isNameSequence τA.property hpath.1
  have hvpath := S.dependentChoiceForcingPath_value τA τB hpath hconds
  let c : ForcingName P := ⟨checkName one γ, checkName_isName htop.1 γ⟩
  have he := (S.formula_truth dependentChoiceSerialFormula ![c, τA, τB]).mpr ⟨p, hpG, hf⟩
  have hserial := ((eval_dependentChoiceSerialFormula _).mp he).2
  have hshort : S.sequenceValue (subnameSequence s) hN ∈ shorterSequences (S.check γ) (S.ofName τA) :=
    (mem_shorterSequences _ _ _).mpr ⟨S.check (domain s), (S.check_mem_iff _ _).mpr hβ, hvpath.1⟩
  obtain ⟨x, hx, hRx⟩ := hserial _ hshort
  obtain ⟨σ, u, _, hσu, heσ⟩ := (S.mem_ofName_iff τA x).mp hx
  have hσdom : σ.val ∈ domain τA.val := mem_domain_of_kpair_mem hσu
  rw [heσ] at hx hRx
  obtain ⟨r, hrG, hr⟩ := (S.dependentChoiceNext_truth τA τB s hN σ).mpr ⟨hx, hRx⟩
  obtain ⟨t, htG, htr, htq⟩ := hG.1.2.2.2 r hrG q hqG
  have htP := hG.1.1 t htG
  refine ⟨⟨t, σ.val⟩ₖ, kpair_mem_iff.mpr ⟨htP, hσdom⟩,
    (pair_mem_dependentChoiceForcingRelation _ _ _ _ _ _ _ _ _).mpr ?_⟩
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  refine ⟨hs, kpair_mem_iff.mpr ⟨htP, hσdom⟩, hR.2.2 t htP q hq p hp htq hqp, ?_, ?_⟩
  · intro i hi
    have hci := function_value_mem hb.1.1 hi
    have hh := hbound i hi
    rw [conditionSequence_value hi] at hci hh
    exact hR.2.2 t htP q hq _ hci htq hh
  · exact (forcingFormula_regular hR dependentChoiceNextFormula _).2.1 r hr t htP htr

end ZFVP
