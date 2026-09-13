import ZFVP.ModelTheory.CountableCohenInjectionCollision
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.ModelTheory.SymmetricModelOrdinals

/-! The set of generic subsets in the countable-support Cohen model is not well-orderable:
an injection into an ordinal would have a countable support, and a transposition moving
a fresh row to another fresh row produces two distinct subsets with the same image. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Every hereditarily symmetric name is fixed by all permutations fixing a countable set of rows. -/
theorem countableCohenName_countableSupport (hCC : InternalCountableChoice V) {I J τ : V}
    (hτ : IsHereditarilySymmetricName (countableCohenConditions I J) (countableCohenGroup I J)
      (countableCohenFilter I J) τ) :
    ∃ E, E ⊆ I ∧ IsInternallyCountable E ∧
      ∀ π, IsInternalPermutation I π → (∀ i ∈ E, π ‘ i = i) →
        nameAction (countableCohenPermutation I J π) τ = τ := by
  obtain ⟨E, hEI, hEc, hE⟩ := countableCohenFilter_rows hCC (hereditarilySymmetric_symmetric hτ).2
  exact ⟨E, hEI, hEc, fun π hπ hfix ↦ (mem_sep_iff.mp (hE π hπ hfix)).2⟩

theorem countableCohen_fresh_transposition {p E ξ : V}
    (hp : p ∈ countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
    (hE : IsInternallyCountable E) (hξE : ξ ∉ E) :
    ∃ ζ ∈ hartogsNumber (ω : V), ζ ≠ ξ ∧ ζ ∉ cohenSupport p ∧ ζ ∉ E ∧
      ∀ k ∈ E, k ∈ hartogsNumber (ω : V) →
        (internalTransposition (hartogsNumber (ω : V)) ξ ζ) ‘ k = k := by
  obtain ⟨ζ, hζ, hζout⟩ := exists_fresh_of_countable
    (internallyCountable_insert (internallyCountable_union hE (countableCohenSupport_countable hp)) ξ)
  have hζξ : ζ ≠ ξ := fun he ↦ hζout (mem_insert.mpr (Or.inl he))
  have hζE : ζ ∉ E := fun he ↦ hζout (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inl he))))
  have hζp : ζ ∉ cohenSupport p :=
    fun he ↦ hζout (mem_insert.mpr (Or.inr (mem_union_iff.mpr (Or.inr he))))
  refine ⟨ζ, hζ, hζξ, hζp, hζE, ?_⟩
  intro k hk hkω
  exact internalTransposition_fixed hkω (fun he ↦ hξE (he ▸ hk)) (fun he ↦ hζE (he ▸ hk))

namespace OmegaOneCohenModel

variable {G : Set V}
  (hG : IsExternalForcingGeneric (countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)))
    (countableCohenOrder (hartogsNumber (ω : V)) (hartogsNumber (ω : V))) G)

/-- If an injective set of the model sends the `ξ`-th generic subset to a check name, then `ξ`
belongs to every countable row support of its name. -/
theorem injection_pair_supported (τ : (omegaOneCohenContext G hG).Name)
    {E : V} (hEω : E ⊆ hartogsNumber (ω : V)) (hEc : IsInternallyCountable E)
    (hE : ∀ π, IsInternalPermutation (hartogsNumber (ω : V)) π → (∀ i ∈ E, π ‘ i = i) →
      nameAction (countableCohenPermutation (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) π) τ.val = τ.val)
    (hinj : Injective ((omegaOneCohenContext G hG).ofName τ))
    {ξ α : V} (hξ : ξ ∈ hartogsNumber (ω : V))
    (hpair : ⟨subset hG ξ hξ, (omegaOneCohenContext G hG).check α⟩ₖ ∈ (omegaOneCohenContext G hG).ofName τ) :
    ξ ∈ E := by
  classical
  let S := omegaOneCohenContext G hG
  let ν : S.Name := ⟨checkName ∅ α, hereditarilySymmetric_checkName S.poset S.group S.normal S.top α⟩
  let v : Fin 3 → S.Name := ![τ, subsetName hG ξ hξ, ν]
  have heval : injectivePairFormula.Evalb (fun k ↦ S.ofName (v k)) :=
    (eval_injectivePairFormula_assignment _).mpr ⟨hinj, hpair⟩
  obtain ⟨q, hqG, hqforce⟩ := (S.formula_truth injectivePairFormula v).mp heval
  have hq : q ∈ countableCohenConditions (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) := hG.1.1 q hqG
  by_contra hξE
  obtain ⟨ζ, hζ, hζξ, hζq, _, hζfix⟩ := countableCohen_fresh_transposition (ξ := ξ) hq hEc hξE
  let π := internalTransposition (hartogsNumber (ω : V)) ξ ζ
  have hπ : IsInternalPermutation (hartogsNumber (ω : V)) π := internalTransposition_permutation hξ hζ
  let a := countableCohenPermutation (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) π
  have ha : IsForcingAutomorphism S.P S.R a := countableCohenPermutation_automorphism hπ
  have haG : a ∈ S.Γ := (mem_countableCohenGroup _ _ a).mpr ⟨π, hπ, rfl⟩
  have hτfix : nameAction a τ.val = τ.val := hE π hπ (fun k hk ↦ hζfix k hk (hEω k hk))
  have hνfix : nameAction a ν.val = ν.val :=
    nameAction_checkName S.top.1 (forcingAutomorphism_top S.poset S.top ha) α
  have hσmove : nameAction a (subsetName hG ξ hξ).val =
      countableCohenSubsetName (hartogsNumber (ω : V)) (hartogsNumber (ω : V)) ζ := by
    change nameAction (countableCohenPermutation _ _ π) (countableCohenSubsetName _ _ ξ) = _
    rw [nameAction_countableCohenSubsetName hπ hξ, internalTransposition_left hξ]
  let w : Fin 3 → S.Name := ![τ, subsetName hG ζ hζ, ν]
  have hnames : (fun k ↦ nameAction a (v k).val) = fun k ↦ (w k).val := by
    funext k
    refine Fin.cases hτfix ?_ k
    intro k
    refine Fin.cases hσmove ?_ k
    intro k
    exact Fin.cases hνfix (fun l ↦ Fin.elim0 l) k
  have haqforce : a ‘ q ∈ symmetricForcingFormula S.P S.R S.Γ S.F injectivePairFormula
      (standardTuple (fun k ↦ (w k).val)) := by
    have hh := (symmetricForcingFormula_nameAction_iff S.order S.group S.normal haG
      injectivePairFormula (fun k ↦ (v k).val) (fun k ↦ (v k).property) hq).mpr hqforce
    simpa only [hnames] using hh
  obtain ⟨r, hr, hrq, hra⟩ := countableCohen_transposition_compatible hq hξ hζ hζq
  have hra' : ⟨r, a ‘ q⟩ₖ ∈ S.R := by
    change ⟨r, (countableCohenPermutation _ _ π) ‘ q⟩ₖ ∈ countableCohenOrder _ _
    rw [countableCohenPermutation_value hq]
    exact hra
  have hrforce := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 q hqforce r hr hrq
  have hraforce := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 (a ‘ q) haqforce r hr hra'
  have hv : (fun k ↦ (v k).val) = ![τ.val, (subsetName hG ξ hξ).val, ν.val] := by
    funext k
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) i) j) k
  have hw : (fun k ↦ (w k).val) = ![τ.val, (subsetName hG ζ hζ).val, ν.val] := by
    funext k
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun i ↦ Fin.cases rfl (fun l ↦ Fin.elim0 l) i) j) k
  rw [hv] at hrforce
  rw [hw] at hraforce
  exact countableCohen_injection_collision S.group S.normal τ.property
    (subsetName hG ξ hξ).property (subsetName hG ζ hζ).property hξ hζ hζξ.symm hr
    hrforce hraforce

theorem subsets_not_wellOrderable (hCC : InternalCountableChoice V) :
    ¬IsWellOrderable (subsets hG) := by
  let S := omegaOneCohenContext G hG
  intro hwo
  obtain ⟨β, hβ, hle⟩ := (wellOrderable_iff_cardLE_ordinal (subsets hG)).mp hwo
  let := hβ
  obtain ⟨γ, _, rfl⟩ := S.ordinal_eq_check β
  obtain ⟨e, he, hinj⟩ := hle
  obtain ⟨τ, rfl⟩ := S.ofName_surjective e
  obtain ⟨E, hEω, hEc, hE⟩ := countableCohenName_countableSupport hCC τ.property
  obtain ⟨ξ, hξ, hξE⟩ := exists_fresh_of_countable hEc
  have hmem : subset hG ξ hξ ∈ subsets hG := (mem_subsets_iff hG _).mpr ⟨ξ, hξ, rfl⟩
  have hval : (S.ofName τ) ‘ (subset hG ξ hξ) ∈ S.check γ := function_value_mem he hmem
  obtain ⟨α, _, hα⟩ := (S.mem_check_iff γ _).mp hval
  let := IsFunction.of_mem he
  have hpair : ⟨subset hG ξ hξ, S.check α⟩ₖ ∈ S.ofName τ := by
    rw [← hα]
    exact kpair_value_mem (by rw [domain_eq_of_mem_function he]; exact hmem)
  exact hξE (injection_pair_supported hG τ hEω hEc hE hinj hξ hpair)

theorem model_not_choice (hCC : InternalCountableChoice V) :
    ¬InternalChoice (omegaOneCohenContext G hG).Model := fun hAC ↦
  subsets_not_wellOrderable hG hCC (wellOrderable_of_internalChoice hAC _)

end OmegaOneCohenModel
end ZFVP
