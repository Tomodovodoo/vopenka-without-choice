import ZFVP.ModelTheory.SymmetricDCTransfer

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
namespace SymmetricContext
variable (S : SymmetricContext V)

theorem chain_conditions_descending {τA τB q f : V}
    (hf : f ∈ (S.chainCandidates τA q) ^ (ω : V))
    (hchain : ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ S.chainRelation τA τB q) :
    ∀ i ∈ (ω : V), ∀ j ∈ i, ⟨kpair.π₁ (f ‘ i), kpair.π₁ (f ‘ j)⟩ₖ ∈ S.R := by
  let := IsFunction.of_mem hf
  have hcond (n : V) (hn : n ∈ (ω : V)) : kpair.π₁ (f ‘ n) ∈ S.P :=
    (S.mem_chainCandidates (function_value_mem hf hn)).1
  apply naturalNumber_induction
    (fun i ↦ ∀ j ∈ i, ⟨kpair.π₁ (f ‘ i), kpair.π₁ (f ‘ j)⟩ₖ ∈ S.R) (by definability)
  · intro j hj
    exact (not_mem_empty hj).elim
  · intro i hi ih j hj
    have hstep : ⟨kpair.π₁ (f ‘ (succ i)), kpair.π₁ (f ‘ i)⟩ₖ ∈ S.R :=
      ((S.pair_mem_chainRelation _ _ _ _ _).mp (hchain i hi)).2.2.1
    rcases mem_succ_iff.mp hj with rfl | hji
    · exact hstep
    · have hjω : j ∈ (ω : V) := IsOrdinal.toIsTransitive.mem_trans hji hi
      exact S.order.2.2 _ (hcond (succ i) (ω_succ_closed hi)) _ (hcond i hi) _ (hcond j hjω)
        hstep (ih j hji)

theorem chain_lowerBound (hclosed : IsForcingClosedAt S.P S.R (ω : V)) {τA τB q f : V}
    (hf : f ∈ (S.chainCandidates τA q) ^ (ω : V))
    (hchain : ∀ n ∈ (ω : V), ⟨f ‘ n, f ‘ (succ n)⟩ₖ ∈ S.chainRelation τA τB q) :
    ∃ r ∈ S.P, ⟨r, q⟩ₖ ∈ S.R ∧ ∀ n ∈ (ω : V), ⟨r, kpair.π₁ (f ‘ n)⟩ₖ ∈ S.R := by
  let := IsFunction.of_mem hf
  have hf' : f ∈ (S.P ×ˢ domain τA) ^ (ω : V) :=
    mem_function_of_mem_function_of_subset hf (fun z hz ↦ (mem_sep_iff.mp hz).1)
  have hdf : domain f = (ω : V) := domain_eq_of_mem_function hf
  have hcv (i : V) (hi : i ∈ (ω : V)) : (conditionSequence f) ‘ i = kpair.π₁ (f ‘ i) :=
    conditionSequence_value (by rw [hdf]; exact hi)
  have hdesc : IsForcingDescending S.P S.R (ω : V) (conditionSequence f) := by
    refine ⟨conditionSequence_function hf', fun i hi j hj ↦ ?_⟩
    rw [hcv i hi, hcv j (IsOrdinal.toIsTransitive.mem_trans hj hi)]
    exact S.chain_conditions_descending hf hchain i hi j hj
  obtain ⟨r, hr, hbound⟩ := hclosed _ hdesc
  have hbound' (n : V) (hn : n ∈ (ω : V)) : ⟨r, kpair.π₁ (f ‘ n)⟩ₖ ∈ S.R := by
    have h := hbound n hn
    rwa [hcv n hn] at h
  have h0 : (0 : V) ∈ (ω : V) := by simp
  have hc0 := S.mem_chainCandidates (function_value_mem hf h0)
  refine ⟨r, hr, S.order.2.2 r hr _ hc0.1 q
    ((S.order.1 _ hc0.2.2.1 |> kpair_mem_iff.mp).2) (hbound' 0 h0) hc0.2.2.1, hbound'⟩

/-- Conditions carrying a full chain of candidates below them. -/
noncomputable def chainConditions (τA τB : V) : V :=
  {r ∈ S.P ; ∃ f ∈ (S.P ×ˢ domain τA) ^ (ω : V), ∀ n ∈ (ω : V),
    ⟨r, kpair.π₁ (f ‘ n)⟩ₖ ∈ S.R ∧
    kpair.π₁ (f ‘ n) ∈ symmetricForcingFormula S.P S.R S.Γ S.F symmetricDCMemberFormula
      (standardTuple ![kpair.π₂ (f ‘ n), τA]) ∧
    kpair.π₁ (f ‘ (succ n)) ∈ symmetricForcingFormula S.P S.R S.Γ S.F dependentChoiceNextFormula
      (standardTuple ![kpair.π₂ (f ‘ n), kpair.π₂ (f ‘ (succ n)), τA, τB])}

theorem chainConditions_denseBelow (hDC : InternalDependentChoice V)
    (hclosed : IsForcingClosedAt S.P S.R (ω : V)) (τA τB : S.Name) {p : V}
    (hne : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F boundedNonemptyFormula
      (standardTuple ![τA.val]))
    (hser : p ∈ symmetricForcingFormula S.P S.R S.Γ S.F serialFormula
      (standardTuple ![τA.val, τB.val])) :
    ForcingDenseBelow S.P S.R (S.chainConditions τA.val τB.val) p := by
  refine ⟨fun r hr ↦ (mem_sep_iff.mp hr).1, fun q hq hqp ↦ ?_⟩
  obtain ⟨f, hf, hchain⟩ := hDC _ _ (S.chainCandidates_nonempty τA hne hq hqp)
    (S.chainRelation_serial τA τB hser hq hqp)
  obtain ⟨r, hr, hrq, hbound⟩ := S.chain_lowerBound hclosed hf hchain
  let := IsFunction.of_mem hf
  have hf' : f ∈ (S.P ×ˢ domain τA.val) ^ (ω : V) :=
    mem_function_of_mem_function_of_subset hf (fun z hz ↦ (mem_sep_iff.mp hz).1)
  refine ⟨r, mem_sep_iff.mpr ⟨hr, f, hf', fun n hn ↦ ⟨hbound n hn, ?_, ?_⟩⟩, hrq⟩
  · exact (S.mem_chainCandidates (function_value_mem hf hn)).2.2.2
  · exact ((S.pair_mem_chainRelation _ _ _ _ _).mp (hchain n hn)).2.2.2

/-- Karagila's Lemma 3.1 at omega: dependent choice holds in the symmetric extension. -/
theorem dependentChoice (hDC : InternalDependentChoice V)
    (hclosed : IsForcingClosedAt S.P S.R (ω : V))
    (hcomplete : ∀ H : V, IsFunction H → domain H = (ω : V) →
      (∀ n ∈ (ω : V), H ‘ n ∈ S.F) → ⋂ˢ range H ∈ S.F) :
    InternalDependentChoice S.Model := by
  intro A B hA hB
  obtain ⟨τA, rfl⟩ := S.ofName_surjective A
  obtain ⟨τB, rfl⟩ := S.ofName_surjective B
  have hne' : boundedNonemptyFormula.Evalb (fun i ↦ S.ofName (![τA] i)) :=
    (eval_boundedNonemptyFormula_assignment _).mpr hA
  obtain ⟨p₁, hp₁G, hp₁⟩ := (S.formula_truth boundedNonemptyFormula ![τA]).mp hne'
  rw [S.tuple_val_one] at hp₁
  have hser' : serialFormula.Evalb (fun i ↦ S.ofName (![τA, τB] i)) :=
    (eval_serialFormula _).mpr hB
  obtain ⟨p₂, hp₂G, hp₂⟩ := (S.formula_truth serialFormula ![τA, τB]).mp hser'
  rw [S.tuple_val_two] at hp₂
  obtain ⟨p, hpG, hpp₁, hpp₂⟩ := S.generic.1.2.2.2 p₁ hp₁G p₂ hp₂G
  have hpP : p ∈ S.P := S.generic.1.1 p hpG
  have hne := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 p₁ hp₁ p hpP hpp₁
  have hser := (symmetricForcingFormula_regular S.order _ _ _ _).2.1 p₂ hp₂ p hpP hpp₂
  obtain ⟨r, hrG, hrD⟩ := externalForcingGeneric_meets_denseBelow S.order S.generic hpG
    (S.chainConditions_denseBelow hDC hclosed τA τB hne hser)
  obtain ⟨_, f, hf, hprops⟩ := mem_sep_iff.mp hrD
  let := IsFunction.of_mem hf
  have hdf : domain f = (ω : V) := domain_eq_of_mem_function hf
  have hfn (n : V) (hn : n ∈ (ω : V)) : f ‘ n ∈ S.P ×ˢ domain τA.val := function_value_mem hf hn
  have hcondP (n : V) (hn : n ∈ (ω : V)) : kpair.π₁ (f ‘ n) ∈ S.P := by
    obtain ⟨a, ha, b, _, he⟩ := mem_prod_iff.mp (hfn n hn)
    rw [he]
    simpa using ha
  have hνd (n : V) (hn : n ∈ (ω : V)) : kpair.π₂ (f ‘ n) ∈ domain τA.val := by
    obtain ⟨a, _, b, hb, he⟩ := mem_prod_iff.mp (hfn n hn)
    rw [he]
    simpa using hb
  have hcondG (n : V) (hn : n ∈ (ω : V)) : kpair.π₁ (f ‘ n) ∈ S.G :=
    S.generic.1.2.2.1 r hrG _ (hcondP n hn) (hprops n hn).1
  -- the sequence of subnames
  let t := subnameSequence f
  have hdt : domain t = (ω : V) := (subnameSequence_domain f).trans hdf
  have htv (n : V) (hn : n ∈ (ω : V)) : t ‘ n = kpair.π₂ (f ‘ n) :=
    subnameSequence_value (by rw [hdf]; exact hn)
  have htHS : ∀ i ∈ domain t, IsHereditarilySymmetricName S.P S.Γ S.F (t ‘ i) := by
    intro i hi
    rw [hdt] at hi
    rw [htv i hi]
    exact S.subname_hereditarilySymmetric τA (hνd i hi)
  let ν : ∀ n : V, n ∈ (ω : V) → S.Name := fun n hn ↦ ⟨t ‘ n, htHS n (hdt.symm ▸ hn)⟩
  have hstab : ∃ H ∈ S.F, ∀ π ∈ H, ∀ i ∈ domain t, nameAction π (t ‘ i) = t ‘ i := by
    let Hs := definableGraph (ω : V) (fun n ↦ nameStabilizer S.Γ (t ‘ n)) (by definability)
    have hHs : IsFunction Hs := definableGraph_isFunction _ _ _
    have hdH : domain Hs = (ω : V) := domain_definableGraph _ _ _
    refine ⟨⋂ˢ range Hs, hcomplete Hs hHs hdH ?_, ?_⟩
    · intro n hn
      rw [value_definableGraph _ _ _ hn]
      exact (hereditarilySymmetric_symmetric (htHS n (hdt.symm ▸ hn))).2
    · intro π hπ i hi
      have hi' : i ∈ (ω : V) := hdt ▸ hi
      have hne0 : IsNonempty (range Hs) :=
        ⟨Hs ‘ 0, mem_range_of_kpair_mem (kpair_value_mem (by rw [hdH]; simp))⟩
      have hmem := mem_sInter_iff_of_nonempty.mp hπ (Hs ‘ i)
        (mem_range_of_kpair_mem (kpair_value_mem (by rw [hdH]; exact hi')))
      rw [value_definableGraph _ _ _ hi'] at hmem
      exact (mem_sep_iff.mp hmem).2
  have hgHS := hereditarilySymmetric_sequenceName S.poset S.group S.normal S.top htHS hstab
  let gN : S.Name := ⟨sequenceName S.one t, hgHS⟩
  let g := S.ofName gN
  have hkey (i : V) (hi : i ∈ (ω : V)) :
      S.ofName ⟨orderedPairName S.one (checkName S.one i) (t ‘ i),
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
          (hereditarilySymmetric_checkName S.poset S.group S.normal S.top i) (htHS i (hdt.symm ▸ hi))⟩ =
      ⟨S.check i, S.ofName (ν i hi)⟩ₖ :=
    S.of_orderedPairName ⟨checkName S.one i, hereditarilySymmetric_checkName S.poset S.group S.normal S.top i⟩
      (ν i hi)
  have hmemg (x : S.Model) : x ∈ g ↔ ∃ n : V, ∃ hn : n ∈ (ω : V), x = ⟨S.check n, S.ofName (ν n hn)⟩ₖ := by
    rw [show g = S.ofName gN from rfl, S.mem_ofName_iff]
    constructor
    · rintro ⟨σ, s, _, hσs, rfl⟩
      obtain ⟨i, hi, he⟩ := (mem_sequenceName _ _ _).mp hσs
      have hi' : i ∈ (ω : V) := hdt ▸ hi
      refine ⟨i, hi', ?_⟩
      rw [← hkey i hi']
      exact congrArg S.ofName (Subtype.ext (kpair_iff.mp he).1)
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨orderedPairName S.one (checkName S.one n) (t ‘ n),
        hereditarilySymmetric_orderedPairName S.poset S.group S.normal S.top
          (hereditarilySymmetric_checkName S.poset S.group S.normal S.top n) (htHS n (hdt.symm ▸ hn))⟩,
        S.one, externalForcingFilter_top S.generic.1 S.top,
        (mem_sequenceName _ _ _).mpr ⟨n, hdt.symm ▸ hn, rfl⟩, (hkey n hn).symm⟩
  have hyA (n : V) (hn : n ∈ (ω : V)) : S.ofName (ν n hn) ∈ S.ofName τA := by
    have hforce := (hprops n hn).2.1
    rw [← htv n hn] at hforce
    have h := (S.formula_truth symmetricDCMemberFormula ![ν n hn, τA]).mpr
      (by rw [S.tuple_val_two]; exact ⟨_, hcondG n hn, hforce⟩)
    exact (eval_symmetricDCMemberFormula _).mp h
  have hyB (n : V) (hn : n ∈ (ω : V)) :
      ⟨S.ofName (ν n hn), S.ofName (ν (succ n) (ω_succ_closed hn))⟩ₖ ∈ S.ofName τB := by
    have hforce := (hprops n hn).2.2
    rw [← htv n hn, ← htv (succ n) (ω_succ_closed hn)] at hforce
    have h := (S.formula_truth dependentChoiceNextFormula ![ν n hn, ν (succ n) (ω_succ_closed hn), τA, τB]).mpr
      (by rw [S.tuple_val_four]; exact ⟨_, hcondG (succ n) (ω_succ_closed hn), hforce⟩)
    exact ((eval_dependentChoiceNextFormula _).mp h).2
  have hco : S.check (ω : V) = (ω : S.Model) := S.checkEmbedding.map_omega
  have hg : g ∈ S.ofName τA ^ (ω : S.Model) := by
    rw [← hco]
    apply mem_function.intro
    · intro z hz
      obtain ⟨n, hn, rfl⟩ := (hmemg z).mp hz
      exact kpair_mem_iff.mpr ⟨(S.check_mem_iff n ω).mpr hn, hyA n hn⟩
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω x).mp hx
      refine ⟨S.ofName (ν n hn), (hmemg _).mpr ⟨n, hn, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨m, hm, he⟩ := (hmemg _).mp hy
      obtain ⟨hnm, rfl⟩ := kpair_iff.mp he
      have hnm' : n = m := (S.check_eq_iff n m).mp hnm
      subst hnm'
      rfl
  refine ⟨g, hg, ?_⟩
  let := IsFunction.of_mem hg
  intro n' hn'
  rw [← hco] at hn'
  obtain ⟨n, hn, rfl⟩ := (S.mem_check_iff ω n').mp hn'
  have hv (m : V) (hm : m ∈ (ω : V)) : g ‘ (S.check m) = S.ofName (ν m hm) :=
    value_eq_of_kpair_mem ((hmemg _).mpr ⟨m, hm, rfl⟩)
  have hsucc : succ (S.check n) = S.check (succ n) := (S.checkEmbedding.map_succ n).symm
  rw [hv n hn, hsucc, hv (succ n) (ω_succ_closed hn)]
  exact hyB n hn

end SymmetricContext
end ZFVP
