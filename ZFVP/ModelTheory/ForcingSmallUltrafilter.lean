import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.UltrafilterFibers

/-! Banerjee, Theorem 2.5(2): a nonprincipal `κ`-complete ultrafilter `U` on a measurable
ordinal `κ` generates, in any forcing extension by a poset of size below `κ`, a nonprincipal
internally `κ`-complete ultrafilter on `κ`. The proof reads a subset of `κ` in the extension
through the ground map sending `a` to the set of conditions forcing `ǎ` into its name; that map
has a fiber in `U` on which membership is decided uniformly by the generic. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def memberFormula : SetTheorySemisentence 2 := “x y. x ∈ y”

def valueMemberFormula : SetTheorySemisentence 3 := f“f i x. x ∈ !value.dfn f i”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_memberFormula (v : Fin 2 → V) : memberFormula.Evalb v ↔ v 0 ∈ v 1 := by
  simp [memberFormula]

theorem eval_valueMemberFormula (v : Fin 3 → V) :
    valueMemberFormula.Evalb v ↔ v 2 ∈ (v 0) ‘ (v 1) := by
  simp [valueMemberFormula]

/-- `p` forces `ǎ ∈ τ`. -/
def ForcesCheckedMember (P R one τ p a : V) : Prop :=
  p ∈ forcingFormula P R memberFormula (standardTuple ![checkName one a, τ])

instance forcesCheckedMember_definable (P R one τ : V) :
    ℒₛₑₜ-relation[V] (ForcesCheckedMember P R one τ) := by
  unfold ForcesCheckedMember
  simp only [standardTuple]
  definability

/-- `p` forces `ǎ ∈ σ(ξ̌)`. -/
def ForcesCheckedValueMember (P R one σ p ξ a : V) : Prop :=
  p ∈ forcingFormula P R valueMemberFormula (standardTuple ![σ, checkName one ξ, checkName one a])

instance forcesCheckedValueMember_definable (P R one σ : V) :
    ℒₛₑₜ-relation₃[V] (ForcesCheckedValueMember P R one σ) := by
  unfold ForcesCheckedValueMember
  simp only [standardTuple]
  definability

/-- The conditions forcing `ǎ` into `τ`. -/
noncomputable def memberDecisions (P R one τ a : V) : V :=
  {p ∈ P ; ForcesCheckedMember P R one τ p a}

theorem memberDecisions_definable_one (P R one τ : V) :
    ℒₛₑₜ-function₁[V] (memberDecisions P R one τ) := by
  have hd : ℒₛₑₜ-relation[V] (fun Q a ↦ ∀ p, p ∈ Q ↔ p ∈ P ∧ ForcesCheckedMember P R one τ p a) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = memberDecisions P R one τ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [memberDecisions, mem_sep_iff]

/-- The conditions forcing `ǎ` into the `ξ̌`-th value of `σ`. -/
noncomputable def valueMemberDecisions (P R one σ ξ a : V) : V :=
  {p ∈ P ; ForcesCheckedValueMember P R one σ p ξ a}

instance valueMemberDecisions_definable (P R one σ : V) :
    ℒₛₑₜ-function₂[V] (valueMemberDecisions P R one σ) := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Q ξ a ↦ ∀ p,
    p ∈ Q ↔ p ∈ P ∧ ForcesCheckedValueMember P R one σ p ξ a) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = valueMemberDecisions P R one σ (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  exact ⟨fun h p ↦ (h p).trans mem_sep_iff, fun h p ↦ (h p).trans mem_sep_iff.symm⟩

/-- The members of `κ` with the same decision set at `ξ` as `a`. -/
noncomputable def decisionFiber (P R one σ κ ξ a : V) : V :=
  {a' ∈ κ ; valueMemberDecisions P R one σ ξ a' = valueMemberDecisions P R one σ ξ a}

instance decisionFiber_definable (P R one σ κ : V) :
    ℒₛₑₜ-function₂[V] (decisionFiber P R one σ κ) := by
  have hd : ℒₛₑₜ-relation₃[V] (fun Y ξ a ↦ ∀ a', a' ∈ Y ↔ a' ∈ κ ∧
    valueMemberDecisions P R one σ ξ a' = valueMemberDecisions P R one σ ξ a) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = decisionFiber P R one σ κ (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp [decisionFiber]

/-- The members of `κ` whose decision set at `ξ` has its fiber in `U`. -/
noncomputable def decisionMajority (P R one σ κ U ξ : V) : V :=
  {a ∈ κ ; decisionFiber P R one σ κ ξ a ∈ U}

theorem decisionMajority_definable_one (P R one σ κ U : V) :
    ℒₛₑₜ-function₁[V] (decisionMajority P R one σ κ U) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y ξ ↦ ∀ a, a ∈ Y ↔ a ∈ κ ∧
    decisionFiber P R one σ κ ξ a ∈ U) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = decisionMajority P R one σ κ U (v 1) ↔ _
  rw [mem_ext_iff]
  simp [decisionMajority]

namespace ForcingContext

theorem checkedMember_truth (S : ForcingContext V) (τ : ForcingName S.P) (a : V) :
    S.check a ∈ S.ofName τ ↔ ∃ p ∈ S.G, ForcesCheckedMember S.P S.R S.one τ.val p a := by
  let ν : ForcingName S.P := ⟨checkName S.one a, checkName_isName S.top.1 a⟩
  have h := S.formula_truth memberFormula ![ν, τ]
  rw [eval_memberFormula] at h
  exact h

theorem checkedValueMember_truth (S : ForcingContext V) (σ : ForcingName S.P) (ξ a : V) :
    S.check a ∈ (S.ofName σ) ‘ (S.check ξ) ↔
      ∃ p ∈ S.G, ForcesCheckedValueMember S.P S.R S.one σ.val p ξ a := by
  let ν : ForcingName S.P := ⟨checkName S.one ξ, checkName_isName S.top.1 ξ⟩
  let μ : ForcingName S.P := ⟨checkName S.one a, checkName_isName S.top.1 a⟩
  have h := S.formula_truth valueMemberFormula ![σ, ν, μ]
  rw [eval_valueMemberFormula] at h
  exact h

theorem check_inter (S : ForcingContext V) (X Y : V) : S.check (X ∩ Y) = S.check X ∩ S.check Y := by
  ext z
  rw [mem_inter_iff, S.mem_check_iff, S.mem_check_iff, S.mem_check_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, (mem_inter_iff.mp hy).1, rfl⟩, ⟨y, (mem_inter_iff.mp hy).2, rfl⟩⟩
  · rintro ⟨⟨y, hy, rfl⟩, ⟨y', hy', he⟩⟩
    rw [S.check_eq_iff] at he
    subst he
    exact ⟨y, mem_inter_iff.mpr ⟨hy, hy'⟩, rfl⟩

/-- The filter on `κ̌` generated by the checks of members of `U`. -/
noncomputable def derivedFilter (S : ForcingContext V) (κ U : V) : S.Model :=
  {X ∈ ℘ (S.check κ) ; ∃ Y ∈ S.check U, Y ⊆ X}

theorem mem_derivedFilter_iff (S : ForcingContext V) (κ U : V) (X : S.Model) :
    X ∈ S.derivedFilter κ U ↔ X ⊆ S.check κ ∧ ∃ Y ∈ U, S.check Y ⊆ X := by
  simp only [derivedFilter, mem_sep_iff, mem_power_iff]
  constructor
  · rintro ⟨hX, Y', hY', hsub⟩
    obtain ⟨Y, hY, rfl⟩ := (S.mem_check_iff U Y').mp hY'
    exact ⟨hX, Y, hY, hsub⟩
  · rintro ⟨hX, Y, hY, hsub⟩
    exact ⟨hX, S.check Y, (S.check_mem_iff Y U).mpr hY, hsub⟩

/-- Membership of checks in a named subset of `κ̌` is decided on a `U`-large set. -/
theorem decided_fiber (S : ForcingContext V) {κ U μ : V}
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hμ : μ ∈ κ)
    (hP : ℘ S.P ≤# μ) (τ : ForcingName S.P) :
    ∃ Y ∈ U, (∀ a ∈ Y, S.check a ∈ S.ofName τ) ∨ (∀ a ∈ Y, S.check a ∉ S.ofName τ) := by
  have hF := memberDecisions_definable_one S.P S.R S.one τ.val
  let g := definableGraph κ (memberDecisions S.P S.R S.one τ.val) hF
  have hg : g ∈ ℘ S.P ^ κ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function κ _ hF)
    intro y hy
    obtain ⟨a, _, rfl⟩ := (repl_spec hF).mp hy
    exact mem_power_iff.mpr sep_subset
  obtain ⟨Q, _, hQ⟩ := ultrafilter_fiber_mem hU hc hμ hP hg
  refine ⟨_, hQ, ?_⟩
  by_cases hG : ∃ p ∈ S.G, p ∈ Q
  · left
    intro a ha
    obtain ⟨haκ, hQa⟩ := mem_sep_iff.mp ha
    rw [value_definableGraph κ _ hF haκ] at hQa
    obtain ⟨p, hp, hpQ⟩ := hG
    rw [← hQa] at hpQ
    exact (S.checkedMember_truth τ a).mpr ⟨p, hp, (mem_sep_iff.mp hpQ).2⟩
  · right
    intro a ha hmem
    obtain ⟨haκ, hQa⟩ := mem_sep_iff.mp ha
    rw [value_definableGraph κ _ hF haκ] at hQa
    obtain ⟨p, hp, hf⟩ := (S.checkedMember_truth τ a).mp hmem
    apply hG
    refine ⟨p, hp, ?_⟩
    rw [← hQa]
    exact mem_sep_iff.mpr ⟨S.generic.1.1 p hp, hf⟩

/-- On the majority set at `ξ`, membership in the `ξ̌`-th value of `σ` is decided uniformly. -/
theorem decisionMajority_mem_and_uniform (S : ForcingContext V) {κ U μ : V}
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hμ : μ ∈ κ)
    (hP : ℘ S.P ≤# μ) (σ : ForcingName S.P) (ξ : V) :
    decisionMajority S.P S.R S.one σ.val κ U ξ ∈ U ∧
      ∀ a ∈ decisionMajority S.P S.R S.one σ.val κ U ξ,
        ∀ z ∈ decisionMajority S.P S.R S.one σ.val κ U ξ,
          valueMemberDecisions S.P S.R S.one σ.val ξ a = valueMemberDecisions S.P S.R S.one σ.val ξ z := by
  have hF : ℒₛₑₜ-function₁ (valueMemberDecisions S.P S.R S.one σ.val ξ) := by definability
  let g := definableGraph κ (valueMemberDecisions S.P S.R S.one σ.val ξ) hF
  have hg : g ∈ ℘ S.P ^ κ := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function κ _ hF)
    intro y hy
    obtain ⟨a, _, rfl⟩ := (repl_spec hF).mp hy
    exact mem_power_iff.mpr sep_subset
  obtain ⟨Q, _, hQ⟩ := ultrafilter_fiber_mem hU hc hμ hP hg
  have hfiber : ∀ a ∈ κ, {a' ∈ κ ; g ‘ a' = g ‘ a} = {a' ∈ κ ; g ‘ a' = Q} ∨
      ({a' ∈ κ ; g ‘ a' = g ‘ a} ∩ {a' ∈ κ ; g ‘ a' = Q}) = ∅ := by
    intro a ha
    by_cases hQa : g ‘ a = Q
    · left
      ext a'
      simp only [mem_sep_iff, hQa]
    · right
      ext a'
      simp only [mem_inter_iff, mem_sep_iff, not_mem_empty, iff_false]
      rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact hQa (h1.symm.trans h2)
  have hmaj : ∀ a ∈ κ, a ∈ decisionMajority S.P S.R S.one σ.val κ U ξ ↔ g ‘ a = Q := by
    intro a ha
    have hval : ∀ a' ∈ κ, valueMemberDecisions S.P S.R S.one σ.val ξ a' = g ‘ a' := fun a' ha' ↦
      (value_definableGraph κ _ hF ha').symm
    have hset : decisionFiber S.P S.R S.one σ.val κ ξ a = {a' ∈ κ ; g ‘ a' = g ‘ a} := by
      ext a'
      constructor
      · intro h
        obtain ⟨ha', h⟩ := mem_sep_iff.mp h
        exact mem_sep_iff.mpr ⟨ha', by rw [← hval a' ha', ← hval a ha]; exact h⟩
      · intro h
        obtain ⟨ha', h⟩ := mem_sep_iff.mp h
        exact mem_sep_iff.mpr ⟨ha', by rw [hval a' ha', hval a ha]; exact h⟩
    have hiff : a ∈ decisionMajority S.P S.R S.one σ.val κ U ξ ↔
        a ∈ κ ∧ decisionFiber S.P S.R S.one σ.val κ ξ a ∈ U := mem_sep_iff
    rw [hiff, hset]
    constructor
    · rintro ⟨_, hin⟩
      rcases hfiber a ha with heq | hdisj
      · have : a ∈ {a' ∈ κ ; g ‘ a' = Q} := by
          rw [← heq]
          exact mem_sep_iff.mpr ⟨ha, rfl⟩
        exact (mem_sep_iff.mp this).2
      · exfalso
        have hi := hU.1.inter hin hQ
        rw [hdisj] at hi
        exact hU.1.empty_not_mem hi
    · intro hQa
      refine ⟨ha, ?_⟩
      have : {a' ∈ κ ; g ‘ a' = g ‘ a} = {a' ∈ κ ; g ‘ a' = Q} := by
        ext a'
        simp only [mem_sep_iff, hQa]
      rw [this]
      exact hQ
  have hsub : decisionMajority S.P S.R S.one σ.val κ U ξ ⊆ κ := sep_subset
  refine ⟨?_, ?_⟩
  · have : {a' ∈ κ ; g ‘ a' = Q} = decisionMajority S.P S.R S.one σ.val κ U ξ := by
      ext a
      constructor
      · intro h
        have ha := (mem_sep_iff.mp h).1
        exact (hmaj a ha).mpr (mem_sep_iff.mp h).2
      · intro h
        have ha := hsub _ h
        exact mem_sep_iff.mpr ⟨ha, (hmaj a ha).mp h⟩
    rw [← this]
    exact hQ
  · intro a ha z hz
    have h1 := (hmaj a (hsub _ ha)).mp ha
    have h2 := (hmaj z (hsub _ hz)).mp hz
    rw [← value_definableGraph κ _ hF (hsub _ ha), ← value_definableGraph κ _ hF (hsub _ hz), h1, h2]

/-- Banerjee 2.5(2): the derived filter is a nonprincipal internally complete ultrafilter. -/
theorem derivedFilter_ultrafilter (S : ForcingContext V) (hAC : InternalChoice V) {κ U lam : V}
    [IsOrdinal κ] (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U)
    (hlam : lam ∈ κ) (hP : S.P ≤# lam) :
    IsNonprincipalSetUltrafilter (S.check κ) (S.derivedFilter κ U) ∧
      IsOrdinalComplete (S.check κ) (S.derivedFilter κ U) := by
  obtain ⟨μ, hμ, hμP⟩ := measurable_power_bounded hAC hU hc hlam
  have hPμ : ℘ S.P ≤# μ := (power_cardLE_of_cardLE hP).trans hμP
  have hmem := S.mem_derivedFilter_iff κ U
  have hκU : κ ∈ U := hU.1.2.1
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro X hX
    exact mem_power_iff.mpr ((hmem X).mp hX).1
  · exact (hmem _).mpr ⟨subset_refl _, κ, hκU, subset_refl _⟩
  · intro h
    obtain ⟨_, Y, hY, hsub⟩ := (hmem _).mp h
    obtain ⟨y, hy⟩ := hU.1.nonempty_of_mem hY
    exact not_mem_empty (hsub _ ((S.check_mem_iff y Y).mpr hy))
  · intro X hX Z hZ hXZ
    obtain ⟨_, Y, hY, hsub⟩ := (hmem X).mp hX
    exact (hmem Z).mpr ⟨hZ, Y, hY, subset_trans hsub hXZ⟩
  · intro X hX Z hZ
    obtain ⟨hXκ, Y, hY, hsub⟩ := (hmem X).mp hX
    obtain ⟨hZκ, W, hW, hsub'⟩ := (hmem Z).mp hZ
    refine (hmem _).mpr ⟨fun z hz ↦ hXκ _ (mem_inter_iff.mp hz).1, Y ∩ W, hU.1.inter hY hW, ?_⟩
    rw [S.check_inter]
    intro z hz
    rw [mem_inter_iff] at hz ⊢
    exact ⟨hsub _ hz.1, hsub' _ hz.2⟩
  · intro X hX
    obtain ⟨τ, rfl⟩ := S.ofName_surjective X
    obtain ⟨Y, hY, hdec⟩ := S.decided_fiber hU hc hμ hPμ τ
    have hYκ : Y ⊆ κ := hU.1.subset_of_mem hY
    rcases hdec with hin | hout
    · left
      refine (hmem _).mpr ⟨hX, Y, hY, ?_⟩
      intro z hz
      obtain ⟨y, hy, rfl⟩ := (S.mem_check_iff Y z).mp hz
      exact hin y hy
    · right
      refine (hmem _).mpr ⟨sep_subset, Y, hY, ?_⟩
      intro z hz
      obtain ⟨y, hy, rfl⟩ := (S.mem_check_iff Y z).mp hz
      rw [mem_relativeComplement_iff]
      exact ⟨(S.check_mem_iff y κ).mpr (hYκ _ hy), hout y hy⟩
  · intro x hx hsx
    obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff κ x).mp hx
    obtain ⟨_, Y, hY, hsub⟩ := (hmem _).mp hsx
    have hYa : Y ⊆ ({a} : V) := by
      intro y hy
      have := hsub _ ((S.check_mem_iff y Y).mpr hy)
      rw [mem_singleton_iff, S.check_eq_iff] at this
      rw [mem_singleton_iff]
      exact this
    exact hU.2 a ha (hU.1.upward hY (by intro z hz; rw [mem_singleton_iff] at hz; exact hz ▸ ha) hYa)
  · intro α hα g hg
    obtain ⟨α₀, hα₀, rfl⟩ := (S.mem_check_iff κ α).mp hα
    obtain ⟨σ, rfl⟩ := S.ofName_surjective g
    have hF := decisionMajority_definable_one S.P S.R S.one σ.val κ U
    let Ygraph := definableGraph α₀ (decisionMajority S.P S.R S.one σ.val κ U) hF
    have hYgraph : Ygraph ∈ U ^ α₀ := by
      apply mem_function_of_mem_function_of_subset (definableGraph_mem_function α₀ _ hF)
      intro y hy
      obtain ⟨ξ, _, rfl⟩ := (repl_spec hF).mp hy
      exact (S.decisionMajority_mem_and_uniform hU hc hμ hPμ σ ξ).1
    have hZ := hc α₀ hα₀ Ygraph hYgraph
    refine (hmem _).mpr ⟨sep_subset, _, hZ, ?_⟩
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := (S.mem_check_iff _ z).mp hz
    rw [mem_indexedIntersection_iff] at hz₀ ⊢
    refine ⟨(S.check_mem_iff z₀ κ).mpr hz₀.1, ?_⟩
    intro i hi
    obtain ⟨ξ, hξ, rfl⟩ := (S.mem_check_iff α₀ i).mp hi
    have hzξ := hz₀.2 ξ hξ
    rw [value_definableGraph α₀ _ hF hξ] at hzξ
    -- the value at `ξ̌` is in the derived filter, so it contains the check of a `U`-set
    have hval : (S.ofName σ) ‘ (S.check ξ) ∈ S.derivedFilter κ U :=
      function_value_mem hg ((S.check_mem_iff ξ α₀).mpr hξ)
    obtain ⟨_, W, hW, hWsub⟩ := (hmem _).mp hval
    obtain ⟨hmaj, huniform⟩ := S.decisionMajority_mem_and_uniform hU hc hμ hPμ σ ξ
    obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem (hU.1.inter hW hmaj)
    rw [mem_inter_iff] at ha
    have hamem : S.check a ∈ (S.ofName σ) ‘ (S.check ξ) := hWsub _ ((S.check_mem_iff a W).mpr ha.1)
    obtain ⟨p, hp, hpa⟩ := (S.checkedValueMember_truth σ ξ a).mp hamem
    apply (S.checkedValueMember_truth σ ξ z₀).mpr
    refine ⟨p, hp, ?_⟩
    have hpQ : p ∈ valueMemberDecisions S.P S.R S.one σ.val ξ a :=
      mem_sep_iff.mpr ⟨S.generic.1.1 p hp, hpa⟩
    rw [huniform a ha.2 z₀ hzξ] at hpQ
    exact (mem_sep_iff.mp hpQ).2

end ForcingContext
end ZFVP
