import ZFVP.ModelTheory.ForcingSemanticConsequence
import ZFVP.ModelTheory.ForcingDependentChoiceTransfer
import ZFVP.ModelTheory.StageCountability
import ZFVP.ModelTheory.ForcingSmallUltrafilter
import ZFVP.ModelTheory.GenericRegularForcing
import ZFVP.ModelTheory.CountableZFTransfer
import ZFVP.ModelTheory.ForcingSmallInaccessibleSpecification
import ZFVP.SetTheory.WellOrderedSurjection
import ZFVP.SetTheory.WellOrderedCardinal

/-! The approximation property of the ground model (Hamkins): a subset of a checked set in a
forcing extension all of whose intersections with checked sets of size at most `|P|` are checked
is itself checked. The countable case is proved with generics through conditions; the general
case follows by the countable-model transfer of the corresponding forcing statement. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The approximation statement for the parameter `⟨θ, ⟨S, Pow⟩⟩`: every subset `A` of `θ` whose
intersections with the members of `S` are members of `Pow` is a member of `Pow`. -/
def approxFormula : SetTheorySemisentence 1 :=
  f“a. ∀ A, (∀ z ∈ A, z ∈ !kpair.π₁.dfn a) →
    (∀ x ∈ !kpair.π₁.dfn (!kpair.π₂.dfn a), ∃ B ∈ !kpair.π₂.dfn (!kpair.π₂.dfn a),
      ∀ z, (z ∈ A ∧ z ∈ x ↔ z ∈ B)) →
    ∃ B ∈ !kpair.π₂.dfn (!kpair.π₂.dfn a), A = B”

/-- `A ∩ X = B`. -/
def interEqFormula : SetTheorySemisentence 3 := f“A X B. ∀ z, (z ∈ A ∧ z ∈ X ↔ z ∈ B)”

def smallSubsetsFormula : SetTheorySemisentence 3 :=
  f“S θ P. ∀ x, x ∈ S ↔ x ⊆ θ ∧ !CardLE.dfn x P”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_approxFormula (a : V) : approxFormula.Evalb ![a] ↔
    ∀ A, (∀ z ∈ A, z ∈ kpair.π₁ a) →
      (∀ x ∈ kpair.π₁ (kpair.π₂ a), ∃ B ∈ kpair.π₂ (kpair.π₂ a), ∀ z, (z ∈ A ∧ z ∈ x ↔ z ∈ B)) →
      ∃ B ∈ kpair.π₂ (kpair.π₂ a), A = B := by
  simp [approxFormula]

theorem eval_interEqFormula (A X B : V) :
    interEqFormula.Evalb ![A, X, B] ↔ ∀ z, (z ∈ A ∧ z ∈ X ↔ z ∈ B) := by
  simp [interEqFormula]

/-- The subsets of `θ` of size at most `|P|`. -/
noncomputable def smallSubsets (θ P : V) : V := {x ∈ ℘ θ ; x ≤# P}

theorem mem_smallSubsets_iff (θ P x : V) : x ∈ smallSubsets θ P ↔ x ⊆ θ ∧ x ≤# P := by
  rw [smallSubsets, mem_sep_iff, mem_power_iff]

instance smallSubsetsFormula_defined : ℒₛₑₜ-function₂[V] smallSubsets via smallSubsetsFormula :=
  ⟨fun v ↦ by
    simp only [smallSubsetsFormula, Semiformula.Evalb]
    simp
    constructor
    · intro h
      apply mem_ext
      intro x
      rw [mem_smallSubsets_iff]
      exact h x
    · intro h x
      rw [h, mem_smallSubsets_iff]⟩

/-- The approximation parameter `⟨θ, ⟨[θ]^{≤|P|}, ℘ θ⟩⟩`. -/
noncomputable def approxParam (θ P : V) : V := ⟨θ, ⟨smallSubsets θ P, ℘ θ⟩ₖ⟩ₖ

theorem mem_memberDecisions_iff (P R one τ a p : V) :
    p ∈ memberDecisions P R one τ a ↔ p ∈ P ∧ ForcesCheckedMember P R one τ p a :=
  mem_sep_iff

theorem forcesCheckedMember_of_below {P R one τ a p q : V} (hR : IsForcingPreorder P R)
    (hp : ForcesCheckedMember P R one τ p a) (hq : q ∈ P) (hqp : ⟨q, p⟩ₖ ∈ R) :
    ForcesCheckedMember P R one τ q a :=
  (forcingFormula_regular hR memberFormula _).2.1 p hp q hq hqp

/-- A condition not forcing `ǎ ∈ τ` has an extension forcing its negation. -/
theorem exists_negation_below {P R one τ a q : V} (hR : IsForcingPreorder P R) (hq : q ∈ P)
    (hnot : ¬ ForcesCheckedMember P R one τ q a) :
    ∃ r ∈ P, ⟨r, q⟩ₖ ∈ R ∧ r ∈ forcingNegation P R (memberDecisions P R one τ a) := by
  by_contra hcon
  push Not at hcon
  apply hnot
  apply (forcingFormula_regular hR memberFormula (standardTuple ![checkName one a, τ])).2.2 q hq
  intro s hs hsq
  have hsN : s ∉ forcingNegation P R (memberDecisions P R one τ a) := hcon s hs hsq
  rw [mem_forcingNegation_iff] at hsN
  push Not at hsN
  obtain ⟨u, hu, hus, huD⟩ := hsN hs
  exact ⟨u, ((mem_memberDecisions_iff _ _ _ _ _ _).mp huD).2, hus⟩

/-- A generic filter cannot contain a condition forcing `ǎ ∈ τ` and one forcing its negation. -/
theorem not_negation_of_generic {P R one τ a p q : V} {G : Set V} (hR : IsForcingPreorder P R)
    (hG : IsExternalForcingGeneric P R G) (hp : p ∈ G) (hq : q ∈ G)
    (hpD : ForcesCheckedMember P R one τ p a)
    (hqN : q ∈ forcingNegation P R (memberDecisions P R one τ a)) : False := by
  obtain ⟨s, hs, hsp, hsq⟩ := hG.1.2.2.2 p hp q hq
  have hsP : s ∈ P := hG.1.1 s hs
  have hsD : s ∈ memberDecisions P R one τ a :=
    (mem_memberDecisions_iff _ _ _ _ _ _).mpr ⟨hsP, forcesCheckedMember_of_below hR hpD hsP hsp⟩
  exact ((mem_forcingNegation_iff _ _ _ _).mp hqN).2 s hsP hsq hsD

/-- No extension of `q` forces `ǎ ∈ τ`. -/
def NoForcingBelow (P R one τ a q : V) : Prop :=
  ∀ u ∈ P, ⟨u, q⟩ₖ ∈ R → u ∉ memberDecisions P R one τ a

/-- `q` decides every `ǎ ∈ τ` for `a ∈ θ`. -/
def DecidesAll (P R one τ θ q : V) : Prop :=
  ∀ a ∈ θ, q ∈ memberDecisions P R one τ a ∨ NoForcingBelow P R one τ a q

instance decidesAll_definable (P R one τ θ : V) : ℒₛₑₜ-predicate (DecidesAll P R one τ θ) := by
  have := memberDecisions_definable_one P R one τ
  unfold DecidesAll NoForcingBelow
  definability

/-- `a` is undecided by `q`: `q` does not force `ǎ ∈ τ` but some extension does. -/
def Undecided (P R one τ q a : V) : Prop :=
  q ∉ memberDecisions P R one τ a ∧ ∃ u ∈ P, ⟨u, q⟩ₖ ∈ R ∧ u ∈ memberDecisions P R one τ a

instance undecided_definable (P R one τ q : V) : ℒₛₑₜ-predicate (Undecided P R one τ q) := by
  have := memberDecisions_definable_one P R one τ
  unfold Undecided
  definability

/-- The elements of `θ` undecided by `q`. -/
noncomputable def undecidedSet (P R one τ θ q : V) : V := sep θ (Undecided P R one τ q) inferInstance

theorem undecidedSet_definable_one (P R one τ θ : V) : ℒₛₑₜ-function₁[V] (undecidedSet P R one τ θ) := by
  have := memberDecisions_definable_one P R one τ
  have h : ℒₛₑₜ-relation[V] (fun S q ↦ ∀ a, a ∈ S ↔ a ∈ θ ∧ Undecided P R one τ q a) := by
    unfold Undecided
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = undecidedSet P R one τ θ (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [undecidedSet, mem_sep_iff]

theorem mem_undecidedSet_iff (P R one τ θ q a : V) :
    a ∈ undecidedSet P R one τ θ q ↔ a ∈ θ ∧ Undecided P R one τ q a :=
  mem_sep_iff

/-- No extension lies in `E`. -/
def NoExtensionIn (P R E q : V) : Prop := ∀ r ∈ P, ⟨r, q⟩ₖ ∈ R → r ∉ E

instance noExtensionIn_definable (P R E : V) : ℒₛₑₜ-predicate (NoExtensionIn P R E) := by
  unfold NoExtensionIn
  definability

theorem function_mem_of_isFunction {g I X : V} [hg : IsFunction g] (hd : domain g = I) (hr : range g = X) :
    g ∈ X ^ I := by
  obtain ⟨X', Y', hg'⟩ := hg.mem_func
  rw [mem_function_iff]
  constructor
  · intro q hq
    obtain ⟨x, -, y, -, rfl⟩ := mem_prod_iff.mp (subset_prod_of_mem_function hg' q hq)
    exact kpair_mem_iff.mpr ⟨by rw [← hd]; exact mem_domain_of_kpair_mem hq,
      by rw [← hr]; exact mem_range_of_kpair_mem hq⟩
  · intro x hx
    rw [← hd] at hx
    exact ⟨g ‘ x, kpair_value_mem hx, fun y hy ↦ (value_eq_of_kpair_mem hy).symm⟩

theorem ForcingContext.interEq_truth (S : ForcingContext V) (τ : ForcingName S.P) (X B : V) :
    (∀ z, (z ∈ S.ofName τ ∧ z ∈ S.check X ↔ z ∈ S.check B)) ↔
      GenericMeets S.G (forcingFormula S.P S.R interEqFormula
        (standardTuple ![τ.val, checkName S.one X, checkName S.one B])) := by
  have h := S.formula_truth interEqFormula
    ![τ, ⟨checkName S.one X, checkName_isName S.top.1 X⟩, ⟨checkName S.one B, checkName_isName S.top.1 B⟩]
  rw [← eval_interEqFormula]
  have hv : (fun i ↦ S.ofName (![τ, ⟨checkName S.one X, checkName_isName S.top.1 X⟩,
      ⟨checkName S.one B, checkName_isName S.top.1 B⟩] i)) = ![S.ofName τ, S.check X, S.check B] := by
    funext i
    refine Fin.cases rfl (fun j ↦ Fin.cases rfl (fun t ↦ Fin.cases rfl (fun u ↦ Fin.elim0 u) t) j) i
  rw [hv] at h
  exact h

section

variable [Countable V] (hAC : InternalChoice V)

include hAC in
/-- The approximation property over a countable ground. -/
theorem approximation_countable (S : ForcingContext V) (θ : V) :
    approxFormula.Evalb ![S.check (approxParam θ S.P)] := by
  rw [eval_approxFormula]
  have hparam : S.check (approxParam θ S.P) =
      ⟨S.check θ, ⟨S.check (smallSubsets θ S.P), S.check (℘ θ)⟩ₖ⟩ₖ := by
    unfold approxParam
    rw [S.check_kpair, S.check_kpair]
  rw [hparam]
  simp only [kpair.π₁_kpair, kpair.π₂_kpair]
  intro A hAθ hsmall
  have hR := S.order
  have hG := S.generic
  have hA : A ⊆ S.check θ := hAθ
  obtain ⟨τ, hτ, hτA⟩ := S.exists_subsetName hA
  let τ' : ForcingName S.P := ⟨τ, subsetNames_isName S.top.1 hτ⟩
  have hAτ : A = S.ofName τ' := by
    rw [← S.nameValue_genericSet_check τ']
    exact hτA.symm
  -- the conditions deciding everything, and those with no such extension
  let E : V := sep S.P (DecidesAll S.P S.R S.one τ θ) inferInstance
  let F : V := sep S.P (NoExtensionIn S.P S.R E) inferInstance
  have hdense : ForcingDense S.P S.R (E ∪ F) := by
    refine ⟨fun q hq ↦ ?_, fun p hp ↦ ?_⟩
    · rcases mem_union_iff.mp hq with hq | hq
      · exact (mem_sep_iff.mp hq).1
      · exact (mem_sep_iff.mp hq).1
    · by_cases h : ∃ r ∈ S.P, ⟨r, p⟩ₖ ∈ S.R ∧ r ∈ E
      · obtain ⟨r, -, hrp, hrE⟩ := h
        exact ⟨r, mem_union_iff.mpr (Or.inl hrE), hrp⟩
      · push Not at h
        exact ⟨p, mem_union_iff.mpr (Or.inr (mem_sep_iff.mpr ⟨hp, h⟩)), hR.2.1 p hp⟩
  obtain ⟨q, hqG, hqEF⟩ := hG.2 (E ∪ F) hdense
  have hqP : q ∈ S.P := hG.1.1 q hqG
  rcases mem_union_iff.mp hqEF with hqE | hqF
  · -- a condition in the generic decides everything
    have hdec : DecidesAll S.P S.R S.one τ θ q := (mem_sep_iff.mp hqE).2
    have hDdef := memberDecisions_definable_one S.P S.R S.one τ
    let B : V := sep θ (fun a ↦ q ∈ memberDecisions S.P S.R S.one τ a) (by definability)
    refine ⟨S.check B, (S.check_mem_iff _ _).mpr (mem_power_iff.mpr sep_subset), ?_⟩
    apply mem_ext
    intro z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff _ _).mp (hA z hz)
      rw [hAτ] at hz
      obtain ⟨p, hpG, hpD⟩ := (S.checkedMember_truth τ' a).mp hz
      have hqD : q ∈ memberDecisions S.P S.R S.one τ a := by
        rcases hdec a ha with h | h
        · exact h
        · exfalso
          obtain ⟨s, hs, hsp, hsq⟩ := hG.1.2.2.2 p hpG q hqG
          have hsP : s ∈ S.P := hG.1.1 s hs
          exact h s hsP hsq ((mem_memberDecisions_iff _ _ _ _ _ _).mpr
            ⟨hsP, forcesCheckedMember_of_below hR hpD hsP hsp⟩)
      exact (S.check_mem_iff _ _).mpr (mem_sep_iff.mpr ⟨ha, hqD⟩)
    · intro hz
      obtain ⟨a, ha, rfl⟩ := (S.mem_check_iff _ _).mp hz
      obtain ⟨-, hqD⟩ := mem_sep_iff.mp ha
      rw [hAτ]
      exact (S.checkedMember_truth τ' a).mpr ⟨q, hqG, ((mem_memberDecisions_iff _ _ _ _ _ _).mp hqD).2⟩
  · -- below `q` nothing decides everything: choose undecided elements and derive a contradiction
    exfalso
    have hqF' : NoExtensionIn S.P S.R E q := (mem_sep_iff.mp hqF).2
    let I : V := sep S.P (fun r ↦ ⟨r, q⟩ₖ ∈ S.R) (by definability)
    have hU : ∀ r ∈ I, IsNonempty (undecidedSet S.P S.R S.one τ θ r) := by
      intro r hr
      obtain ⟨hrP, hrq⟩ := mem_sep_iff.mp hr
      have hrE : r ∉ E := hqF' r hrP hrq
      have hnd : ¬ DecidesAll S.P S.R S.one τ θ r := fun h ↦ hrE (mem_sep_iff.mpr ⟨hrP, h⟩)
      unfold DecidesAll NoForcingBelow at hnd
      push Not at hnd
      obtain ⟨a, ha, h1, u, hu, hur, huD⟩ := hnd
      exact ⟨⟨a, (mem_undecidedSet_iff _ _ _ _ _ _ _).mpr ⟨ha, h1, u, hu, hur, huD⟩⟩⟩
    obtain ⟨g, hgf, hgd, hgval⟩ :=
      choice_for_definable_family hAC I _ (undecidedSet_definable_one S.P S.R S.one τ θ) hU
    have hXθ : range g ⊆ θ := by
      intro y hy
      obtain ⟨r, hry⟩ := mem_range_iff.mp hy
      have hr : r ∈ I := by rw [← hgd]; exact mem_domain_of_kpair_mem hry
      have := hgval r hr
      rw [value_eq_of_kpair_mem hry] at this
      exact ((mem_undecidedSet_iff _ _ _ _ _ _ _).mp this).1
    have hXP : range g ≤# S.P := by
      have h1 : range g ≤# I := cardLE_of_surjective_function (wellOrderable_of_internalChoice hAC I)
        (function_mem_of_isFunction hgd rfl) rfl
      exact h1.trans (cardLE_of_subset sep_subset)
    have hXS : range g ∈ smallSubsets θ S.P := (mem_smallSubsets_iff _ _ _).mpr ⟨hXθ, hXP⟩
    obtain ⟨B, hB, hBeq⟩ := hsmall (S.check (range g)) ((S.check_mem_iff _ _).mpr hXS)
    obtain ⟨B₀, hB₀, rfl⟩ := (S.mem_check_iff _ _).mp hB
    -- a condition in the generic forcing `A ∩ X̌ = B̌₀`
    rw [hAτ] at hBeq
    obtain ⟨q₀, hq₀G, hq₀⟩ := (S.interEq_truth τ' (range g) B₀).mp hBeq
    obtain ⟨r, hrG, hrq₀, hrq⟩ := hG.1.2.2.2 q₀ hq₀G q hqG
    have hrP : r ∈ S.P := hG.1.1 r hrG
    have hrI : r ∈ I := mem_sep_iff.mpr ⟨hrP, hrq⟩
    -- the undecided element chosen for `r`
    have ha := (mem_undecidedSet_iff _ _ _ _ _ _ _).mp (hgval r hrI)
    obtain ⟨haθ, hrnot, u, huP, hur, huD⟩ := ha
    have haX : g ‘ r ∈ range g := by
      rw [← hgd] at hrI
      exact mem_range_of_kpair_mem (kpair_value_mem hrI)
    have hreg := forcingFormula_regular hR interEqFormula
      (standardTuple ![τ'.val, checkName S.one (range g), checkName S.one B₀])
    have hnotD : ¬ ForcesCheckedMember S.P S.R S.one τ r (g ‘ r) :=
      fun h ↦ hrnot ((mem_memberDecisions_iff _ _ _ _ _ _).mpr ⟨hrP, h⟩)
    obtain ⟨u', hu'P, hu'r, hu'N⟩ := exists_negation_below hR hrP hnotD
    -- both extensions force `A ∩ X̌ = B̌₀`
    have hq₀P : q₀ ∈ S.P := hG.1.1 q₀ hq₀G
    have huF := hreg.2.1 q₀ hq₀ u huP (hR.2.2 u huP r hrP q₀ hq₀P hur hrq₀)
    have hu'F := hreg.2.1 q₀ hq₀ u' hu'P (hR.2.2 u' hu'P r hrP q₀ hq₀P hu'r hrq₀)
    -- generic through `u`: `a ∈ B₀`
    obtain ⟨G', hG', huG'⟩ := exists_externalForcingGeneric hR huP
    let S' : ForcingContext V := ⟨S.P, S.R, S.one, G', hR, S.top, hG'⟩
    have haB : g ‘ r ∈ B₀ := by
      have heq := (S'.interEq_truth τ' (range g) B₀).mpr ⟨u, huG', huF⟩
      have hmem : S'.check (g ‘ r) ∈ S'.ofName τ' :=
        (S'.checkedMember_truth τ' (g ‘ r)).mpr ⟨u, huG', ((mem_memberDecisions_iff _ _ _ _ _ _).mp huD).2⟩
      have := (heq (S'.check (g ‘ r))).mp ⟨hmem, (S'.check_mem_iff _ _).mpr haX⟩
      exact (S'.check_mem_iff _ _).mp this
    -- generic through `u'`: `a ∉ B₀`
    obtain ⟨G'', hG'', hu'G''⟩ := exists_externalForcingGeneric hR hu'P
    let S'' : ForcingContext V := ⟨S.P, S.R, S.one, G'', hR, S.top, hG''⟩
    have heq := (S''.interEq_truth τ' (range g) B₀).mpr ⟨u', hu'G'', hu'F⟩
    have hmem : S''.check (g ‘ r) ∈ S''.ofName τ' :=
      ((heq (S''.check (g ‘ r))).mpr ((S''.check_mem_iff _ _).mpr haB)).1
    obtain ⟨p, hpG'', hpD⟩ := (S''.checkedMember_truth τ' (g ‘ r)).mp hmem
    exact not_negation_of_generic hR hG'' hpG'' hu'G'' hpD hu'N

end

/-- The transfer formula: choice and the forcing hypotheses imply that `p` forces the
approximation statement at the checked parameter. -/
def approxTransferFormula : SetTheorySemisentence 5 :=
  f“P R o p a. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧ p ∈ P ∧
    !choiceFunctionSentence ∧
    (∃ θ, a = !kpair.dfn θ (!kpair.dfn (!smallSubsetsFormula θ P) (!power.dfn θ))) →
      !(checkedUnaryForcingFormula approxFormula) P R o p a”

theorem eval_approxTransferFormula (v : Fin 5 → V) :
    approxTransferFormula.Evalb v ↔
      (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) → v 3 ∈ v 0 →
        InternalChoice V → (∃ θ, v 4 = approxParam θ (v 0)) →
        v 3 ∈ forcingFormula (v 0) (v 1) approxFormula (standardTuple ![checkName (v 2) (v 4)])) := by
  simp [approxTransferFormula, approxParam]

theorem approximation_forces {P R one p θ : V} (hAC : InternalChoice V) (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) :
    p ∈ forcingFormula P R approxFormula (standardTuple ![checkName one (approxParam θ P)]) := by
  have hh := eval_of_countable_zf approxTransferFormula (by
    intro W _ _ _ _ v
    refine (eval_approxTransferFormula v).mpr (fun hR htop hp hAC hθ ↦ ?_)
    obtain ⟨θ, hθ⟩ := hθ
    rw [hθ]
    refine forces_checkedUnary_of_all_generics hR htop hp approxFormula ?_
    intro G hG _
    have h := approximation_countable hAC (ForcingContext.mk (v 0) (v 1) (v 2) G hR htop hG) θ
    have hv : (![(ForcingContext.mk (v 0) (v 1) (v 2) G hR htop hG).check (approxParam θ (v 0))] :
        Fin 1 → (ForcingContext.mk (v 0) (v 1) (v 2) G hR htop hG).Model) =
        fun _ ↦ (ForcingContext.mk (v 0) (v 1) (v 2) G hR htop hG).check (approxParam θ (v 0)) := by
      funext i
      exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
    rw [hv] at h
    exact h)
    ![P, R, one, p, approxParam θ P]
  exact (eval_approxTransferFormula ![P, R, one, p, approxParam θ P]).mp hh hR htop hp hAC ⟨θ, rfl⟩

/-- The approximation property: a subset of `θ̌` whose intersections with the checks of the small
subsets of `θ` are checks is a check. -/
theorem ForcingContext.approximation (S : ForcingContext V) (hAC : InternalChoice V) (θ : V)
    {A : S.Model} (hA : A ⊆ S.check θ)
    (hsmall : ∀ x ∈ smallSubsets θ S.P, ∃ B : V, B ⊆ θ ∧ A ∩ S.check x = S.check B) :
    ∃ B : V, B ⊆ θ ∧ A = S.check B := by
  have hf := approximation_forces (θ := θ) hAC S.order S.top S.top.1
  have ht := S.formula_truth approxFormula ![⟨checkName S.one (approxParam θ S.P), checkName_isName S.top.1 _⟩]
  have hv : (fun i ↦ S.ofName (![(⟨checkName S.one (approxParam θ S.P), checkName_isName S.top.1 _⟩ :
      ForcingName S.P)] i)) = ![S.check (approxParam θ S.P)] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  rw [hv] at ht
  have h := ht.mpr ⟨S.one, S.one_mem_G, hf⟩
  rw [eval_approxFormula] at h
  have hparam : S.check (approxParam θ S.P) =
      ⟨S.check θ, ⟨S.check (smallSubsets θ S.P), S.check (℘ θ)⟩ₖ⟩ₖ := by
    unfold approxParam
    rw [S.check_kpair, S.check_kpair]
  rw [hparam] at h
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at h
  obtain ⟨B, hB, hAB⟩ := h A hA (by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (S.mem_check_iff _ _).mp hx
    obtain ⟨B, hBθ, hAB⟩ := hsmall x₀ hx₀
    refine ⟨S.check B, (S.check_mem_iff _ _).mpr (mem_power_iff.mpr hBθ), fun z ↦ ?_⟩
    rw [← mem_inter_iff, hAB])
  obtain ⟨B₀, hB₀, rfl⟩ := (S.mem_check_iff _ _).mp hB
  exact ⟨B₀, mem_power_iff.mp hB₀, hAB⟩

end ZFVP
