import ZFVP.ModelTheory.ForcingFunctionValues
import ZFVP.SetTheory.MaximalAntichains
import ZFVP.SetTheory.CountableSets
import ZFVP.SetTheory.InternalChoice

/-! Internal ccc bounds the possible checked values of an actual forcing name.
Ground Choice selects one deciding condition per possible value. Their range
is an internal antichain, so the set of possible values is internally countable.
The construction uses no external countability hypothesis on the ground model. -/

namespace ZFVP.Schmerl

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Countability of every antichain which is a set of the ground model. -/
def IsInternallyCCC (P R : V) : Prop :=
  ∀ A : V, IsForcingAntichain P R A → IsInternallyCountable A

instance isInternallyCCC_definable : ℒₛₑₜ-relation[V] IsInternallyCCC := by
  unfold IsInternallyCCC
  definability

theorem forcesCheckedFunctionValue_eq_of_compatible {P R one τ p q a x y : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hc : ForcingCompatible P R p q)
    (hx : ForcesCheckedFunctionValue P R one τ p a x)
    (hy : ForcesCheckedFunctionValue P R one τ q a y) : x = y := by
  obtain ⟨r, hr, hrp, hrq⟩ := hc
  exact forcesCheckedFunctionValue_unique hR htop hτ
    ((forcingFormula_regular hR functionValueFormula _).2.1 p hx r hr hrp)
    ((forcingFormula_regular hR functionValueFormula _).2.1 q hy r hr hrq)

/-- All values in `X` which some ground condition forces at the argument `a`. -/
noncomputable def checkedPossibleValues (P R one τ X a : V) : V :=
  {x ∈ X ; ∃ p ∈ P, ForcesCheckedFunctionValue P R one τ p a x}

theorem mem_checkedPossibleValues (P R one τ X a x : V) :
    x ∈ checkedPossibleValues P R one τ X a ↔
      x ∈ X ∧ ∃ p ∈ P, ForcesCheckedFunctionValue P R one τ p a x := by
  simp only [checkedPossibleValues, mem_sep_iff]

instance checkedPossibleValues_definable (P R one τ X : V) :
    ℒₛₑₜ-function₁[V] (checkedPossibleValues P R one τ X) := by
  have h : ℒₛₑₜ-relation[V] (fun Y a ↦ ∀ x, x ∈ Y ↔
      x ∈ X ∧ ∃ p ∈ P, ForcesCheckedFunctionValue P R one τ p a x) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = checkedPossibleValues P R one τ X (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [mem_checkedPossibleValues]

/-- The selected deciding conditions form a genuine internal antichain,
and the selection is an internal injection of all possible values into it. -/
theorem checkedPossibleValues_antichain (hAC : InternalChoice V)
    {P R one τ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (X a : V) :
    ∃ g : V, IsFunction g ∧ domain g = checkedPossibleValues P R one τ X a ∧
      Injective g ∧ IsForcingAntichain P R (range g) ∧
      ∀ x ∈ checkedPossibleValues P R one τ X a,
        ForcesCheckedFunctionValue P R one τ (g ‘ x) a x := by
  let E := checkedPossibleValues P R one τ X a
  let D : V → V := fun x ↦ {p ∈ P ; ForcesCheckedFunctionValue P R one τ p a x}
  have hD : ℒₛₑₜ-function₁ D := by
    have h : ℒₛₑₜ-relation[V] (fun Y x ↦ ∀ p, p ∈ Y ↔
        p ∈ P ∧ ForcesCheckedFunctionValue P R one τ p a x) := by definability
    apply Language.Definable.of_iff h
    intro v
    change v 0 = D (v 1) ↔ _
    rw [mem_ext_iff]
    apply forall_congr'
    intro p
    exact iff_congr Iff.rfl mem_sep_iff
  obtain ⟨g, hg, hdom, hchoice⟩ := choice_for_definable_family hAC E D hD (by
    intro x hx
    obtain ⟨_, p, hp, hpx⟩ := (mem_checkedPossibleValues _ _ _ _ _ _ _).mp hx
    exact ⟨p, mem_sep_iff.mpr ⟨hp, hpx⟩⟩)
  let : IsFunction g := hg
  have hvalue (x : V) (hx : x ∈ E) :
      g ‘ x ∈ P ∧ ForcesCheckedFunctionValue P R one τ (g ‘ x) a x :=
    mem_sep_iff.mp (hchoice x hx)
  have hpair (x p : V) (hxp : ⟨x, p⟩ₖ ∈ g) :
      p ∈ P ∧ ForcesCheckedFunctionValue P R one τ p a x := by
    have hx : x ∈ E := hdom ▸ mem_domain_of_kpair_mem hxp
    exact value_eq_of_kpair_mem hxp ▸ hvalue x hx
  have hinj : Injective g := by
    intro x y p hxp hyp
    exact forcesCheckedFunctionValue_unique hR htop hτ (hpair x p hxp).2 (hpair y p hyp).2
  have hanti : IsForcingAntichain P R (range g) := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨x, hxp⟩ := mem_range_iff.mp hp
      exact (hpair x p hxp).1
    · intro p hp q hq hpq hc
      obtain ⟨x, hxp⟩ := mem_range_iff.mp hp
      obtain ⟨y, hyq⟩ := mem_range_iff.mp hq
      have hxy := forcesCheckedFunctionValue_eq_of_compatible hR htop hτ hc
        (hpair x p hxp).2 (hpair y q hyq).2
      subst y
      exact hpq (IsFunction.unique hxp hyq)
  exact ⟨g, hg, hdom, hinj, hanti, fun x hx ↦ (hvalue x hx).2⟩

theorem checkedPossibleValues_countable (hAC : InternalChoice V)
    {P R one τ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hccc : IsInternallyCCC P R) (X a : V) :
    IsInternallyCountable (checkedPossibleValues P R one τ X a) := by
  obtain ⟨g, hg, hdom, hinj, hanti, _⟩ := checkedPossibleValues_antichain hAC hR htop hτ X a
  let : IsFunction g := hg
  have hcard : checkedPossibleValues P R one τ X a ≤# range g :=
    ⟨g, by simpa only [hdom] using IsFunction.mem_function g, hinj⟩
  exact hcard.trans (hccc (range g) hanti)

/-- One internal set collects all possible values over the internal omega. -/
noncomputable def checkedPossibleOmegaRange (P R one τ X : V) : V :=
  ⋃ˢ repl (checkedPossibleValues P R one τ X) (checkedPossibleValues_definable P R one τ X) (ω : V)

theorem mem_checkedPossibleOmegaRange (P R one τ X x : V) :
    x ∈ checkedPossibleOmegaRange P R one τ X ↔
      ∃ a ∈ (ω : V), x ∈ checkedPossibleValues P R one τ X a := by
  simp only [checkedPossibleOmegaRange, mem_sUnion_iff, repl_spec]
  constructor
  · rintro ⟨Y, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨_, ⟨a, ha, rfl⟩, hx⟩

theorem checkedPossibleOmegaRange_subset (P R one τ X : V) :
    checkedPossibleOmegaRange P R one τ X ⊆ X := by
  intro x hx
  obtain ⟨a, _, hx⟩ := (mem_checkedPossibleOmegaRange _ _ _ _ _ _).mp hx
  exact (mem_checkedPossibleValues _ _ _ _ _ _ _).mp hx |>.1

theorem checkedPossibleOmegaRange_countable (hAC : InternalChoice V)
    {P R one τ : V} (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hccc : IsInternallyCCC P R) (X : V) :
    IsInternallyCountable (checkedPossibleOmegaRange P R one τ X) := by
  let F := checkedPossibleValues P R one τ X
  let hF := checkedPossibleValues_definable P R one τ X
  let C := definableGraph (ω : V) F hF
  let : IsFunction C := definableGraph_isFunction _ _ _
  have hc : IsInternallyCountable (⋃ˢ range C) :=
    countable_union_of_countableChoice (countableChoice_of_internalChoice hAC)
      (domain_definableGraph _ _ _) (fun n hn ↦ by
        rw [value_definableGraph _ _ _ hn]
        exact checkedPossibleValues_countable hAC hR htop hτ hccc X n)
  simpa only [C, F, hF, range_definableGraph, checkedPossibleOmegaRange] using hc

end ZFVP.Schmerl
