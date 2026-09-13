import ZFVP.SetTheory.SetUltrafilter
import ZFVP.SetTheory.WellOrderedCardinal
import ZFVP.SetTheory.WellOrderingChoice
import ZFVP.SetTheory.FunctionValue

/-! Combinatorics of a nonprincipal `κ`-complete ultrafilter on an ordinal `κ`: a map from
`κ` into a set of size below `κ` has a fiber in the ultrafilter, `κ` is a strong limit, and
under Choice every power set of a smaller ordinal is bounded in `κ`. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The complement of the composite fiber of `i` under `e ∘ g`. -/
noncomputable def compositeFiberComplement (κ e g i : V) : V :=
  relativeComplement κ {a ∈ κ ; e ‘ (g ‘ a) = i}

instance compositeFiberComplement_definable : ℒₛₑₜ-function₄[V] compositeFiberComplement := by
  have hd : ℒₛₑₜ-relation₅[V] (fun Y κ e g i ↦ ∀ a,
    a ∈ Y ↔ a ∈ κ ∧ ¬(a ∈ κ ∧ e ‘ (g ‘ a) = i)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = compositeFiberComplement (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [compositeFiberComplement, mem_relativeComplement_iff, mem_sep_iff]

/-- The members of `κ` whose `f`-value contains `i`. -/
noncomputable def coordinateFiber (κ f i : V) : V := {a ∈ κ ; i ∈ f ‘ a}

instance coordinateFiber_definable : ℒₛₑₜ-function₃[V] coordinateFiber := by
  have hd : ℒₛₑₜ-relation₄[V] (fun Y κ f i ↦ ∀ a, a ∈ Y ↔ a ∈ κ ∧ i ∈ f ‘ a) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coordinateFiber (v 1) (v 2) (v 3) ↔ _
  rw [mem_ext_iff]
  simp only [coordinateFiber, mem_sep_iff]

/-- The side of the coordinate fiber of `i` that belongs to `U`. -/
noncomputable def coordinateChoice (κ U f i : V) : V :=
  {a ∈ κ ; (coordinateFiber κ f i ∈ U → i ∈ f ‘ a) ∧ (coordinateFiber κ f i ∉ U → i ∉ f ‘ a)}

instance coordinateChoice_definable : ℒₛₑₜ-function₄[V] coordinateChoice := by
  have hd : ℒₛₑₜ-relation₅[V] (fun Y κ U f i ↦ ∀ a, a ∈ Y ↔ a ∈ κ ∧
    (coordinateFiber κ f i ∈ U → i ∈ f ‘ a) ∧ (coordinateFiber κ f i ∉ U → i ∉ f ‘ a)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coordinateChoice (v 1) (v 2) (v 3) (v 4) ↔ _
  rw [mem_ext_iff]
  simp only [coordinateChoice, mem_sep_iff]

theorem compositeFiberComplement_definable_one (κ e g : V) :
    ℒₛₑₜ-function₁[V] (compositeFiberComplement κ e g) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y i ↦ ∀ a,
    a ∈ Y ↔ a ∈ κ ∧ ¬(a ∈ κ ∧ e ‘ (g ‘ a) = i)) := by definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = compositeFiberComplement κ e g (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [compositeFiberComplement, mem_relativeComplement_iff, mem_sep_iff]

theorem coordinateChoice_definable_one (κ U f : V) :
    ℒₛₑₜ-function₁[V] (coordinateChoice κ U f) := by
  have hd : ℒₛₑₜ-relation[V] (fun Y i ↦ ∀ a, a ∈ Y ↔ a ∈ κ ∧
    (coordinateFiber κ f i ∈ U → i ∈ f ‘ a) ∧ (coordinateFiber κ f i ∉ U → i ∉ f ‘ a)) := by
    definability
  apply Language.Definable.of_iff hd
  intro v
  change v 0 = coordinateChoice κ U f (v 1) ↔ _
  rw [mem_ext_iff]
  simp only [coordinateChoice, mem_sep_iff]

theorem IsSetUltrafilter.empty_not_mem {K U : V} (h : IsSetUltrafilter K U) : (∅ : V) ∉ U :=
  h.2.2.1

theorem IsSetUltrafilter.upward {K U X Y : V} (h : IsSetUltrafilter K U) (hX : X ∈ U)
    (hY : Y ⊆ K) (hXY : X ⊆ Y) : Y ∈ U :=
  h.2.2.2.1 X hX Y hY hXY

theorem IsSetUltrafilter.inter {K U X Y : V} (h : IsSetUltrafilter K U) (hX : X ∈ U)
    (hY : Y ∈ U) : X ∩ Y ∈ U :=
  h.2.2.2.2.1 X hX Y hY

theorem IsSetUltrafilter.dichotomy {K U X : V} (h : IsSetUltrafilter K U) (hX : X ⊆ K) :
    X ∈ U ∨ relativeComplement K X ∈ U :=
  h.2.2.2.2.2 X hX

theorem IsSetUltrafilter.subset_of_mem {K U X : V} (h : IsSetUltrafilter K U) (hX : X ∈ U) :
    X ⊆ K :=
  mem_power_iff.mp (h.1 X hX)

theorem IsSetUltrafilter.nonempty_of_mem {K U X : V} (h : IsSetUltrafilter K U) (hX : X ∈ U) :
    ∃ z, z ∈ X := by
  by_contra hno
  push Not at hno
  have : X = ∅ := by
    ext z
    simp [hno z]
  exact h.empty_not_mem (this ▸ hX)

theorem IsSetUltrafilter.not_mem_of_complement_mem {K U X : V} (h : IsSetUltrafilter K U)
    (hc : relativeComplement K X ∈ U) : X ∉ U := by
  intro hX
  have hi := h.inter hX hc
  obtain ⟨z, hz⟩ := h.nonempty_of_mem hi
  rw [mem_inter_iff, mem_relativeComplement_iff] at hz
  exact hz.2.2 hz.1

/-- A map from `κ` into a set of size below `κ` has a fiber in `U`. -/
theorem ultrafilter_fiber_mem {κ U B lam g : V} (hU : IsNonprincipalSetUltrafilter κ U)
    (hc : IsOrdinalComplete κ U) (hlam : lam ∈ κ) (hB : B ≤# lam) (hg : g ∈ B ^ κ) :
    ∃ b ∈ B, {a ∈ κ ; g ‘ a = b} ∈ U := by
  by_contra hno
  push Not at hno
  obtain ⟨e, he, hinj⟩ := hB
  let := IsFunction.of_mem he
  let := IsFunction.of_mem hg
  have hde : domain e = B := domain_eq_of_mem_function he
  have hF := compositeFiberComplement_definable_one κ e g
  let Y := definableGraph lam (compositeFiberComplement κ e g) hF
  have hFi : ∀ i ∈ lam, compositeFiberComplement κ e g i ∈ U := by
    intro i hi
    have hsub : {a ∈ κ ; e ‘ (g ‘ a) = i} ⊆ κ := sep_subset
    rcases hU.1.dichotomy hsub with hin | hout
    · exfalso
      obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem hin
      obtain ⟨haκ, hai⟩ := mem_sep_iff.mp ha
      have hb : g ‘ a ∈ B := function_value_mem hg haκ
      apply hno (g ‘ a) hb
      have : {a' ∈ κ ; e ‘ (g ‘ a') = i} = {a' ∈ κ ; g ‘ a' = g ‘ a} := by
        ext a'
        simp only [mem_sep_iff]
        constructor
        · rintro ⟨ha', hai'⟩
          refine ⟨ha', ?_⟩
          have hb' : g ‘ a' ∈ B := function_value_mem hg ha'
          have h1 : ⟨g ‘ a', e ‘ (g ‘ a')⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hb')
          have h2 : ⟨g ‘ a, e ‘ (g ‘ a)⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact hb)
          rw [hai'] at h1
          rw [hai] at h2
          exact hinj _ _ i h1 h2
        · rintro ⟨ha', hab'⟩
          exact ⟨ha', by rw [hab', hai]⟩
      rw [← this]
      exact hin
    · exact hout
  have hY : Y ∈ U ^ lam := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function lam _ hF)
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hy
    exact hFi i hi
  have hZ := hc lam hlam Y hY
  have hempty : indexedIntersection κ lam Y = ∅ := by
    ext a
    simp only [mem_indexedIntersection_iff, not_mem_empty, iff_false, not_and, not_forall]
    intro ha
    have hb : g ‘ a ∈ B := function_value_mem hg ha
    have hi : e ‘ (g ‘ a) ∈ lam := function_value_mem he hb
    refine ⟨e ‘ (g ‘ a), hi, ?_⟩
    rw [value_definableGraph lam _ hF hi]
    intro hmem
    unfold compositeFiberComplement at hmem
    rw [mem_relativeComplement_iff] at hmem
    exact hmem.2 (mem_sep_iff.mpr ⟨ha, rfl⟩)
  rw [hempty] at hZ
  exact hU.1.empty_not_mem hZ

/-- A measurable ordinal is a strong limit: no smaller power set injects `κ`. -/
theorem measurable_not_cardLE_power {κ U lam : V} (hU : IsNonprincipalSetUltrafilter κ U)
    (hc : IsOrdinalComplete κ U) (hlam : lam ∈ κ) : ¬κ ≤# ℘ lam := by
  rintro ⟨f, hf, hinj⟩
  let := IsFunction.of_mem hf
  have hdf : domain f = κ := domain_eq_of_mem_function hf
  have hF := coordinateChoice_definable_one κ U f
  let Y := definableGraph lam (coordinateChoice κ U f) hF
  have hFi : ∀ i ∈ lam, coordinateChoice κ U f i ∈ U := by
    intro i _
    by_cases hX : coordinateFiber κ f i ∈ U
    · have : coordinateChoice κ U f i = coordinateFiber κ f i := by
        ext a
        simp only [coordinateChoice, coordinateFiber, mem_sep_iff]
        constructor
        · rintro ⟨ha, h1, _⟩
          exact ⟨ha, h1 hX⟩
        · rintro ⟨ha, h1⟩
          exact ⟨ha, fun _ ↦ h1, fun h ↦ (h hX).elim⟩
      rw [this]
      exact hX
    · rcases hU.1.dichotomy (show coordinateFiber κ f i ⊆ κ from sep_subset) with h | h
      · exact (hX h).elim
      · have : coordinateChoice κ U f i = relativeComplement κ (coordinateFiber κ f i) := by
          ext a
          simp only [coordinateChoice, coordinateFiber, mem_sep_iff, mem_relativeComplement_iff]
          constructor
          · rintro ⟨ha, _, h2⟩
            exact ⟨ha, fun h' ↦ h2 hX h'.2⟩
          · rintro ⟨ha, h2⟩
            exact ⟨ha, fun h' ↦ (hX h').elim, fun _ h' ↦ h2 ⟨ha, h'⟩⟩
        rw [this]
        exact h
  have hY : Y ∈ U ^ lam := by
    apply mem_function_of_mem_function_of_subset (definableGraph_mem_function lam _ hF)
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (repl_spec hF).mp hy
    exact hFi i hi
  have hZ := hc lam hlam Y hY
  obtain ⟨a, ha⟩ := hU.1.nonempty_of_mem hZ
  have haκ : a ∈ κ := (mem_indexedIntersection_iff _ _ _ _).mp ha |>.1
  -- every member of the intersection equals `a`
  have hsingle : indexedIntersection κ lam Y ⊆ ({a} : V) := by
    intro a' ha'
    rw [mem_indexedIntersection_iff] at ha ha'
    have hfa : f ‘ a ∈ ℘ lam := function_value_mem hf haκ
    have hfa' : f ‘ a' ∈ ℘ lam := function_value_mem hf ha'.1
    have heq : f ‘ a' = f ‘ a := by
      ext i
      constructor
      · intro hi
        have hil : i ∈ lam := mem_power_iff.mp hfa' _ hi
        have h1 := ha.2 i hil
        have h2 := ha'.2 i hil
        rw [value_definableGraph lam _ hF hil] at h1 h2
        simp only [coordinateChoice, coordinateFiber, mem_sep_iff] at h1 h2
        by_contra hni
        exact h2.2.2 (fun hX ↦ hni (h1.2.1 hX)) hi
      · intro hi
        have hil : i ∈ lam := mem_power_iff.mp hfa _ hi
        have h1 := ha.2 i hil
        have h2 := ha'.2 i hil
        rw [value_definableGraph lam _ hF hil] at h1 h2
        simp only [coordinateChoice, coordinateFiber, mem_sep_iff] at h1 h2
        by_contra hni
        exact h1.2.2 (fun hX ↦ hni (h2.2.1 hX)) hi
    have h1 : ⟨a', f ‘ a'⟩ₖ ∈ f := kpair_value_mem (by rw [hdf]; exact ha'.1)
    have h2 : ⟨a, f ‘ a⟩ₖ ∈ f := kpair_value_mem (by rw [hdf]; exact haκ)
    rw [heq] at h1
    rw [hinj a' a _ h1 h2]
    simp
  have hsa : ({a} : V) ∈ U :=
    hU.1.upward hZ (by intro z hz; rw [mem_singleton_iff] at hz; exact hz ▸ haκ) hsingle
  exact hU.2 a haκ hsa

/-- Images of a set under an injection are injective on subsets. -/
theorem power_cardLE_of_cardLE {P lam : V} (h : P ≤# lam) : ℘ P ≤# ℘ lam := by
  obtain ⟨e, he, hinj⟩ := h
  let := IsFunction.of_mem he
  have hde : domain e = P := domain_eq_of_mem_function he
  let F : V → V := fun X ↦ ordinalImage e X
  have hF : ℒₛₑₜ-function₁ F := by definability
  refine ⟨definableGraph (℘ P) F hF, ?_, ?_⟩
  · apply mem_function_of_mem_function_of_subset (definableGraph_mem_function (℘ P) F hF)
    intro y hy
    obtain ⟨X, hX, rfl⟩ := (repl_spec hF).mp hy
    apply mem_power_iff.mpr
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_ordinalImage e X z).mp hz
    exact function_value_mem he (mem_power_iff.mp hX _ hx)
  · intro X₁ X₂ y h₁ h₂
    have hX₁ := (pair_mem_definableGraph_iff (℘ P) F hF X₁ y).mp h₁
    have hX₂ := (pair_mem_definableGraph_iff (℘ P) F hF X₂ y).mp h₂
    have key : ∀ X₁ X₂ : V, X₁ ∈ ℘ P → X₂ ∈ ℘ P → F X₁ = F X₂ → X₁ ⊆ X₂ := by
      intro X₁ X₂ hX₁ hX₂ heq x hx
      have hx' : e ‘ x ∈ F X₂ := by
        rw [← heq]
        exact (mem_ordinalImage e X₁ _).mpr ⟨x, hx, rfl⟩
      obtain ⟨x', hx', hxx'⟩ := (mem_ordinalImage e X₂ _).mp hx'
      have h1 : ⟨x, e ‘ x⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact mem_power_iff.mp hX₁ _ hx)
      have h2 : ⟨x', e ‘ x'⟩ₖ ∈ e := kpair_value_mem (by rw [hde]; exact mem_power_iff.mp hX₂ _ hx')
      rw [← hxx'] at h2
      rw [hinj x x' _ h1 h2]
      exact hx'
    apply SetTheory.subset_antisymm
    · exact key X₁ X₂ hX₁.1 hX₂.1 (hX₁.2.symm.trans hX₂.2)
    · exact key X₂ X₁ hX₂.1 hX₁.1 (hX₂.2.symm.trans hX₁.2)

/-- Under Choice, the power set of an ordinal below a measurable ordinal is bounded in size
by an ordinal below it. -/
theorem measurable_power_bounded (hAC : InternalChoice V) {κ U lam : V} [IsOrdinal κ]
    (hU : IsNonprincipalSetUltrafilter κ U) (hc : IsOrdinalComplete κ U) (hlam : lam ∈ κ) :
    ∃ μ ∈ κ, ℘ lam ≤# μ := by
  have hwo := wellOrderable_of_internalChoice hAC (℘ lam)
  have hμ := wellOrderedCardinal_initial hwo
  have hμeq := wellOrderedCardinal_cardEQ hwo
  let := hμ.1
  rcases IsOrdinal.mem_trichotomy (α := wellOrderedCardinal (℘ lam)) (β := κ) with h | h | h
  · exact ⟨_, h, hμeq.ge⟩
  · exact (measurable_not_cardLE_power hU hc hlam (h ▸ hμeq.le)).elim
  · exact (measurable_not_cardLE_power hU hc hlam
      ((cardLE_of_subset (IsTransitive.transitive _ h)).trans hμeq.le)).elim

end ZFVP
