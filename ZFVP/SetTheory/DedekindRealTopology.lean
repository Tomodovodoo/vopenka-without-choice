import ZFVP.SetTheory.InternalDedekindReals
import ZFVP.SetTheory.InternalRationalField

/-! The rational interval basis on the actual internal Dedekind real line. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def dedekindLTFormula : SetTheorySemisentence 2 := f“x y. x ⊆ y ∧ x ≠ y”

def realIntervalFormula : SetTheorySemisentence 3 :=
  f“U a b. ∀ x, x ∈ U ↔ !isDedekindCutFormula x ∧
    !dedekindLTFormula (!rationalCutFormula a) x ∧ !dedekindLTFormula x (!rationalCutFormula b)”

def realBasicCodesFormula : SetTheorySemisentence 1 :=
  f“B. ∀ p, p ∈ B ↔ p ∈ !prod.dfn (!internalRationalsFormula) (!internalRationalsFormula) ∧
    !internalRationalLTFormula (!kpair.π₁.dfn p) (!kpair.π₂.dfn p)”

def realOpenFromFormula : SetTheorySemisentence 2 :=
  f“U S. ∀ x, x ∈ U ↔ !isDedekindCutFormula x ∧
    ∃ p ∈ S, x ∈ !realIntervalFormula (!kpair.π₁.dfn p) (!kpair.π₂.dfn p)”

def isRealOpenFormula : SetTheorySemisentence 1 :=
  f“U. ∃ S, S ⊆ !realBasicCodesFormula ∧ U = !realOpenFromFormula S”

def realClosedFromFormula : SetTheorySemisentence 2 :=
  f“F S. F = !sdiff.dfn (!dedekindRealsFormula) (!realOpenFromFormula S)”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

instance dedekindLTFormula_defined : ℒₛₑₜ-relation[V] DedekindLT via dedekindLTFormula :=
  ⟨fun v ↦ by simp [dedekindLTFormula, dedekindLT_iff]⟩

noncomputable def realInterval (a b : V) : V :=
  {x ∈ dedekindReals V ; DedekindLT (rationalCut a) x ∧ DedekindLT x (rationalCut b)}

theorem mem_realInterval_iff (a b x : V) : x ∈ realInterval a b ↔
    IsDedekindCut x ∧ DedekindLT (rationalCut a) x ∧ DedekindLT x (rationalCut b) := by
  simp [realInterval, mem_dedekindReals_iff]

instance realIntervalFormula_defined : ℒₛₑₜ-function₂[V] realInterval via realIntervalFormula :=
  ⟨fun v ↦ by simp [realIntervalFormula, mem_ext_iff (y := realInterval _ _), mem_realInterval_iff]⟩

instance realInterval_definable : ℒₛₑₜ-function₂[V] realInterval := realIntervalFormula_defined.to_definable

noncomputable def realBasicCodes (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V :=
  {p ∈ (internalRationals V) ×ˢ (internalRationals V) ; InternalRationalLT (kpair.π₁ p) (kpair.π₂ p)}

theorem mem_realBasicCodes_iff (p : V) : p ∈ realBasicCodes V ↔
    p ∈ (internalRationals V) ×ˢ (internalRationals V) ∧
      InternalRationalLT (kpair.π₁ p) (kpair.π₂ p) := by
  simp [realBasicCodes]

theorem pair_mem_realBasicCodes_iff (a b : V) : ⟨a, b⟩ₖ ∈ realBasicCodes V ↔
    a ∈ internalRationals V ∧ b ∈ internalRationals V ∧ InternalRationalLT a b := by
  simp [mem_realBasicCodes_iff, and_assoc]

instance realBasicCodesFormula_defined : ℒₛₑₜ-function₀[V] (realBasicCodes V) via realBasicCodesFormula :=
  ⟨fun v ↦ by simp [realBasicCodesFormula, mem_ext_iff (y := realBasicCodes V), mem_realBasicCodes_iff]⟩

noncomputable def realOpenFrom (S : V) : V :=
  {x ∈ dedekindReals V ; ∃ p ∈ S, x ∈ realInterval (kpair.π₁ p) (kpair.π₂ p)}

theorem mem_realOpenFrom_iff (S x : V) : x ∈ realOpenFrom S ↔
    IsDedekindCut x ∧ ∃ p ∈ S, x ∈ realInterval (kpair.π₁ p) (kpair.π₂ p) := by
  simp [realOpenFrom, mem_dedekindReals_iff]

instance realOpenFromFormula_defined : ℒₛₑₜ-function₁[V] realOpenFrom via realOpenFromFormula :=
  ⟨fun v ↦ by simp [realOpenFromFormula, mem_ext_iff (y := realOpenFrom _), mem_realOpenFrom_iff]⟩

instance realOpenFrom_definable : ℒₛₑₜ-function₁[V] realOpenFrom := realOpenFromFormula_defined.to_definable

def IsRealOpen (U : V) : Prop := ∃ S, S ⊆ realBasicCodes V ∧ U = realOpenFrom S

instance isRealOpenFormula_defined : ℒₛₑₜ-predicate[V] IsRealOpen via isRealOpenFormula :=
  ⟨fun v ↦ by simp [isRealOpenFormula, IsRealOpen]⟩

instance isRealOpen_definable : ℒₛₑₜ-predicate[V] IsRealOpen := isRealOpenFormula_defined.to_definable

noncomputable def realClosedFrom (S : V) : V := (dedekindReals V) \ realOpenFrom S

theorem mem_realClosedFrom_iff (S x : V) : x ∈ realClosedFrom S ↔
    IsDedekindCut x ∧ x ∉ realOpenFrom S := by
  simp [realClosedFrom, mem_dedekindReals_iff]

instance realClosedFromFormula_defined : ℒₛₑₜ-function₁[V] realClosedFrom via realClosedFromFormula :=
  ⟨fun v ↦ by simp [realClosedFromFormula, realClosedFrom]⟩

instance realClosedFrom_definable : ℒₛₑₜ-function₁[V] realClosedFrom := realClosedFromFormula_defined.to_definable

theorem dedekindLT_of_subset_of_lt {x y z : V} (hxy : x ⊆ y) (hyz : DedekindLT y z) :
    DedekindLT x z := by
  refine ⟨subset_trans hxy hyz.1, ?_⟩
  intro h
  exact hyz.2 (SetTheory.subset_antisymm hyz.1 (h ▸ hxy))

theorem dedekindLT_of_lt_of_subset {x y z : V} (hxy : DedekindLT x y) (hyz : y ⊆ z) :
    DedekindLT x z := by
  refine ⟨subset_trans hxy.1 hyz, ?_⟩
  intro h
  exact hxy.2 (SetTheory.subset_antisymm hxy.1 (h.symm ▸ hyz))

namespace InternalRational

theorem rationalCut_mono {a b : InternalRational V} (hab : a ≤ b) : rationalCut a.val ⊆ rationalCut b.val := by
  intro r hr
  obtain ⟨hrQ, hra⟩ := (mem_rationalCut_iff _ _).mp hr
  have h : (⟨r, hrQ⟩ : InternalRational V) < b := lt_of_lt_of_le hra hab
  exact (mem_rationalCut_iff _ _).mpr ⟨hrQ, h⟩

theorem le_of_rationalCut_subset {a b : InternalRational V} (hab : rationalCut a.val ⊆ rationalCut b.val) :
    a ≤ b := by
  intro hba
  have h := hab b.val ((mem_rationalCut_iff _ _).mpr ⟨b.property, hba⟩)
  exact internalRationalLT_irrefl b.property ((mem_rationalCut_iff _ _).mp h).2

theorem rationalCut_subset_iff {a b : InternalRational V} : rationalCut a.val ⊆ rationalCut b.val ↔ a ≤ b :=
  ⟨le_of_rationalCut_subset, rationalCut_mono⟩

end InternalRational

theorem realInterval_subset_reals (a b : V) : realInterval a b ⊆ dedekindReals V :=
  fun _ hx ↦ (mem_dedekindReals_iff _).mpr ((mem_realInterval_iff _ _ _).mp hx).1

theorem realOpenFrom_subset_reals (S : V) : realOpenFrom S ⊆ dedekindReals V :=
  fun _ hx ↦ (mem_dedekindReals_iff _).mpr ((mem_realOpenFrom_iff _ _).mp hx).1

theorem realOpenFrom_interval {S p : V} (hp : p ∈ S) :
    realInterval (kpair.π₁ p) (kpair.π₂ p) ⊆ realOpenFrom S := by
  intro x hx
  exact (mem_realOpenFrom_iff _ _).mpr ⟨((mem_realInterval_iff _ _ _).mp hx).1, p, hp, hx⟩

theorem realOpenFrom_isOpen {S : V} (hS : S ⊆ realBasicCodes V) : IsRealOpen (realOpenFrom S) :=
  ⟨S, hS, rfl⟩

theorem realOpen_neighborhood {U x : V} (hU : IsRealOpen U) (hx : x ∈ U) :
    ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
      InternalRationalLT a b ∧ x ∈ realInterval a b ∧ realInterval a b ⊆ U := by
  obtain ⟨S, hS, rfl⟩ := hU
  obtain ⟨_, p, hp, hxp⟩ := (mem_realOpenFrom_iff S x).mp hx
  obtain ⟨hpp, hlt⟩ := (mem_realBasicCodes_iff p).mp (hS p hp)
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod_iff.mp hpp
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hlt hxp
  refine ⟨a, ha, b, hb, hlt, hxp, ?_⟩
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using realOpenFrom_interval hp

noncomputable def realInteriorCode (U : V) : V :=
  {p ∈ realBasicCodes V ; realInterval (kpair.π₁ p) (kpair.π₂ p) ⊆ U}

instance realInteriorCode_definable : ℒₛₑₜ-function₁[V] realInteriorCode := by
  have h : ℒₛₑₜ-relation (fun S U : V ↦ ∀ p, p ∈ S ↔ p ∈ realBasicCodes V ∧
      realInterval (kpair.π₁ p) (kpair.π₂ p) ⊆ U) := by definability
  apply Language.Definable.of_iff h
  intro v
  rw [mem_ext_iff]
  simp [realInteriorCode]

theorem realOpen_of_neighborhoods {U : V}
    (h : ∀ x ∈ U, ∃ a ∈ internalRationals V, ∃ b ∈ internalRationals V,
      InternalRationalLT a b ∧ x ∈ realInterval a b ∧ realInterval a b ⊆ U) : IsRealOpen U := by
  refine ⟨realInteriorCode U, fun p hp ↦ (mem_sep_iff.mp hp).1, ?_⟩
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab, hxi, hiU⟩ := h x hx
    refine (mem_realOpenFrom_iff _ _).mpr ⟨((mem_realInterval_iff _ _ _).mp hxi).1, ⟨a, b⟩ₖ, ?_, ?_⟩
    · exact mem_sep_iff.mpr ⟨(pair_mem_realBasicCodes_iff a b).mpr ⟨ha, hb, hab⟩, by simpa using hiU⟩
    · simpa using hxi
  · intro hx
    obtain ⟨_, p, hp, hxi⟩ := (mem_realOpenFrom_iff _ _).mp hx
    exact (mem_sep_iff.mp hp).2 x hxi

end ZFVP
