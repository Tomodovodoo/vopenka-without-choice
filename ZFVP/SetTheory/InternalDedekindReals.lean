import ZFVP.SetTheory.InternalRationalOrder

/-! Dedekind reals formed inside an arbitrary first-order ZF model. The cuts
are subsets of the actual internal rational quotient, and their completeness
is for internal sets of cuts. No external completeness of the model is used. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def isDedekindCutFormula : SetTheorySemisentence 1 :=
  f“x. x ⊆ !internalRationalsFormula ∧ !isNonempty x ∧
    (∃ q ∈ !internalRationalsFormula, q ∉ x) ∧
    (∀ q ∈ x, ∀ r ∈ !internalRationalsFormula, !internalRationalLTFormula r q → r ∈ x) ∧
    ∀ q ∈ x, ∃ r ∈ x, !internalRationalLTFormula q r”

def dedekindRealsFormula : SetTheorySemisentence 1 :=
  f“R. ∀ x, x ∈ R ↔ !isDedekindCutFormula x”

def rationalCutFormula : SetTheorySemisentence 2 :=
  f“x q. ∀ r, r ∈ x ↔ r ∈ !internalRationalsFormula ∧ !internalRationalLTFormula r q”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

def IsDedekindCut (x : V) : Prop :=
  x ⊆ internalRationals V ∧ IsNonempty x ∧
    (∃ q ∈ internalRationals V, q ∉ x) ∧
    (∀ q ∈ x, ∀ r ∈ internalRationals V, InternalRationalLT r q → r ∈ x) ∧
    ∀ q ∈ x, ∃ r ∈ x, InternalRationalLT q r

instance isDedekindCutFormula_defined :
    ℒₛₑₜ-predicate[V] IsDedekindCut via isDedekindCutFormula :=
  ⟨fun v ↦ by simp [isDedekindCutFormula, IsDedekindCut]⟩

instance isDedekindCut_definable : ℒₛₑₜ-predicate[V] IsDedekindCut :=
  isDedekindCutFormula_defined.to_definable

noncomputable def dedekindReals (V : Type*) [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V := {x ∈ power (internalRationals V) ; IsDedekindCut x}

theorem mem_dedekindReals_iff (x : V) : x ∈ dedekindReals V ↔ IsDedekindCut x := by
  simp only [dedekindReals, mem_sep_iff, mem_power_iff]
  exact ⟨And.right, fun h ↦ ⟨h.1, h⟩⟩

instance dedekindRealsFormula_defined :
    ℒₛₑₜ-function₀[V] (dedekindReals V) via dedekindRealsFormula :=
  ⟨fun v ↦ by simp [dedekindRealsFormula, mem_ext_iff (y := dedekindReals V),
    mem_dedekindReals_iff]⟩

noncomputable def rationalCut (q : V) : V :=
  {r ∈ internalRationals V ; InternalRationalLT r q}

theorem mem_rationalCut_iff (q r : V) :
    r ∈ rationalCut q ↔ r ∈ internalRationals V ∧ InternalRationalLT r q := by
  simp [rationalCut]

instance rationalCutFormula_defined :
    ℒₛₑₜ-function₁[V] rationalCut via rationalCutFormula :=
  ⟨fun v ↦ by simp [rationalCutFormula, mem_ext_iff (y := rationalCut _),
    mem_rationalCut_iff]⟩

instance rationalCut_definable : ℒₛₑₜ-function₁[V] rationalCut :=
  rationalCutFormula_defined.to_definable

theorem rationalCut_isCut {q : V} (hq : q ∈ internalRationals V) : IsDedekindCut (rationalCut q) := by
  refine ⟨fun r hr ↦ ((mem_rationalCut_iff q r).mp hr).1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr, hrq⟩ := (internalRational_noEndpoints hq).1
    exact ⟨r, (mem_rationalCut_iff q r).mpr ⟨hr, hrq⟩⟩
  · exact ⟨q, hq, fun h ↦ internalRationalLT_irrefl hq ((mem_rationalCut_iff q q).mp h).2⟩
  · intro r hr s hs hsr
    obtain ⟨hrQ, hrq⟩ := (mem_rationalCut_iff q r).mp hr
    exact (mem_rationalCut_iff q s).mpr ⟨hs, internalRationalLT_trans hs hrQ hq hsr hrq⟩
  · intro r hr
    obtain ⟨hrQ, hrq⟩ := (mem_rationalCut_iff q r).mp hr
    obtain ⟨s, hs, hrs, hsq⟩ := internalRational_dense hrQ hq hrq
    exact ⟨s, (mem_rationalCut_iff q s).mpr ⟨hs, hsq⟩, hrs⟩

theorem rationalCut_mem_reals {q : V} (hq : q ∈ internalRationals V) :
    rationalCut q ∈ dedekindReals V := (mem_dedekindReals_iff _).mpr (rationalCut_isCut hq)

theorem dedekindCuts_comparable {x y : V} (hx : IsDedekindCut x) (hy : IsDedekindCut y) :
    x ⊆ y ∨ y ⊆ x := by
  classical
  by_cases hxy : x ⊆ y
  · exact Or.inl hxy
  · have hw : ∃ p, p ∈ x ∧ p ∉ y := by
      simpa only [subset_def, not_forall, exists_prop] using hxy
    obtain ⟨p, hpx, hpy⟩ := hw
    right
    intro q hqy
    rcases internalRational_trichotomy (hy.1 q hqy) (hx.1 p hpx) with hqp | hqp | hpq
    · exact hx.2.2.2.1 p hpx q (hy.1 q hqy) hqp
    · exact (hpy (hqp ▸ hqy)).elim
    · exact (hpy (hy.2.2.2.1 q hqy p (hx.1 p hpx) hpq)).elim

def DedekindLT (x y : V) : Prop := x ⊊ y

instance dedekindLT_definable : ℒₛₑₜ-relation[V] DedekindLT := by
  unfold DedekindLT
  definability

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem dedekindLT_iff (x y : V) : DedekindLT x y ↔ x ⊆ y ∧ x ≠ y := Iff.rfl

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem dedekindLT_irrefl (x : V) : ¬ DedekindLT x x := SSubset.irrefl x

theorem dedekindLT_trans {x y z : V} (hxy : DedekindLT x y) (hyz : DedekindLT y z) :
    DedekindLT x z := by
  refine ⟨subset_trans hxy.1 hyz.1, ?_⟩
  intro h
  exact hxy.2 (subset_antisymm hxy.1 (h.symm ▸ hyz.1))

theorem dedekindLT_of_mem_not_mem {x y p : V} (hx : IsDedekindCut x) (hy : IsDedekindCut y)
    (hpy : p ∈ y) (hpx : p ∉ x) : DedekindLT x y := by
  have hsub : x ⊆ y := (dedekindCuts_comparable hx hy).resolve_right (fun h ↦ hpx (h p hpy))
  exact ⟨hsub, fun he ↦ hpx (he.symm ▸ hpy)⟩

theorem dedekindLT_has_gap {x y : V} (hxy : DedekindLT x y) : ∃ p, p ∈ y ∧ p ∉ x := by
  classical
  by_contra h
  have hyx : y ⊆ x := by simpa only [not_exists, not_and, not_not, ← subset_def] using h
  exact hxy.2 (subset_antisymm hxy.1 hyx)

theorem dedekindCut_le_rationalCut_of_not_mem {x q : V} (hx : IsDedekindCut x)
    (hq : q ∈ internalRationals V) (hqx : q ∉ x) : x ⊆ rationalCut q := by
  intro r hr
  refine (mem_rationalCut_iff q r).mpr ⟨hx.1 r hr, ?_⟩
  rcases internalRational_trichotomy (hx.1 r hr) hq with hrq | he | hqr
  · exact hrq
  · exact (hqx (he ▸ hr)).elim
  · exact (hqx (hx.2.2.2.1 r hr q hq hqr)).elim

theorem rationalCut_lt_iff_mem {x q : V} (hx : IsDedekindCut x)
    (hq : q ∈ internalRationals V) : DedekindLT (rationalCut q) x ↔ q ∈ x := by
  constructor
  · intro h
    by_contra hqx
    exact h.2 (subset_antisymm h.1 (dedekindCut_le_rationalCut_of_not_mem hx hq hqx))
  · intro hqx
    have hsub : rationalCut q ⊆ x := by
      intro r hr
      obtain ⟨hrQ, hrq⟩ := (mem_rationalCut_iff q r).mp hr
      exact hx.2.2.2.1 q hqx r hrQ hrq
    refine ⟨hsub, ?_⟩
    intro h
    have hqcut : q ∈ rationalCut q := h.symm ▸ hqx
    exact internalRationalLT_irrefl hq ((mem_rationalCut_iff q q).mp hqcut).2

theorem rationalCut_lt_iff {q r : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) :
    DedekindLT (rationalCut q) (rationalCut r) ↔ InternalRationalLT q r := by
  rw [rationalCut_lt_iff_mem (rationalCut_isCut hr) hq, mem_rationalCut_iff]
  exact and_iff_right hq

theorem rationalCut_injective {q r : V} (hq : q ∈ internalRationals V)
    (hr : r ∈ internalRationals V) (h : rationalCut q = rationalCut r) : q = r := by
  rcases internalRational_trichotomy hq hr with hqr | he | hrq
  · have hh := (rationalCut_lt_iff hq hr).mpr hqr
    rw [h] at hh
    exact (dedekindLT_irrefl _ hh).elim
  · exact he
  · have hh := (rationalCut_lt_iff hr hq).mpr hrq
    rw [h] at hh
    exact (dedekindLT_irrefl _ hh).elim

theorem rationalCuts_dense {x y : V} (hx : IsDedekindCut x) (hy : IsDedekindCut y)
    (hxy : DedekindLT x y) : ∃ q ∈ internalRationals V,
      DedekindLT x (rationalCut q) ∧ DedekindLT (rationalCut q) y := by
  obtain ⟨p, hpy, hpx⟩ := dedekindLT_has_gap hxy
  obtain ⟨q, hqy, hpq⟩ := hy.2.2.2.2 p hpy
  have hqQ := hy.1 q hqy
  refine ⟨q, hqQ, ?_, (rationalCut_lt_iff_mem hy hqQ).mpr hqy⟩
  exact dedekindLT_of_mem_not_mem hx (rationalCut_isCut hqQ)
    ((mem_rationalCut_iff q p).mpr ⟨hy.1 p hpy, hpq⟩) hpx

theorem dedekindCuts_noEndpoints {x : V} (hx : IsDedekindCut x) :
    (∃ q ∈ internalRationals V, DedekindLT (rationalCut q) x) ∧
      ∃ r ∈ internalRationals V, DedekindLT x (rationalCut r) := by
  constructor
  · obtain ⟨q, hqx⟩ := hx.2.1.nonempty
    exact ⟨q, hx.1 q hqx, (rationalCut_lt_iff_mem hx (hx.1 q hqx)).mpr hqx⟩
  · obtain ⟨q, hqQ, hqx⟩ := hx.2.2.1
    obtain ⟨r, hrQ, hqr⟩ := (internalRational_noEndpoints hqQ).2
    exact ⟨r, hrQ, dedekindLT_of_mem_not_mem hx (rationalCut_isCut hrQ)
      ((mem_rationalCut_iff r q).mpr ⟨hqQ, hqr⟩) hqx⟩

theorem dedekindCut_sUnion {A b : V} (hA : A ⊆ dedekindReals V) (hne : IsNonempty A)
    (hb : IsDedekindCut b) (hub : ∀ x ∈ A, x ⊆ b) : IsDedekindCut (⋃ˢ A) := by
  have hsub : ⋃ˢ A ⊆ b := by
    intro q hq
    obtain ⟨x, hxA, hqx⟩ := mem_sUnion_iff.mp hq
    exact hub x hxA q hqx
  refine ⟨subset_trans hsub hb.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hxA⟩ := hne.nonempty
    obtain ⟨q, hqx⟩ := ((mem_dedekindReals_iff x).mp (hA x hxA)).2.1.nonempty
    exact ⟨q, mem_sUnion_iff.mpr ⟨x, hxA, hqx⟩⟩
  · obtain ⟨q, hqQ, hqb⟩ := hb.2.2.1
    exact ⟨q, hqQ, fun h ↦ hqb (hsub q h)⟩
  · intro q hq r hrQ hrq
    obtain ⟨x, hxA, hqx⟩ := mem_sUnion_iff.mp hq
    have hx := (mem_dedekindReals_iff x).mp (hA x hxA)
    exact mem_sUnion_iff.mpr ⟨x, hxA, hx.2.2.2.1 q hqx r hrQ hrq⟩
  · intro q hq
    obtain ⟨x, hxA, hqx⟩ := mem_sUnion_iff.mp hq
    have hx := (mem_dedekindReals_iff x).mp (hA x hxA)
    obtain ⟨r, hrx, hqr⟩ := hx.2.2.2.2 q hqx
    exact ⟨r, mem_sUnion_iff.mpr ⟨x, hxA, hrx⟩, hqr⟩

theorem dedekindReals_complete {A b : V} (hA : A ⊆ dedekindReals V) (hne : IsNonempty A)
    (hb : b ∈ dedekindReals V) (hub : ∀ x ∈ A, x ⊆ b) :
    ∃ s ∈ dedekindReals V, (∀ x ∈ A, x ⊆ s) ∧
      ∀ c ∈ dedekindReals V, (∀ x ∈ A, x ⊆ c) → s ⊆ c := by
  refine ⟨⋃ˢ A, (mem_dedekindReals_iff _).mpr
    (dedekindCut_sUnion hA hne ((mem_dedekindReals_iff b).mp hb) hub), ?_, ?_⟩
  · intro x hxA q hqx
    exact mem_sUnion_iff.mpr ⟨x, hxA, hqx⟩
  · intro c _ hc q hq
    obtain ⟨x, hxA, hqx⟩ := mem_sUnion_iff.mp hq
    exact hc x hxA q hqx

end ZFVP
