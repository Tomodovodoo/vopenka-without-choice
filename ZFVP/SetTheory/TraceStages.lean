import ZFVP.SetTheory.StageGenericUniqueness
import ZFVP.ModelTheory.GeneratedSubalgebra

/-! The trace of a generic on a generated subalgebra, computed by an internal recursion along the
closure stages from the decisions on the generators: at each stage the complements of undecided
elements and the joins of families meeting the decided set are added. For any antichain-generic
ultrafilter agreeing with the decisions on the generators, the recursion produces exactly its
trace on each stage. Being an internal recursion, it is transported by end extensions. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem mem_sUnion_range_iff {f : V} [IsFunction f] (z : V) :
    z ∈ ⋃ˢ range f ↔ ∃ x ∈ domain f, z ∈ f ‘ x := by
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨x, hx⟩ := mem_range_iff.mp hy
    rw [← value_eq_of_kpair_mem hx] at hzy
    exact ⟨x, mem_domain_of_kpair_mem hx, hzy⟩
  · rintro ⟨x, hx, hz⟩
    exact ⟨f ‘ x, mem_range_of_kpair_mem (kpair_value_mem hx), hz⟩

theorem mem_sUnion_range_restrict_iff {f : V} [IsFunction f] (A z : V) :
    z ∈ ⋃ˢ range (f ↾ A) ↔ ∃ x ∈ A, x ∈ domain f ∧ z ∈ f ‘ x := by
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨x, hx⟩ := mem_range_iff.mp hy
    obtain ⟨hxf, hxA⟩ := kpair_mem_restrict_iff.mp hx
    rw [← value_eq_of_kpair_mem hxf] at hzy
    exact ⟨x, hxA, mem_domain_of_kpair_mem hxf, hzy⟩
  · rintro ⟨x, hxA, hx, hz⟩
    exact ⟨f ‘ x, mem_range_of_kpair_mem (kpair_mem_restrict_iff.mpr ⟨kpair_value_mem hx, hxA⟩), hz⟩

/-- One step of the trace recursion: from the decided set `U` on the previous algebra `X`, add the
complements of the undecided elements of `X` and the joins of the families in `Ysets` inside `X`
that meet the decided set. -/
noncomputable def traceStep (P R Ysets H₀ X U : V) : V :=
  H₀ ∪ U ∪ repl (fun A ↦ forcingNegation P R A) (by definability) {A ∈ X ; A ∉ H₀ ∪ U} ∪
    repl (fun Y ↦ regularJoin P R Y) (regularJoin_definable_one P R)
      {Y ∈ Ysets ; Y ⊆ X ∧ ∃ y ∈ Y, y ∈ H₀ ∪ U}

theorem mem_traceStep_iff (P R Ysets H₀ X U d : V) :
    d ∈ traceStep P R Ysets H₀ X U ↔ d ∈ H₀ ∨ d ∈ U ∨
      (∃ A ∈ X, A ∉ H₀ ∪ U ∧ d = forcingNegation P R A) ∨
      ∃ Y ∈ Ysets, Y ⊆ X ∧ (∃ y ∈ Y, y ∈ H₀ ∪ U) ∧ d = regularJoin P R Y := by
  unfold traceStep
  rw [mem_union_iff, mem_union_iff, mem_union_iff, repl_spec, repl_spec]
  simp only [mem_sep_iff, or_assoc, and_assoc]

theorem traceStep_definable (P R Ysets H₀ : V) : ℒₛₑₜ-function₂[V] (traceStep P R Ysets H₀) := by
  have h : ℒₛₑₜ-relation₃ (fun T X U : V ↦ ∀ d, d ∈ T ↔ d ∈ H₀ ∨ d ∈ U ∨
      (∃ A ∈ X, A ∉ H₀ ∪ U ∧ d = forcingNegation P R A) ∨
      ∃ Y ∈ Ysets, Y ⊆ X ∧ (∃ y ∈ Y, y ∈ H₀ ∪ U) ∧ d = regularJoin P R Y) := by
    have := regularJoin_definable_one P R
    definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = traceStep P R Ysets H₀ (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [mem_traceStep_iff]

/-- The trace stages: the recursion along `θ` deciding each closure stage. -/
noncomputable def traceStages (P R Ysets S H₀ Cl θ : V) : V :=
  wellFoundedRecursion (membershipRelation_wellFounded θ)
    (fun α g ↦ traceStep P R Ysets H₀ (S ∪ ⋃ˢ range (Cl ↾ α)) (⋃ˢ range g))
    (by
      have := traceStep_definable P R Ysets H₀
      definability)

instance traceStages_isFunction (P R Ysets S H₀ Cl θ : V) : IsFunction (traceStages P R Ysets S H₀ Cl θ) :=
  wellFoundedRecursion_isFunction _ _ _

theorem traceStages_domain (P R Ysets S H₀ Cl θ : V) : domain (traceStages P R Ysets S H₀ Cl θ) = θ :=
  domain_wellFoundedRecursion _ _ _

theorem traceStages_value {P R Ysets S H₀ Cl θ α : V} [IsOrdinal θ] (hα : α ∈ θ) :
    (traceStages P R Ysets S H₀ Cl θ) ‘ α =
      traceStep P R Ysets H₀ (S ∪ ⋃ˢ range (Cl ↾ α))
        (⋃ˢ range ((traceStages P R Ysets S H₀ Cl θ) ↾ α)) := by
  unfold traceStages
  rw [wellFoundedRecursion_value _ _ _ hα, predecessors_membershipRelation hα]

/-- The union of the trace stages. -/
noncomputable def traceSet (P R Ysets S H₀ Cl θ : V) : V := ⋃ˢ range (traceStages P R Ysets S H₀ Cl θ)

section

variable {P R Reg MA Ysets S Cl θ U H₀ : V} (hR : IsForcingPreorder P R)
  (hsys : IsStageSystem P R Reg MA Ysets S Cl θ) (hU : IsAntichainGeneric Reg MA U)
  (hCl : ∀ α ∈ θ, S ⊆ Cl ‘ α ∧ (∀ β ∈ α, Cl ‘ β ⊆ Cl ‘ α) ∧
    (∀ A ∈ S ∪ ⋃ˢ range (Cl ↾ α), forcingNegation P R A ∈ Cl ‘ α) ∧
    ∀ Y ∈ Ysets, Y ⊆ S ∪ ⋃ˢ range (Cl ↾ α) → regularJoin P R Y ∈ Cl ‘ α)
  (hH₀ : H₀ ⊆ S) (hagree : ∀ s ∈ S, s ∈ U ↔ s ∈ H₀)

include hR hsys hU hCl hH₀ hagree in
/-- The trace recursion computes the trace of any antichain-generic ultrafilter agreeing with the
decisions on the generators. -/
theorem traceStages_eq : ∀ α ∈ θ, (traceStages P R Ysets S H₀ Cl θ) ‘ α = U ∩ Cl ‘ α := by
  have := hsys.ordinal
  have hClf := hsys.fn
  apply internalWellFounded_induction (membershipRelation_wellFounded θ)
    (fun α ↦ (traceStages P R Ysets S H₀ Cl θ) ‘ α = U ∩ Cl ‘ α) (by definability)
  intro α hα ih
  have hαθ : ∀ β ∈ α, β ∈ θ := fun β hβα ↦ IsOrdinal.toIsTransitive.mem_trans hβα hα
  have hih : ∀ β ∈ α, (traceStages P R Ysets S H₀ Cl θ) ‘ β = U ∩ Cl ‘ β := fun β hβα ↦
    ih β (hαθ β hβα) ((pair_mem_membershipRelation _ _ _).mpr ⟨hαθ β hβα, hα, hβα⟩)
  obtain ⟨X, hX⟩ : ∃ X : V, X = S ∪ ⋃ˢ range (Cl ↾ α) := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : V, U' = ⋃ˢ range ((traceStages P R Ysets S H₀ Cl θ) ↾ α) := ⟨_, rfl⟩
  have hXmem : ∀ d, d ∈ X ↔ d ∈ S ∨ ∃ β ∈ α, d ∈ Cl ‘ β := by
    intro d
    rw [hX, mem_union_iff, mem_sUnion_range_restrict_iff, hsys.dom]
    constructor
    · rintro (h | ⟨β, hβα, _, hβ⟩)
      · exact Or.inl h
      · exact Or.inr ⟨β, hβα, hβ⟩
    · rintro (h | ⟨β, hβα, hβ⟩)
      · exact Or.inl h
      · exact Or.inr ⟨β, hβα, hαθ β hβα, hβ⟩
  have hXreg : ∀ d ∈ X, d ∈ Reg := by
    intro d hd
    rcases (hXmem d).mp hd with h | ⟨β, hβα, hβ⟩
    · exact hsys.gen_reg d h
    · exact hsys.stage_reg β (hαθ β hβα) d hβ
  have hprev : ∀ d, d ∈ H₀ ∪ U' ↔ d ∈ X ∧ d ∈ U := by
    intro d
    rw [mem_union_iff, hU', mem_sUnion_range_restrict_iff, traceStages_domain, hXmem]
    constructor
    · rintro (h | ⟨β, hβα, _, hβ⟩)
      · exact ⟨Or.inl (hH₀ d h), (hagree d (hH₀ d h)).mpr h⟩
      · rw [hih β hβα, mem_inter_iff] at hβ
        exact ⟨Or.inr ⟨β, hβα, hβ.2⟩, hβ.1⟩
    · rintro ⟨h | ⟨β, hβα, hβ⟩, hdU⟩
      · exact Or.inl ((hagree d h).mp hdU)
      · refine Or.inr ⟨β, hβα, hαθ β hβα, ?_⟩
        rw [hih β hβα, mem_inter_iff]
        exact ⟨hdU, hβ⟩
  obtain ⟨hSCl, hmonoCl, hnegCl, hjoinCl⟩ := hCl α hα
  rw [← hX] at hnegCl hjoinCl
  rw [traceStages_value hα, ← hX, ← hU']
  apply mem_ext
  intro d
  rw [mem_traceStep_iff, mem_inter_iff]
  constructor
  · rintro (h | h | ⟨A, hAX, hAU, rfl⟩ | ⟨Y, hY, hYX, ⟨y, hy, hyU⟩, rfl⟩)
    · exact ⟨((hprev d).mp (mem_union_iff.mpr (Or.inl h))).2, hSCl d (hH₀ d h)⟩
    · obtain ⟨hdX, hdU⟩ := (hprev d).mp (mem_union_iff.mpr (Or.inr h))
      refine ⟨hdU, ?_⟩
      rcases (hXmem d).mp hdX with hdS | ⟨β, hβα, hdβ⟩
      · exact hSCl d hdS
      · exact hmonoCl β hβα d hdβ
    · have hAnot : A ∉ U := fun hAU' ↦ hAU ((hprev A).mpr ⟨hAX, hAU'⟩)
      exact ⟨(antichainGeneric_neg_mem_iff hR hsys hU (hXreg A hAX)).mpr hAnot, hnegCl A hAX⟩
    · have hYreg : ∀ y ∈ Y, y ∈ Reg := fun y hy ↦ hXreg y (hYX y hy)
      exact ⟨(antichainGeneric_join_mem_iff hR hsys hU hY hYreg).mpr ⟨y, hy, ((hprev y).mp hyU).2⟩,
        hjoinCl Y hY hYX⟩
  · rintro ⟨hdU, hdCl⟩
    have hearlier : ∀ A, (A ∈ S ∨ ∃ β ∈ α, A ∈ Cl ‘ β) → A ∈ X := fun A hA ↦ (hXmem A).mpr hA
    rcases hsys.step α hα d hdCl with hdS | ⟨β, hβα, hdβ⟩ | ⟨A, hA, rfl⟩ | ⟨Y, hY, hYearly, rfl⟩
    · exact Or.inl ((hagree d hdS).mp hdU)
    · refine Or.inr (Or.inl ?_)
      have := (hprev d).mpr ⟨hearlier d (Or.inr ⟨β, hβα, hdβ⟩), hdU⟩
      rcases mem_union_iff.mp this with h | h
      · rw [hU', mem_sUnion_range_restrict_iff, traceStages_domain]
        refine ⟨β, hβα, hαθ β hβα, ?_⟩
        rw [hih β hβα, mem_inter_iff]
        exact ⟨hdU, hdβ⟩
      · exact h
    · have hAX := hearlier A hA
      have hAnot : A ∉ U := (antichainGeneric_neg_mem_iff hR hsys hU (hXreg A hAX)).mp hdU
      exact Or.inr (Or.inr (Or.inl ⟨A, hAX, fun h ↦ hAnot ((hprev A).mp h).2, rfl⟩))
    · have hYX : Y ⊆ X := fun y hy ↦ hearlier y (hYearly y hy)
      have hYreg : ∀ y ∈ Y, y ∈ Reg := fun y hy ↦ hXreg y (hYX y hy)
      obtain ⟨y, hy, hyU⟩ := (antichainGeneric_join_mem_iff hR hsys hU hY hYreg).mp hdU
      exact Or.inr (Or.inr (Or.inr ⟨Y, hY, hYX, ⟨y, hy, (hprev y).mpr ⟨hYX y hy, hyU⟩⟩, rfl⟩))

include hR hsys hU hCl hH₀ hagree in
/-- The trace set is the trace of the ultrafilter on the union of the stages. -/
theorem traceSet_eq : traceSet P R Ysets S H₀ Cl θ = U ∩ ⋃ˢ range Cl := by
  have := hsys.ordinal
  have hClf := hsys.fn
  apply mem_ext
  intro d
  unfold traceSet
  rw [mem_inter_iff, mem_sUnion_range_iff, mem_sUnion_range_iff, traceStages_domain, hsys.dom]
  constructor
  · rintro ⟨α, hα, hd⟩
    rw [traceStages_eq hR hsys hU hCl hH₀ hagree α hα, mem_inter_iff] at hd
    exact ⟨hd.1, α, hα, hd.2⟩
  · rintro ⟨hdU, α, hα, hd⟩
    refine ⟨α, hα, ?_⟩
    rw [traceStages_eq hR hsys hU hCl hH₀ hagree α hα, mem_inter_iff]
    exact ⟨hdU, hd⟩

end

end ZFVP
