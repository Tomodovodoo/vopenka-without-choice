import ZFVP.ModelTheory.NamedFunctionValues
import ZFVP.ModelTheory.ForcingModelPairs

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

noncomputable def activeScottSlots (D g : V) : V := {s ∈ D ; g ‘ s ≠ ∅}

instance activeScottSlots_definable : ℒₛₑₜ-function₂[V] activeScottSlots := by
  have h : ℒₛₑₜ-relation₃[V] (fun B D g ↦ ∀ s, s ∈ B ↔ s ∈ D ∧ g ‘ s ≠ ∅) := by definability
  apply Language.Definable.of_iff h
  intro v
  change v 0 = activeScottSlots (v 1) (v 2) ↔ _
  rw [mem_ext_iff]
  simp only [activeScottSlots, mem_sep_iff]

noncomputable def scottFunctionName (one g X P : V) : V :=
  repl (fun s ↦ ⟨orderedPairName one (checkName one (kpair.π₁ s)) (⋃ˢ (g ‘ s)), kpair.π₂ s⟩ₖ)
    (by definability) (activeScottSlots (X ×ˢ P) g)

theorem mem_scottFunctionName (one g X P z : V) :
    z ∈ scottFunctionName one g X P ↔ ∃ s ∈ X ×ˢ P, g ‘ s ≠ ∅ ∧
      z = ⟨orderedPairName one (checkName one (kpair.π₁ s)) (⋃ˢ (g ‘ s)), kpair.π₂ s⟩ₖ := by
  simp only [scottFunctionName, repl_spec, activeScottSlots, mem_sep_iff]
  constructor
  · rintro ⟨s, ⟨hs, hn⟩, he⟩
    exact ⟨s, hs, hn, he⟩
  · rintro ⟨s, hs, hn, he⟩
    exact ⟨s, ⟨hs, hn⟩, he⟩

theorem scottFunctionName_isName {one g X P : V} (hone : one ∈ P)
    (hg : ∀ s ∈ X ×ˢ P, g ‘ s ≠ ∅ → IsForcingName P (⋃ˢ (g ‘ s))) :
    IsForcingName P (scottFunctionName one g X P) := by
  apply (forcingName_iff P _).mpr
  intro z hz
  obtain ⟨s, hs, hn, rfl⟩ := (mem_scottFunctionName _ _ _ _ _).mp hz
  obtain ⟨a, ha, p, hp, rfl⟩ := mem_prod_iff.mp hs
  simp only [kpair.π₁_kpair, kpair.π₂_kpair] at *
  exact ⟨_, _, hp, rfl, orderedPairName_isName hone (checkName_isName hone a) (hg _
    (kpair_mem_iff.mpr ⟨ha, hp⟩) hn)⟩

namespace TransitiveZF
variable (U : V) [IsTransitive U] [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem activeScottSlots_val (D g : SetDomain U) :
    (activeScottSlots D g).val = activeScottSlots D.val g.val := by
  unfold activeScottSlots
  apply sep_val U
  intro s _
  have he : g ‘ s = ∅ ↔ g.val ‘ s.val = ∅ := by
    constructor
    · intro he
      have hv := congrArg Subtype.val he
      simpa only [value_val_total U, empty_val U] using hv
    · intro he
      apply Subtype.ext
      simpa only [value_val_total U, empty_val U] using he
  exact not_congr he

theorem orderedPairName_val (one σ τ : SetDomain U) :
    (orderedPairName one σ τ).val = orderedPairName one.val σ.val τ.val := by
  simp only [orderedPairName, pairName, insert_val U, singleton_val U, kpair_val U]

theorem scottFunctionName_val (one g X P : SetDomain U) :
    (scottFunctionName one g X P).val = scottFunctionName one.val g.val X.val P.val := by
  unfold scottFunctionName
  have ha := activeScottSlots_val U (X ×ˢ P) g
  rw [prod_val U] at ha
  rw [← ha]
  apply repl_val U
  intro s hs
  obtain ⟨a, _, p, _, rfl⟩ := mem_prod_iff.mp (mem_sep_iff.mp hs).1
  simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_val U, orderedPairName_val U,
    checkName_val U, sUnion_val U, value_val_total U]

end TransitiveZF
theorem namedValueScottGraph_scott {U P R one τ D s : V} [IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hτ : IsForcingName P τ) (hs : s ∈ D)
    (hn : (namedValueScottGraph U P R one τ D) ‘ s ≠ ∅) :
    IsNamedValueScottSet U P R one τ (kpair.π₂ s) (kpair.π₁ s)
      ((namedValueScottGraph U P R one τ D) ‘ s) := by
  have hf := namedValueScottGraph_function (U := U) hR htop hτ D
  let := IsFunction.of_mem hf
  have hm := kpair_value_mem ((domain_eq_of_mem_function hf).symm ▸ hs)
  have hslot := ((pair_mem_namedValueScottGraph U P R one τ D s _).mp hm).2.2
  exact hslot.elim id (fun h ↦ (hn h.2).elim)

theorem ForcingContext.mem_scottFunctionValue (A : ForcingContext V) (g X : V)
    (hg : ∀ s ∈ X ×ˢ A.P, g ‘ s ≠ ∅ → IsForcingName A.P (⋃ˢ (g ‘ s))) (z : A.Model) :
    z ∈ A.ofName ⟨scottFunctionName A.one g X A.P, scottFunctionName_isName A.top.1 hg⟩ ↔
      ∃ a, ∃ ha : a ∈ X, ∃ p, ∃ hp : p ∈ A.G, ∃ hn : g ‘ (⟨a, p⟩ₖ) ≠ ∅,
        z = ⟨A.check a, A.ofName ⟨⋃ˢ (g ‘ (⟨a, p⟩ₖ)),
          hg _ (kpair_mem_iff.mpr ⟨ha, A.generic.1.1 p hp⟩) hn⟩⟩ₖ := by
  rw [A.mem_ofName_iff]
  constructor
  · rintro ⟨σ, p, hp, hm, hz⟩
    obtain ⟨s, hs, hn, he⟩ := (mem_scottFunctionName _ _ _ _ _).mp hm
    obtain ⟨a, ha, q, hq, rfl⟩ := mem_prod_iff.mp hs
    simp only [kpair.π₁_kpair, kpair.π₂_kpair, kpair_iff] at he
    obtain ⟨he, rfl⟩ := he
    refine ⟨a, ha, p, hp, hn, hz.trans ?_⟩
    have hn' := hg _ (kpair_mem_iff.mpr ⟨ha, hq⟩) hn
    have he' : σ = ⟨orderedPairName A.one (checkName A.one a) (⋃ˢ (g ‘ (⟨a, p⟩ₖ))),
        orderedPairName_isName A.top.1 (checkName_isName A.top.1 a) hn'⟩ := Subtype.ext he
    rw [he']
    exact A.of_orderedPair ⟨checkName A.one a, checkName_isName A.top.1 a⟩ ⟨_, hn'⟩
  · rintro ⟨a, ha, p, hp, hn, rfl⟩
    have hn' := hg _ (kpair_mem_iff.mpr ⟨ha, A.generic.1.1 p hp⟩) hn
    refine ⟨⟨orderedPairName A.one (checkName A.one a) (⋃ˢ (g ‘ (⟨a, p⟩ₖ))),
      orderedPairName_isName A.top.1 (checkName_isName A.top.1 a) hn'⟩, p, hp, ?_, ?_⟩
    · exact (mem_scottFunctionName _ _ _ _ _).mpr
        ⟨⟨a, p⟩ₖ, kpair_mem_iff.mpr ⟨ha, A.generic.1.1 p hp⟩, hn, by simp⟩
    · exact (A.of_orderedPair ⟨checkName A.one a, checkName_isName A.top.1 a⟩ ⟨_, hn'⟩).symm

theorem ForcingContext.function_name_in_closed_model (A : ForcingContext V)
    {U : V} [hU : IsTransitive U]
    [Nonempty (SetDomain U)] [(SetDomain U)↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (hP : A.P ∈ U) (hR : A.R ∈ U) (hone : A.one ∈ U) (X : SetDomain U)
    (hclosed : U ^ (X.val ×ˢ A.P) ⊆ U) (τ : ForcingName A.P)
    (hf : IsFunction (A.ofName τ)) (hd : domain (A.ofName τ) = A.check X.val)
    (hr : ∀ a ∈ X.val, ∃ σ : ForcingName A.P, σ.val ∈ U ∧
      (A.ofName τ) ‘ (A.check a) = A.ofName σ) :
    ∃ ν : ForcingName A.P, ν.val ∈ U ∧ A.ofName ν = A.ofName τ := by
  let g := namedValueScottGraph U A.P A.R A.one τ.val (X.val ×ˢ A.P)
  have hgU : g ∈ U := namedValueScottGraph_mem A.order A.top τ.property hclosed
  have hs (s : V) (hs : s ∈ X.val ×ˢ A.P) (hn : g ‘ s ≠ ∅) :
      IsNamedValueScottSet U A.P A.R A.one τ.val (kpair.π₂ s) (kpair.π₁ s) (g ‘ s) :=
    namedValueScottGraph_scott A.order A.top τ.property hs hn
  have hg (s : V) (hmem : s ∈ X.val ×ˢ A.P) (hn : g ‘ s ≠ ∅) :
      IsForcingName A.P (⋃ˢ (g ‘ s)) := (hs s hmem hn).union.2.2.2.1
  let ν : ForcingName A.P := ⟨scottFunctionName A.one g X.val A.P, scottFunctionName_isName A.top.1 hg⟩
  have hνU : ν.val ∈ U := by
    have he := TransitiveZF.scottFunctionName_val U ⟨A.one, hone⟩ ⟨g, hgU⟩ X ⟨A.P, hP⟩
    let ν' : SetDomain U := scottFunctionName ⟨A.one, hone⟩ ⟨g, hgU⟩ X ⟨A.P, hP⟩
    have hm : ν'.val ∈ U := ν'.property
    rwa [he] at hm
  have hval (a : V) (ha : a ∈ X.val) (p : V) (hp : p ∈ A.G) (hn : g ‘ (⟨a, p⟩ₖ) ≠ ∅) :
      (A.ofName τ) ‘ (A.check a) =
        A.ofName ⟨⋃ˢ (g ‘ (⟨a, p⟩ₖ)), hg _ (kpair_mem_iff.mpr ⟨ha, A.generic.1.1 p hp⟩) hn⟩ := by
    have hsc := hs _ (kpair_mem_iff.mpr ⟨ha, A.generic.1.1 p hp⟩) hn
    simp only [kpair.π₁_kpair, kpair.π₂_kpair] at hsc
    obtain ⟨η, he, _, _, hv⟩ := A.namedValueScottSet_eval τ hp hsc
    exact hv.trans (congrArg A.ofName (Subtype.ext he))
  have hcover (a : V) (ha : a ∈ X.val) : ∃ p ∈ A.G, g ‘ (⟨a, p⟩ₖ) ≠ ∅ := by
    obtain ⟨σ, hσ, hv⟩ := hr a ha
    obtain ⟨p, hp, hforce⟩ := (A.namedFunctionValue_truth τ σ a).mpr ⟨hf, hv⟩
    have hpP := A.generic.1.1 p hp
    obtain ⟨C, hC⟩ := namedValueScottSet_exists (⟨A.P, hP⟩ : SetDomain U) ⟨A.R, hR⟩
      ⟨p, hU.mem_trans hpP hP⟩ A.one τ.val a A.order ⟨σ.val, hσ, σ.property, hforce⟩
    have he : g ‘ (⟨a, p⟩ₖ) = C := namedValueScottGraph_value A.order A.top τ.property
      (kpair_mem_iff.mpr ⟨ha, hpP⟩) (by simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using hC)
    obtain ⟨y, hy⟩ := hC.union.2.1.nonempty
    refine ⟨p, hp, ?_⟩
    intro hempty
    rw [he] at hempty
    simp [hempty] at hy
  refine ⟨ν, hνU, ?_⟩
  let := hf
  apply mem_ext
  intro z
  rw [A.mem_scottFunctionValue g X.val hg z]
  constructor
  · rintro ⟨a, ha, p, hp, hn, rfl⟩
    rw [← hval a ha p hp hn]
    exact kpair_value_mem (hd.symm ▸ (A.check_mem_iff a X.val).mpr ha)
  · intro hz
    obtain ⟨x, y, rfl⟩ := IsFunction.mem_eq_kpair hz
    have hx := mem_domain_of_kpair_mem hz
    rw [hd] at hx
    obtain ⟨a, ha, rfl⟩ := (A.mem_check_iff X.val x).mp hx
    obtain ⟨p, hp, hn⟩ := hcover a ha
    refine ⟨a, ha, p, hp, hn, ?_⟩
    have hy := (value_eq_of_kpair_mem hz).symm.trans (hval a ha p hp hn)
    exact congrArg (fun t ↦ ⟨A.check a, t⟩ₖ) hy

end ZFVP
