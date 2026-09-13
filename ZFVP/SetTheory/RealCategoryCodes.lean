import ZFVP.SetTheory.BinaryNowhereDenseImages

/-! Actual rational-interval codes for closed sets and meagre real sets. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem realOpen_eq_interiorCode {U : V} (hU : IsRealOpen U) :
    U = realOpenFrom (realInteriorCode U) := by
  apply mem_ext
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab, hxi, hiU⟩ := realOpen_neighborhood hU hx
    exact (mem_realOpenFrom_iff _ _).mpr ⟨((mem_realInterval_iff _ _ _).mp hxi).1,
      ⟨a, b⟩ₖ, mem_sep_iff.mpr ⟨(pair_mem_realBasicCodes_iff _ _).mpr ⟨ha, hb, hab⟩,
        by simpa using hiU⟩, by simpa using hxi⟩
  · intro hx
    obtain ⟨_, p, hp, hxi⟩ := (mem_realOpenFrom_iff _ _).mp hx
    exact (mem_sep_iff.mp hp).2 x hxi

noncomputable def realClosedCode (P : V) : V :=
  realInteriorCode ((dedekindReals V) \ P)

instance realClosedCode_definable : ℒₛₑₜ-function₁[V] realClosedCode := by
  unfold realClosedCode
  definability

theorem realClosedCode_subset (P : V) : realClosedCode P ⊆ realBasicCodes V := by
  intro p hp
  simp only [realClosedCode, realInteriorCode, mem_sep_iff] at hp
  exact hp.1

theorem realClosedCode_spec {P : V} (hP : P ⊆ dedekindReals V)
    (hopen : IsRealOpen ((dedekindReals V) \ P)) : realClosedFrom (realClosedCode P) = P := by
  have he := realOpen_eq_interiorCode hopen
  apply mem_ext
  intro x
  rw [mem_realClosedFrom_iff]
  change (IsDedekindCut x ∧ x ∉ realOpenFrom (realInteriorCode ((dedekindReals V) \ P))) ↔ x ∈ P
  rw [← he, mem_sdiff_iff]
  constructor
  · rintro ⟨hx, h⟩
    by_contra hxP
    exact h ⟨(mem_dedekindReals_iff _).mpr hx, hxP⟩
  · intro hxP
    exact ⟨(mem_dedekindReals_iff _).mp (hP x hxP), fun h ↦ h.2 hxP⟩

def IsRealMeagre (A : V) : Prop :=
  ∃ f ∈ (℘ (realBasicCodes V)) ^ (ω : V),
    (∀ n ∈ (ω : V), IsRealNowhereDense (realClosedFrom (f ‘ n))) ∧
    ∀ x ∈ A, ∃ n ∈ (ω : V), x ∈ realClosedFrom (f ‘ n)

instance isRealMeagre_definable : ℒₛₑₜ-predicate[V] IsRealMeagre := by
  unfold IsRealMeagre
  definability

def RealBaireProperty (A : V) : Prop :=
  ∃ U, IsRealOpen U ∧ IsRealMeagre ((A \ U) ∪ (U \ A))

instance realBaireProperty_definable : ℒₛₑₜ-predicate[V] RealBaireProperty := by
  unfold RealBaireProperty
  definability

theorem isRealMeagre_subset {A B : V} (hB : IsRealMeagre B) (hAB : A ⊆ B) : IsRealMeagre A := by
  obtain ⟨f, hf, hfn, hcover⟩ := hB
  exact ⟨f, hf, hfn, fun x hx ↦ hcover x (hAB x hx)⟩

theorem binaryImage_meagre {A : V} (hA : IsMeagre A) : IsRealMeagre (binaryImage A) := by
  obtain ⟨f, _, hfn, hcover⟩ := hA
  let F : V → V := fun n ↦ realClosedCode (binaryImage (treeBody (f ‘ n)))
  have hF : ℒₛₑₜ-function₁ F := by unfold F; definability
  let g := definableGraph (ω : V) F hF
  have hspec : ∀ n ∈ (ω : V), realClosedFrom (F n) = binaryImage (treeBody (f ‘ n)) := by
    intro n hn
    exact realClosedCode_spec (binaryImage_subset_reals (treeBody_subset_cantorSpace _))
      (binaryTreeImage_complement_open (hfn n hn).1)
  refine ⟨g, definableGraph_mem_function_of_mapsTo _ _ _ _
    (fun n _ ↦ mem_power_iff.mpr (realClosedCode_subset _)), ?_, ?_⟩
  · intro n hn
    rw [value_definableGraph _ _ _ hn, hspec n hn]
    exact binaryNowhereDenseImage_nowhereDense (hfn n hn)
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := (mem_binaryImage_iff _ _).mp hx
    obtain ⟨n, hn, hcn⟩ := hcover c hc
    refine ⟨n, hn, ?_⟩
    rw [value_definableGraph _ _ _ hn, hspec n hn]
    exact (mem_binaryImage_iff _ _).mpr ⟨c, hcn, rfl⟩

end ZFVP
