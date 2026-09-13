import ZFVP.ModelTheory.LastPointCn
import ZFVP.ModelTheory.EmbeddingFixedCofinality
import ZFVP.SetTheory.OrdinalMapBound
import ZFVP.SetTheory.ClubSets

/-! Correct fixed ranks are cofinal below a last point of uncountable cofinality. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rankEmbedding_correct_fixed_above {n k l : ℕ} {θ η f ξ : V}
    (hθ : Cn (k + 1) θ) (hη : Cn (l + 1) η)
    (hf : IsCodedMembershipEmbedding (hierarchy θ) (hierarchy η) f)
    (hγθ : lastPoint θ f ∈ θ) (hCn : CnCofinal n (lastPoint θ f))
    (hno : ∀ g, ¬IsCofinalMap (lastPoint θ f) (ω : V) g)
    (hξ : ξ ∈ lastPoint θ f) :
    ∃ δ, ξ ∈ δ ∧ δ ∈ lastPoint θ f ∧ Cn n δ ∧ f ‘ δ = δ := by
  let := hθ.ordinal
  let := lastPoint_ordinal θ f
  let γ := lastPoint θ f
  let C := fixedOrdinals θ f
  let D := {δ ∈ γ ; Cn n δ}
  have hC : IsUnboundedIn C γ := by
    constructor
    · intro δ hδ
      obtain ⟨hδθ, hfix⟩ := mem_fixedOrdinals.mp hδ
      exact rankEmbedding_fixed_mem_lastPoint hθ hη hf hδθ hfix
    · intro δ hδ
      obtain ⟨ζ, hζ, hδζ, hfix⟩ := rankEmbedding_fixed_cofinal_lastPoint hθ hη hf hδ
      exact ⟨ζ, mem_fixedOrdinals.mpr ⟨lastPoint_subset θ f _ hζ, hfix⟩, hδζ⟩
  have hD : IsUnboundedIn D γ := by
    refine ⟨fun _ h ↦ (mem_sep_iff.mp h).1, ?_⟩
    intro δ hδ
    obtain ⟨ζ, hζ, hδζ, hCζ⟩ := hCn δ hδ
    exact ⟨ζ, mem_sep_iff.mpr ⟨hζ, hCζ⟩, hδζ⟩
  let F := fun x : V ↦ nextIn C (nextIn D x)
  have hF : ℒₛₑₜ-function₁[V] F := by unfold F; definability
  have hstep : ∀ x ∈ γ, F x ∈ γ ∧ f ‘ (F x) = F x ∧ x ∈ F x := by
    intro x hx
    have hd := nextIn_spec hD hx
    have hc := nextIn_spec hC (hD.1 _ hd.1)
    let : IsOrdinal (F x) := IsOrdinal.of_mem (hC.1 _ hc.1)
    exact ⟨hC.1 _ hc.1, (mem_fixedOrdinals.mp hc.1).2,
      IsOrdinal.toIsTransitive.mem_trans hd.2 hc.2⟩
  let start := nextIn C ξ
  have hstart := nextIn_spec hC hξ
  let a := naturalIteration F hF start
  have ha : ∀ i ∈ (ω : V), a i ∈ γ ∧ f ‘ (a i) = a i :=
    naturalIteration_invariant F hF start (fun x ↦ x ∈ γ ∧ f ‘ x = x) (by definability)
      ⟨hC.1 _ hstart.1, (mem_fixedOrdinals.mp hstart.1).2⟩
      (fun x hx ↦ ⟨(hstep x hx.1).1, (hstep x hx.1).2.1⟩)
  have hsucc : ∀ i ∈ (ω : V), a (succ i) = F (a i) :=
    fun i hi ↦ naturalIteration_succ F hF start hi
  have hinc : ∀ i ∈ (ω : V), a i ∈ a (succ i) := by
    intro i hi
    rw [hsucc i hi]
    exact (hstep (a i) (ha i hi).1).2.2
  let g := naturalIterationGraph F hF start
  have hg : g ∈ γ ^ (ω : V) := definableGraph_mem_function_of_mapsTo _ _ _ _ (fun i hi ↦ (ha i hi).1)
  have hval : ∀ i ∈ (ω : V), g ‘ i = a i := fun i hi ↦ naturalIterationGraph_value F hF start hi
  obtain ⟨β, hβγ, hb⟩ := ordinalMap_bounded_of_not_cofinal hg (hno g)
  let := IsOrdinal.of_mem hβγ
  let δ := ⋃ˢ range g
  have hδord : IsOrdinal δ := IsOrdinal.sUnion
    (fun y hy ↦ IsOrdinal.of_mem (range_subset_of_mem_function hg y hy))
  let := hδord
  have hcof : ∀ x ∈ δ, ∃ i ∈ (ω : V), x ∈ a i := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_sUnion_iff.mp hx
    obtain ⟨i, hiy⟩ := mem_range_iff.mp hy
    have hi : i ∈ (ω : V) := domain_eq_of_mem_function hg ▸ mem_domain_of_kpair_mem hiy
    exact ⟨i, hi, by rw [← hval i hi, value_eq_of_kpair_mem hiy]; exact hxy⟩
  have hδβ : δ ⊆ β := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcof x hx
    have hai : a i ∈ β := by
      rw [← hval i hi]
      exact hb i hi
    exact IsOrdinal.toIsTransitive.mem_trans hxi hai
  have hδγ : δ ∈ γ := ordinal_mem_of_subset_mem hδβ hβγ
  have harange : ∀ i ∈ (ω : V), a i ∈ range g := by
    intro i hi
    rw [← hval i hi]
    exact value_mem_range hg hi
  have haiδ : ∀ i ∈ (ω : V), a i ∈ δ := by
    intro i hi
    exact mem_sUnion_iff.mpr ⟨a (succ i), harange _ (ω_succ_closed hi), hinc i hi⟩
  have hstartδ : start ∈ δ := by simpa only [a, naturalIteration_zero] using haiδ 0 (by simp)
  have hδCn : Cn n δ := by
    apply cn_closed n ⟨start, hstartδ⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcof x hx
    have hd := nextIn_spec hD (ha i hi).1
    have hc := nextIn_spec hC (hD.1 _ hd.1)
    have hdnext : nextIn D (a i) ∈ a (succ i) := by simpa only [hsucc i hi, F] using hc.2
    have hdδ := IsOrdinal.toIsTransitive.mem_trans hdnext (haiδ _ (ω_succ_closed hi))
    let := IsOrdinal.of_mem hdδ
    exact ⟨nextIn D (a i), hdδ, IsOrdinal.toIsTransitive.mem_trans hxi hd.2,
      (mem_sep_iff.mp hd.1).2⟩
  have hgδ : IsCofinalMap δ (ω : V) g := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ haiδ, ?_⟩
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcof x hx
    let := IsOrdinal.of_mem (haiδ i hi)
    exact ⟨i, hi, (hval i hi).symm ▸ IsOrdinal.toIsTransitive.transitive _ hxi⟩
  have hfixδ := rankEmbedding_fixed_of_omegaCofinal hθ hη hf
    (IsOrdinal.toIsTransitive.mem_trans hδγ hγθ) hgδ (by
      intro i hi
      rw [hval i hi]
      exact (ha i hi).2)
  exact ⟨δ, IsOrdinal.toIsTransitive.mem_trans hstart.2 hstartδ, hδγ, hδCn, hfixδ⟩

end ZFVP
