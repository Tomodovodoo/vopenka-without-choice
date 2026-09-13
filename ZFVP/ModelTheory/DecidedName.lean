import ZFVP.ModelTheory.SplittingName
import ZFVP.ModelTheory.StageCountability
import ZFVP.SetTheory.CheckNameTransport
import ZFVP.SetTheory.EndExtensionLevyColumns
import ZFVP.SetTheory.EndExtensionWellOrdering

/-! The name of the real assembled from decided segments: the nice name `decidedName` whose value
under a filter `H` is the union of the checked decided segments of the conditions in `H`. Under a
directed filter through the deciders, this value is a real. Also transports of the forcing
notions along the check map and the enumeration of the ground dense subsets of a cone. -/

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- The nice name of the union of the decided segments of the conditions in the generic. -/
noncomputable def decidedName (P R one τ : V) : V :=
  {w ∈ checkNames one ((ω : V) ×ˢ ((2 : ℕ) : V)) ×ˢ P ;
    ∃ q ∈ P, ∃ z, z ∈ (ω : V) ×ˢ ((2 : ℕ) : V) ∧ IsDecided P R one τ q z ∧ w = ⟨checkName one z, q⟩ₖ}

theorem mem_decidedName_iff (P R one τ w : V) :
    w ∈ decidedName P R one τ ↔ ∃ q ∈ P, ∃ z ∈ decidedSegment P R one τ q, w = ⟨checkName one z, q⟩ₖ := by
  unfold decidedName
  rw [mem_sep_iff]
  constructor
  · rintro ⟨-, q, hq, z, hz, hdec, rfl⟩
    exact ⟨q, hq, z, (mem_decidedSegment_iff _ _ _ _ _ _).mpr ⟨hz, hdec⟩, rfl⟩
  · rintro ⟨q, hq, z, hz, rfl⟩
    obtain ⟨hzprod, hdec⟩ := (mem_decidedSegment_iff _ _ _ _ _ _).mp hz
    refine ⟨mem_prod_iff.mpr ⟨_, (mem_checkNames_iff _ _ _).mpr ⟨z, hzprod, rfl⟩, q, hq, rfl⟩,
      q, hq, z, hzprod, hdec, rfl⟩

theorem decidedName_mem_subsetNames (P R one τ : V) :
    decidedName P R one τ ∈ subsetNames one ((ω : V) ×ˢ ((2 : ℕ) : V)) P :=
  mem_power_iff.mpr sep_subset

theorem decidedName_isName {P one : V} (R τ : V) (hone : one ∈ P) : IsForcingName P (decidedName P R one τ) :=
  subsetNames_isName hone (decidedName_mem_subsetNames P R one τ)

/-- The ground dense subsets of the cone below `p₁`. -/
noncomputable def coneDenseSets (P R p₁ : V) : V :=
  {D ∈ ℘ (cone P R p₁) ; ForcingDense (cone P R p₁) (restrictedOrder R (cone P R p₁)) D}

theorem mem_coneDenseSets_iff (P R p₁ D : V) : D ∈ coneDenseSets P R p₁ ↔
    D ⊆ cone P R p₁ ∧ ForcingDense (cone P R p₁) (restrictedOrder R (cone P R p₁)) D := by
  unfold coneDenseSets
  rw [mem_sep_iff, mem_power_iff]

theorem coneDenseSets_subset_power (P R p₁ : V) : coneDenseSets P R p₁ ⊆ ℘ P := fun D hD ↦
  mem_power_iff.mpr (fun x hx ↦ cone_subset P R p₁ x (((mem_coneDenseSets_iff _ _ _ _).mp hD).1 x hx))

theorem cone_dense_self {P R : V} (hR : IsForcingPreorder P R) (p₁ : V) :
    ForcingDense (cone P R p₁) (restrictedOrder R (cone P R p₁)) (cone P R p₁) :=
  ⟨fun x hx ↦ hx, fun p hp ↦ ⟨p, hp, (cone_preorder hR p₁).2.1 p hp⟩⟩

namespace ForcingContext

variable (S : ForcingContext V)

theorem check_forcingPreorder {P R : V} (hR : IsForcingPreorder P R) :
    IsForcingPreorder (S.check P) (S.check R) := by
  refine ⟨?_, fun p hp ↦ ?_, fun p hp q hq r hr hpq hqr ↦ ?_⟩
  · have h := (S.checkEmbedding.subset_iff R (P ×ˢ P)).mpr hR.1
    have hprod : S.check (P ×ˢ P) = S.check P ×ˢ S.check P := S.checkEmbedding.map_prod P P
    change S.check R ⊆ S.check (P ×ˢ P) at h
    rw [hprod] at h
    exact h
  · obtain ⟨p', hp', rfl⟩ := (S.mem_check_iff _ _).mp hp
    rw [← S.check_kpair, S.check_mem_iff]
    exact hR.2.1 p' hp'
  · obtain ⟨p', hp', rfl⟩ := (S.mem_check_iff _ _).mp hp
    obtain ⟨q', hq', rfl⟩ := (S.mem_check_iff _ _).mp hq
    obtain ⟨r', hr', rfl⟩ := (S.mem_check_iff _ _).mp hr
    rw [← S.check_kpair, S.check_mem_iff] at hpq hqr ⊢
    exact hR.2.2 p' hp' q' hq' r' hr' hpq hqr

theorem check_forcingTop {P R one : V} (htop : IsForcingTop P R one) :
    IsForcingTop (S.check P) (S.check R) (S.check one) := by
  refine ⟨(S.check_mem_iff _ _).mpr htop.1, fun p hp ↦ ?_⟩
  obtain ⟨p', hp', rfl⟩ := (S.mem_check_iff _ _).mp hp
  rw [← S.check_kpair, S.check_mem_iff]
  exact htop.2 p' hp'

theorem check_forcingDense {P R D : V} (hD : ForcingDense P R D) :
    ForcingDense (S.check P) (S.check R) (S.check D) := by
  refine ⟨(S.checkEmbedding.subset_iff D P).mpr hD.1, fun p hp ↦ ?_⟩
  obtain ⟨p', hp', rfl⟩ := (S.mem_check_iff _ _).mp hp
  obtain ⟨q, hqD, hqp⟩ := hD.2 p' hp'
  exact ⟨S.check q, (S.check_mem_iff _ _).mpr hqD, by rw [← S.check_kpair, S.check_mem_iff]; exact hqp⟩

theorem check_incompatible {s t : V} [IsFunction s] [IsFunction t] (h : Incompatible s t) :
    Incompatible (S.check s) (S.check t) := by
  obtain ⟨i, his, hit, hne⟩ := h
  refine ⟨S.check i, ?_, ?_, ?_⟩
  · rw [S.check_domain, S.check_mem_iff]; exact his
  · rw [S.check_domain, S.check_mem_iff]; exact hit
  · rw [S.check_value his, S.check_value hit]
    intro heq
    exact hne ((S.check_eq_iff _ _).mp heq)

theorem check_restrictedOrder (R Q : V) :
    S.check (restrictedOrder R Q) = restrictedOrder (S.check R) (S.check Q) :=
  S.checkEmbedding.map_restrictedOrder R Q

/-- The value of the checked decided name under a filter containing the checked top. -/
theorem mem_nameValue_check_decidedName_iff {P R one τ : V} (hR : IsForcingPreorder P R) {H : S.Model}
    (hone : S.check one ∈ H) (y : S.Model) :
    y ∈ nameValue H (S.check (decidedName P R one τ)) ↔
      ∃ q, S.check q ∈ H ∧ ∃ z ∈ decidedSegment P R one τ q, y = S.check z := by
  rw [mem_nameValue_iff]
  constructor
  · rintro ⟨ν, p, hpH, hνp, rfl⟩
    obtain ⟨w, hw, hwe⟩ := (S.mem_check_iff _ _).mp hνp
    obtain ⟨q, hq, z, hz, rfl⟩ := (mem_decidedName_iff _ _ _ _ _).mp hw
    rw [S.check_kpair] at hwe
    obtain ⟨rfl, rfl⟩ := kpair_inj hwe
    exact ⟨q, hpH, z, hz, S.nameValue_check_checkName hone z⟩
  · rintro ⟨q, hqH, z, hz, rfl⟩
    have hqP : q ∈ P := by
      obtain ⟨hzprod, m, hm, i, hi, rfl, hf, -⟩ := (mem_decidedSegment_iff _ _ _ _ _ _).mp hz
      exact forcesCheckedMember_mem hR hf
    refine ⟨S.check (checkName one z), S.check q, hqH, ?_, (S.nameValue_check_checkName hone z).symm⟩
    rw [← S.check_kpair, S.check_mem_iff, mem_decidedName_iff]
    exact ⟨q, hqP, z, hz, rfl⟩

/-- The union of the decided segments along a directed filter through the deciders is a real. -/
theorem decided_union_real {P R one τ p₀ : V} (hR : IsForcingPreorder P R)
    (hfun : ∀ q ∈ P, ⟨q, p₀⟩ₖ ∈ R → decidedSegment P R one τ q ∈ binarySequences V)
    {H : S.Model} (hHP : ∀ q, S.check q ∈ H → q ∈ P)
    (hdir : ∀ p q, S.check p ∈ H → S.check q ∈ H →
      ∃ r, S.check r ∈ H ∧ ⟨r, p⟩ₖ ∈ R ∧ ⟨r, q⟩ₖ ∈ R ∧ ⟨r, p₀⟩ₖ ∈ R)
    (hdec : ∀ n ∈ (ω : V), ∃ q ∈ deciderSet P R one τ n, S.check q ∈ H)
    {Y : S.Model} (hY : ∀ y, y ∈ Y ↔ ∃ q, S.check q ∈ H ∧ ∃ z ∈ decidedSegment P R one τ q, y = S.check z) :
    Y ∈ cantorSpace S.Model := by
  rw [cantorSpace_eq_check, mem_function_iff]
  refine ⟨fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨q, hqH, z, hz, rfl⟩ := (hY y).mp hy
    have hzprod := ((mem_decidedSegment_iff _ _ _ _ _ _).mp hz).1
    obtain ⟨m, hm, i, hi, rfl⟩ := mem_prod_iff.mp hzprod
    rw [S.check_kpair]
    exact mem_prod_iff.mpr ⟨_, (S.check_mem_iff _ _).mpr hm, _, (S.check_mem_iff _ _).mpr hi, rfl⟩
  · obtain ⟨m, hm, rfl⟩ := (S.mem_check_iff _ _).mp hx
    obtain ⟨q, hqD, hqH⟩ := hdec m hm
    obtain ⟨hqP, hqdec⟩ := (mem_deciderSet_iff _ _ _ _ _ _).mp hqD
    obtain ⟨i, hi, hf⟩ := hqdec m (mem_succ_iff.mpr (Or.inl rfl))
    have hzq : ⟨m, i⟩ₖ ∈ decidedSegment P R one τ q :=
      (mem_decidedSegment_iff _ _ _ _ _ _).mpr ⟨mem_prod_iff.mpr ⟨m, hm, i, hi, rfl⟩,
        m, hm, i, hi, rfl, hf, fun m' hm' ↦ hqdec m' (mem_succ_iff.mpr (Or.inr hm'))⟩
    refine ⟨S.check i, ?_, ?_⟩
    · show ⟨S.check m, S.check i⟩ₖ ∈ Y
      rw [← S.check_kpair]
      exact (hY _).mpr ⟨q, hqH, _, hzq, rfl⟩
    · intro y hy
      obtain ⟨q', hq'H, z', hz', hze⟩ := (hY _).mp hy
      have hz'prod := ((mem_decidedSegment_iff _ _ _ _ _ _).mp hz').1
      obtain ⟨m', hm', i', hi', rfl⟩ := mem_prod_iff.mp hz'prod
      rw [S.check_kpair] at hze
      obtain ⟨hmm, hyi⟩ := kpair_inj hze
      have hmm' : m = m' := (S.check_eq_iff _ _).mp hmm
      subst hmm'
      obtain ⟨r, hrH, hrq, hrq', hrp₀⟩ := hdir q q' hqH hq'H
      have hrP : r ∈ P := hHP r hrH
      have hrfun : IsFunction (decidedSegment P R one τ r) := binarySequence_isFunction (hfun r hrP hrp₀)
      have h1 : ⟨m, i⟩ₖ ∈ decidedSegment P R one τ r := decidedSegment_mono hR hrP hrq _ hzq
      have h2 : ⟨m, i'⟩ₖ ∈ decidedSegment P R one τ r := decidedSegment_mono hR hrP hrq' _ hz'
      have : i' = i := (value_eq_of_kpair_mem h2).symm.trans (value_eq_of_kpair_mem h1)
      rw [hyi, this]

/-- Enumeration of the ground dense subsets of the cone in the extension. -/
theorem exists_cone_dense_enumeration {P R : V} (hR : IsForcingPreorder P R) (p₁ : V)
    (hcount : IsInternallyCountable (S.check (coneDenseSets P R p₁))) :
    ∃ e ∈ (℘ (S.check (cone P R p₁))) ^ (ω : S.Model),
      (∀ n ∈ (ω : S.Model), ForcingDense (S.check (cone P R p₁))
        (S.check (restrictedOrder R (cone P R p₁))) (e ‘ n)) ∧
      ∀ D : V, D ∈ coneDenseSets P R p₁ → ∃ n ∈ (ω : S.Model), e ‘ n = S.check D := by
  have h0 : S.check (cone P R p₁) ∈ S.check (coneDenseSets P R p₁) :=
    (S.mem_check_iff _ _).mpr ⟨_, (mem_coneDenseSets_iff _ _ _ _).mpr ⟨fun x hx ↦ hx, cone_dense_self hR p₁⟩, rfl⟩
  obtain ⟨E, hE, hrange⟩ := exists_surjection_of_cardLE hcount h0
  have hEf : IsFunction E := IsFunction.of_mem hE
  have hval : ∀ D ∈ S.check (coneDenseSets P R p₁),
      ForcingDense (S.check (cone P R p₁)) (S.check (restrictedOrder R (cone P R p₁))) D := by
    intro D hD
    obtain ⟨D₀, hD₀, rfl⟩ := (S.mem_check_iff _ _).mp hD
    exact S.check_forcingDense ((mem_coneDenseSets_iff _ _ _ _).mp hD₀).2
  refine ⟨E, mem_function_of_mem_function_of_subset hE (fun D hD ↦ mem_power_iff.mpr (hval D hD).1),
    fun n hn ↦ hval _ (function_value_mem hE hn), ?_⟩
  intro D hD
  have hmem : S.check D ∈ range E := by
    rw [hrange]
    exact (S.mem_check_iff _ _).mpr ⟨D, hD, rfl⟩
  obtain ⟨n, hn⟩ := mem_range_iff.mp hmem
  have hnω : n ∈ (ω : S.Model) := by
    rw [← domain_eq_of_mem_function hE]
    exact mem_domain_of_kpair_mem hn
  exact ⟨n, hnω, value_eq_of_kpair_mem hn⟩

end ForcingContext

end ZFVP
