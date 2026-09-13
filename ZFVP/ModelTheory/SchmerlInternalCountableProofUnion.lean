import ZFVP.ModelTheory.SchmerlInternalProofConstruction
import ZFVP.ModelTheory.SchmerlInternalBMR

/-! Countable conjunction from an actual internally indexed family of derivation
codes. Internal Choice bounds the two countable unions and selects premise
codes from the witness fibers supplied by Collection. -/

namespace ZFVP.Infinitary.Internal
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem IsInternalDerivationCode.unpack {L Γ n φ c : V} (h : IsInternalDerivationCode L Γ n φ c) :
    IsInternallyCountable (kpair.π₁ c) ∧ IsInternallyCountable (kpair.π₁ (kpair.π₂ c)) ∧
    IsInternalProof L Γ (kpair.π₁ c) (kpair.π₁ (kpair.π₂ c)) ∧
    kpair.π₂ (kpair.π₂ c) ∈ kpair.π₁ (kpair.π₂ c) ∧
    kpair.π₁ (kpair.π₂ (kpair.π₂ c)) = ⟨n, φ⟩ₖ := by
  obtain ⟨F, D, d, rfl, hF, hD, hP, hd, hl⟩ := h
  simpa only [kpair.π₁_kpair, kpair.π₂_kpair] using And.intro hF ⟨hD, hP, hd, hl⟩

theorem IsFragment.sUnion_repl {L I : V} (U : V → V) (hU : ℒₛₑₜ-function₁ U)
    (hL : IsLanguageCode L) (hf : ∀ i ∈ I, IsFragment L (U i)) :
    IsFragment L (⋃ˢ repl U hU I) := by
  refine ⟨hL, ?_⟩
  intro t ht
  obtain ⟨A, hA, ht⟩ := mem_sUnion_iff.mp ht
  obtain ⟨i, hi, rfl⟩ := (repl_spec hU).mp hA
  have hsub : U i ⊆ ⋃ˢ repl U hU I := fun x hx ↦
    mem_sUnion_iff.mpr ⟨U i, (repl_spec hU).mpr ⟨i, hi, rfl⟩, hx⟩
  exact ⟨(hf i hi).2 t ht |>.1, ((hf i hi).2 t ht).2.mono hsub⟩

theorem internalDerivation_conjunction_of_codes {L Γ n f C : V} (hAC : InternalChoice V)
    (hf : IsFunction f) (hfd : domain f = (ω : V))
    (hC : ∀ i ∈ (ω : V), IsInternalDerivationCode L Γ n (f ‘ i) (C ‘ i)) :
    ∃ z, IsInternalDerivationCode L Γ n (conjCode f) z := by
  let U : V → V := fun i ↦ kpair.π₁ (C ‘ i)
  let P : V → V := fun i ↦ kpair.π₁ (kpair.π₂ (C ‘ i))
  let r : V → V := fun i ↦ kpair.π₂ (kpair.π₂ (C ‘ i))
  have hU : ℒₛₑₜ-function₁ U := by unfold U; definability
  have hP : ℒₛₑₜ-function₁ P := by unfold P; definability
  have hr : ℒₛₑₜ-function₁ r := by unfold r; definability
  let F := ⋃ˢ repl U hU (ω : V)
  let D := ⋃ˢ repl P hP (ω : V)
  have hdata (i : V) (hi : i ∈ (ω : V)) := (hC i hi).unpack
  have hUF (i : V) (hi : i ∈ (ω : V)) : U i ⊆ F := fun x hx ↦
    mem_sUnion_iff.mpr ⟨U i, (repl_spec hU).mpr ⟨i, hi, rfl⟩, hx⟩
  have hPD (i : V) (hi : i ∈ (ω : V)) : P i ⊆ D := fun x hx ↦
    mem_sUnion_iff.mpr ⟨P i, (repl_spec hP).mpr ⟨i, hi, rfl⟩, hx⟩
  have hzero := hdata 0 (by simp)
  have hF : IsFragment L F := IsFragment.sUnion_repl U hU hzero.2.2.1.1.1
    (fun i hi ↦ (hdata i hi).2.2.1.1)
  have hlabels (i : V) (hi : i ∈ (ω : V)) : ⟨n, f ‘ i⟩ₖ ∈ F := by
    have h := ((hdata i hi).2.2.1.2.2 _ (hdata i hi).2.2.2.1).label_mem
    rw [(hdata i hi).2.2.2.2] at h
    exact hUF i hi _ h
  have hn := (hF.node (hlabels 0 (by simp))).1
  have hFc : IsInternallyCountable F := Schmerl.internal_countable_union hAC
    internallyCountable_omega U hU (fun i hi ↦ (hdata i hi).1)
  have hDc : IsInternallyCountable D := Schmerl.internal_countable_union hAC
    internallyCountable_omega P hP (fun i hi ↦ (hdata i hi).2.1)
  have hProof : IsInternalProof L Γ F D := by
    refine ⟨hF, fun x hx ↦ hUF 0 (by simp) x (hzero.2.2.1.2.1 x hx), ?_⟩
    intro d hd
    obtain ⟨A, hA, hd⟩ := mem_sUnion_iff.mp hd
    obtain ⟨i, hi, rfl⟩ := (repl_spec hP).mp hA
    exact ((hdata i hi).2.2.1.2.2 d hd).mono (fun _ hx ↦ hx) (hUF i hi) (hPD i hi)
  let H := insert ⟨n, conjCode f⟩ₖ F
  let g := definableGraph (ω : V) r hr
  let d := booleanProofNode n (conjCode f) 3 g
  have hFH : F ⊆ H := fun _ hx ↦ mem_insert.mpr (Or.inr hx)
  have hH : IsFragment L H := hF.insert_conj hn hf hfd hlabels
  have hProofH := hProof.weaken hH (fun _ hx ↦ hx) (fun x hx ↦ hFH x (hProof.2.1 x hx)) hFH
  have hnode : IsInternalProofNode L Γ H (insert d D) d := by
    apply Or.inl
    apply Or.inl
    refine ⟨n, conjCode f, by simp [H], Or.inr (Or.inr (Or.inr ⟨f, g, hf, hfd,
      definableGraph_isFunction _ _ _, domain_definableGraph _ _ _, rfl, rfl, ?_⟩))⟩
    intro i hi
    rw [show g ‘ i = r i from value_definableGraph _ _ _ hi]
    exact ⟨mem_insert.mpr (Or.inr (hPD i hi _ (hdata i hi).2.2.2.1)), (hdata i hi).2.2.2.2⟩
  refine ⟨⟨H, ⟨insert d D, d⟩ₖ⟩ₖ, H, insert d D, d, rfl,
    internallyCountable_insert hFc _, internallyCountable_insert hDc d,
    hProofH.insert hnode, by simp, ?_⟩
  exact booleanProofNode_label _ _ _ _

theorem internalDerivation_conjunction {L Γ n f : V} (hAC : InternalChoice V)
    (hf : IsFunction f) (hfd : domain f = (ω : V))
    (h : ∀ i ∈ (ω : V), ∃ c, IsInternalDerivationCode L Γ n (f ‘ i) c) :
    ∃ z, IsInternalDerivationCode L Γ n (conjCode f) z := by
  let R : V → V → Prop := fun i c ↦ IsInternalDerivationCode L Γ n (f ‘ i) c
  have hR : ℒₛₑₜ-relation R := by
    unfold R
    definability
  obtain ⟨B, hB⟩ := collection (ω : V) R hR h
  let S : V → V := fun i ↦ {c ∈ B ; R i c}
  have hS : ℒₛₑₜ-function₁ S := by
    have hsrel : ℒₛₑₜ-relation (fun X i : V ↦ ∀ c, c ∈ X ↔ c ∈ B ∧ R i c) := by definability
    apply Language.Definable.of_iff hsrel
    intro v
    change v 0 = S (v 1) ↔ _
    simp only [mem_ext_iff, S, mem_sep_iff]
  let g := definableGraph (ω : V) S hS
  have hg (i : V) (hi : i ∈ (ω : V)) : g ‘ i = S i := value_definableGraph _ _ _ hi
  have hn : ∀ i ∈ (ω : V), IsNonempty (g ‘ i) := by
    intro i hi
    obtain ⟨c, hc, hrc⟩ := hB i hi
    rw [hg i hi]
    exact ⟨c, mem_sep_iff.mpr ⟨hc, hrc⟩⟩
  obtain ⟨C, _, hC⟩ := countableChoice_of_internalChoice hAC g
    (definableGraph_isFunction _ _ _) (domain_definableGraph _ _ _) hn
  apply internalDerivation_conjunction_of_codes hAC hf hfd (C := C)
  intro i hi
  have hc := hC i hi
  rw [hg i hi] at hc
  exact (mem_sep_iff.mp hc).2

end ZFVP.Infinitary.Internal
