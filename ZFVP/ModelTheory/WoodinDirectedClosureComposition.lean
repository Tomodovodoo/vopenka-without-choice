import ZFVP.ModelTheory.WoodinDirectedQuotientTransport
import ZFVP.ModelTheory.QuotientClosureComposition

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem projection_separative_directedClosedAt_countable [Countable V]
    {P R one Q S π α : V} [IsOrdinal α]
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (hπ : IsForcingProjection P R Q S π) (hS : IsForcingPreorder Q S)
    (hbase : IsForcingDirectedClosedAt P (forcingSeparativeOrder P R) α)
    (htail : ∀ (G : Set V) (hG : IsExternalForcingGeneric P R G),
      let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
      IsForcingDirectedClosedAt (A.projectionQuotient Q π)
        (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
        (A.check α)) :
    IsForcingDirectedClosedAt Q (forcingSeparativeOrder Q S) α := by
  intro f hf
  let := IsFunction.of_mem hf.1
  have hpdesc := hπ.separative_directed_compose hf
  obtain ⟨p, hp, hpb⟩ := hbase _ hpdesc
  obtain ⟨G, hG, hpG⟩ := exists_externalForcingGeneric hR hp
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hfi (i : V) (hi : i ∈ α) : A.check (f ‘ i) ∈ A.projectionQuotient Q π := by
    apply (A.check_mem_projectionQuotient_iff hπ.maps).mpr
    refine ⟨function_value_mem hf.1 hi, externalForcingGeneric_separative_upward hR hG hpG ?_⟩
    simpa only [value_compose_of_mem_function hf.1 hπ.maps hi] using hpb i hi
  have hval (i : V) (hi : i ∈ α) : (A.check f) ‘ (A.check i) = A.check (f ‘ i) :=
    A.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hi)
  let g : A.Model := definableGraph (A.check α) (fun i ↦ (A.check f) ‘ i) (by definability)
  have hgv (i : A.Model) (hi : i ∈ A.check α) : g ‘ i = (A.check f) ‘ i :=
    value_definableGraph _ _ _ hi
  have hg : IsForcingDirectedFamily (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π))
      (A.check α) g := by
    refine ⟨definableGraph_mem_function_of_mapsTo _ _ _ _ ?_, ?_⟩
    · intro i hi
      obtain ⟨i, hi', rfl⟩ := (A.mem_check_iff α i).mp hi
      rw [hval i hi']
      exact hfi i hi'
    · intro i hi j hj
      obtain ⟨i, hi', rfl⟩ := (A.mem_check_iff α i).mp hi
      obtain ⟨j, hj', rfl⟩ := (A.mem_check_iff α j).mp hj
      obtain ⟨k, hk, hki, hkj⟩ := hf.2 i hi' j hj'
      have hk' := (A.check_mem_iff k α).mpr hk
      refine ⟨A.check k, hk', ?_, ?_⟩
      · rw [hgv _ hk', hgv _ hi, hval k hk, hval i hi']
        exact A.projectionQuotient_separative_of_ground hπ hS (hfi k hk) (hfi i hi') hki
      · rw [hgv _ hk', hgv _ hj, hval k hk, hval j hj']
        exact A.projectionQuotient_separative_of_ground hπ hS (hfi k hk) (hfi j hj') hkj
  obtain ⟨x, hx, hxb⟩ := htail G hG g hg
  obtain ⟨q, hq, hqG, rfl⟩ := (A.mem_projectionQuotient_iff hπ.maps x).mp hx
  let QN : ForcingName P := ⟨projectionQuotientName Q π one, projectionQuotientName_isName htop.1 hπ.maps⟩
  let SN : ForcingName P := ⟨projectionQuotientOrderName S π one,
    projectionQuotientOrderName_isName htop.1 hπ.maps hS⟩
  let cn (x : V) : ForcingName P := ⟨checkName one x, checkName_isName htop.1 x⟩
  have hev : forcingSeparativeBoundFormula.Evalb
      (fun i ↦ A.ofName (![QN, SN, cn α, cn f, cn q] i)) := by
    apply (Defined.eval_iff _).mpr
    change A.check q ∈ A.ofName QN ∧ ∀ i ∈ A.check α,
      ⟨A.check q, (A.check f) ‘ i⟩ₖ ∈ forcingSeparativeOrder (A.ofName QN) (A.ofName SN)
    rw [A.ofName_projectionQuotient hπ.maps, A.ofName_projectionQuotientOrder hπ hS]
    exact ⟨hx, fun i hi ↦ hgv i hi ▸ hxb i hi⟩
  obtain ⟨a, haG, haf⟩ := (A.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, cn α, cn f, cn q]).mp hev
  obtain ⟨b, hbG, hba, hbq⟩ := hG.1.2.2.2 a haG _ hqG
  obtain ⟨u, hu, huq, heu⟩ := hπ.lift q hq b (hG.1.1 b hbG) hbq
  refine ⟨u, hu, ?_⟩
  intro i hi
  refine (kpair_mem_forcingSeparativeOrder Q S u (f ‘ i)).mpr
    ⟨hu, function_value_mem hf.1 hi, ?_⟩
  intro s hs hsu
  obtain ⟨H, hH, hsH⟩ := exists_externalForcingGeneric hR (function_value_mem hπ.maps hs)
  let B : ForcingContext V := ⟨P, R, one, H, hR, htop, hH⟩
  have hsa : ⟨π ‘ s, a⟩ₖ ∈ R := by
    have hsb := hπ.monotone s hs u hu hsu
    rw [heu] at hsb
    exact hR.2.2 _ (function_value_mem hπ.maps hs) b (hG.1.1 b hbG) a (hG.1.1 a haG) hsb hba
  have haH := hH.1.2.2.1 _ hsH a (hG.1.1 a haG) hsa
  have hb := (Defined.eval_iff _).mp ((B.formula_truth forcingSeparativeBoundFormula
    ![QN, SN, cn α, cn f, cn q]).mpr ⟨a, haH, haf⟩)
  change B.check q ∈ B.ofName QN ∧ ∀ j ∈ B.check α,
    ⟨B.check q, (B.check f) ‘ j⟩ₖ ∈ forcingSeparativeOrder (B.ofName QN) (B.ofName SN) at hb
  rw [B.ofName_projectionQuotient hπ.maps, B.ofName_projectionQuotientOrder hπ hS] at hb
  have hbi := hb.2 (B.check i) ((B.check_mem_iff i α).mpr hi)
  rw [B.check_value ((domain_eq_of_mem_function hf.1).symm ▸ hi)] at hbi
  have hs' := (B.check_mem_projectionQuotient_iff hπ.maps).mpr ⟨hs, hsH⟩
  have hsq' : ⟨B.check s, B.check q⟩ₖ ∈ B.projectionQuotientOrder Q S π :=
    (B.projectionQuotientOrder_pair_iff Q S π _ _).mpr
      ⟨B.check_kpair s q ▸ (B.check_mem_iff _ _).mpr (hS.2.2 s hs u hu q hq hsu huq), hs', hb.1⟩
  obtain ⟨y, hy, hys, hyi⟩ := ((kpair_mem_forcingSeparativeOrder _ _ _ _).mp hbi).2.2 _ hs' hsq'
  obtain ⟨v, hv, _, rfl⟩ := (B.mem_projectionQuotient_iff hπ.maps y).mp hy
  have hvs := ((B.projectionQuotientOrder_pair_iff Q S π _ _).mp hys).1
  have hvi := ((B.projectionQuotientOrder_pair_iff Q S π _ _).mp hyi).1
  rw [← B.check_kpair, B.check_mem_iff] at hvs hvi
  exact ⟨v, hv, hvs, hvi⟩


namespace ForcingContext

theorem double_projectionQuotient_separative_directedClosedAt_iff (A C : ForcingContext V)
    {Q S π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R C.P C.R τ E)
    (hA : forcingProjectionGeneric A.P A.R τ C.G = A.G)
    (hπ : π ∈ A.P ^ Q) (hρ : ρ ∈ C.P ^ Q)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q) (γ : A.Model) :
    let B := A.projectionQuotientContext C hτ hA
    IsForcingDirectedClosedAt
      (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
      (forcingSeparativeOrder
        (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
        (B.projectionQuotientOrder (A.projectionQuotient Q π)
          (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)))
      (B.check γ) ↔
    IsForcingDirectedClosedAt (C.projectionQuotient Q ρ)
      (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
      (A.projectionInclusion C hτ hA γ) := by
  dsimp only
  let B := A.projectionQuotientContext C hτ hA
  let j := A.projectionFactorizationElementaryMap C hτ hA
  have h := j.forcingSeparativeDirectedClosedAt_iff
    (B.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
    (B.projectionQuotientOrder (A.projectionQuotient Q π)
      (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ)) (B.check γ)
  change _ ↔ IsForcingDirectedClosedAt
    (A.projectionFactorizationEquiv C hτ hA _)
    (forcingSeparativeOrder (A.projectionFactorizationEquiv C hτ hA _)
      (A.projectionFactorizationEquiv C hτ hA _))
    (A.projectionFactorizationEquiv C hτ hA (B.check γ)) at h
  rw [A.projectionFactorizationEquiv_quotient C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_quotientOrder C hτ hA hπ hρ he,
    A.projectionFactorizationEquiv_check C hτ hA] at h
  exact h

theorem quotient_separative_directedClosedAt_comp_countable [Countable V]
    (A : ForcingContext V) {Q S T U o π τ ρ E : V}
    (hτ : IsForcingSplitProjection A.P A.R T U τ E)
    (hU : IsForcingPreorder T U) (ho : IsForcingTop T U o) (hS : IsForcingPreorder Q S)
    (hπ : π ∈ A.P ^ Q) (hρ : IsForcingProjection T U Q S ρ)
    (he : ∀ q ∈ Q, τ ‘ (ρ ‘ q) = π ‘ q)
    (γ : A.Model) [IsOrdinal γ]
    (hbase : IsForcingDirectedClosedAt (A.projectionQuotient T τ)
      (forcingSeparativeOrder (A.projectionQuotient T τ) (A.projectionQuotientOrder T U τ)) γ)
    (htail : ∀ (H : Set V) (hH : IsExternalForcingGeneric T U H)
      (hA : forcingProjectionGeneric A.P A.R τ H = A.G),
      let C : ForcingContext V := ⟨T, U, o, H, hU, ho, hH⟩
      IsForcingDirectedClosedAt (C.projectionQuotient Q ρ)
        (forcingSeparativeOrder (C.projectionQuotient Q ρ) (C.projectionQuotientOrder Q S ρ))
        (A.projectionInclusion C hτ hA γ)) :
    IsForcingDirectedClosedAt (A.projectionQuotient Q π)
      (forcingSeparativeOrder (A.projectionQuotient Q π) (A.projectionQuotientOrder Q S π)) γ := by
  have ht : IsForcingTop T U (E ‘ A.one) :=
    ⟨function_value_mem hτ.maps A.top.1, fun q hq ↦
      (hτ.below q hq A.one A.top.1).mpr (A.top.2 _ (function_value_mem hτ.projection.maps hq))⟩
  have htop := A.projectionQuotient_top hτ.projection.maps ht (hτ.right_inverse A.one A.top.1)
  have hR := A.projectionQuotient_preorder hτ.projection.maps hU
  apply projection_separative_directedClosedAt_countable hR htop
    (A.projectionQuotient_projection hπ hτ.projection.maps hρ he)
    (A.projectionQuotient_preorder hπ hS) hbase
  intro H hH
  let B : ForcingContext A.Model := ⟨_, _, _, H, hR, htop, hH⟩
  let C := A.projectionCombinedContext hτ.projection hU ho hH
  have hA : forcingProjectionGeneric A.P A.R τ C.G = A.G :=
    A.projectionCombined_projection hτ.projection hH
  have hB : B = A.projectionQuotientContext C hτ hA :=
    B.eq_of_data_eq _ rfl rfl rfl (A.projectionCombined_quotientFilter hτ.projection.maps hH.1).symm
  have hc := htail C.G C.generic hA
  have hb := (A.double_projectionQuotient_separative_directedClosedAt_iff C hτ hA hπ hρ.maps he γ).mpr hc
  change IsForcingDirectedClosedAt (B.projectionQuotient _ _)
    (forcingSeparativeOrder (B.projectionQuotient _ _) (B.projectionQuotientOrder _ _ _)) (B.check γ)
  let transfer (D : ForcingContext A.Model) : Prop :=
    IsForcingDirectedClosedAt (D.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
      (forcingSeparativeOrder
        (D.projectionQuotient (A.projectionQuotient Q π) (A.projectionQuotientMap Q π ρ))
        (D.projectionQuotientOrder (A.projectionQuotient Q π)
          (A.projectionQuotientOrder Q S π) (A.projectionQuotientMap Q π ρ))) (D.check γ)
  exact (congrArg transfer hB).mpr hb


end ForcingContext
end ZFVP


