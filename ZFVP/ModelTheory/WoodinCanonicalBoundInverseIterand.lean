import ZFVP.ModelTheory.WoodinInverseFirstCoordinates
import ZFVP.ModelTheory.InverseSourceCollapseCode
import ZFVP.ModelTheory.WoodinInverseStageBounds

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- A nonempty ordinal contains the empty set. -/
theorem empty_mem_of_ordinal_ne_empty {α : V} [IsOrdinal α] (h : α ≠ ∅) : (∅ : V) ∈ α := by
  rcases IsOrdinal.mem_trichotomy (α := (∅ : V)) (β := α) with h1 | h1 | h1
  · exact h1
  · exact absurd h1.symm h
  · exact (not_mem_empty h1).elim

/-- The forced top of the Woodin collapse only needs the collapse cardinal name to be
forced nonzero, not forced regular. -/
theorem woodinCollapse_empty_top_forced_of_member {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (κ δ : ForcingName P)
    (hκ : p ∈ atomicMembership P R ∅ κ.val)
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    p ∈ forcingFormula P R forcingTopFormula
      (standardTuple ![woodinCollapseName P R κ.val δ.val,
        reverseInclusionOrderName P R (woodinCollapseName P R κ.val δ.val), (∅ : V)]) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨(∅ : V), empty_forcingName _⟩
  have hκ' : p ∈ forcingFormula P R nameMemberFormula (standardTuple ![t.val, κ.val]) := by
    rw [forcingFormula_nameMember]
    exact hκ
  let φ : SetTheorySemisentence 5 :=
    (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).and
      ((piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).and
        ((isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).and
          ((nameMemberFormula.subst (fun i ↦ .bvar ((![2, 3] : Fin 2 → Fin 5) i))).and
            (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i))))))
  let ψ : SetTheorySemisentence 5 := forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 5) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![Q.val, S.val, t.val, κ.val, δ.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_and, mem_inter_iff, forcingFormula_and, mem_inter_iff,
      forcingFormula_rename, forcingFormula_rename, forcingFormula_rename, forcingFormula_rename,
      forcingFormula_rename]
    exact ⟨woodinCollapseName_forces hR htop hp κ δ,
      reverseInclusionOrderName_forces hR htop hp Q, emptyName_forces hR htop hp, hκ', hδ⟩
  have hψ := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (totalWoodinCollapseFormula.subst (fun i ↦ .bvar ((![0, 3, 4] : Fin 3 → Fin 5) i))).Evalb v ∧
      (piOneReverseInclusionOrderFormula.subst (fun i ↦ .bvar ((![1, 0] : Fin 2 → Fin 5) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 5) i))).Evalb v ∧
      (nameMemberFormula.subst (fun i ↦ .bvar ((![2, 3] : Fin 2 → Fin 5) i))).Evalb v ∧
      (IsOrdinal.dfn.subst (fun i ↦ .bvar ((![4] : Fin 1 → Fin 5) i))).Evalb v at hv
    have hh : v 0 = totalWoodinCollapse (v 3) (v 4) ∧ v 1 = reverseInclusionOrder (v 0) ∧
        v 2 = ∅ ∧ v 2 ∈ v 3 ∧ IsOrdinal (v 4) := by
      simpa [Semiformula.eval_substs, nameMemberFormula] using hv
    let := hh.2.2.2.2
    have hz : (∅ : W) ∈ v 3 := hh.2.2.1 ▸ hh.2.2.2.1
    have ht : IsForcingTop (v 0) (v 1) (v 2) := by
      rw [hh.2.1, hh.1, hh.2.2.1, totalWoodinCollapse_eq]
      exact woodinCollapse_top hz (v 4)
    simpa [ψ, Semiformula.eval_substs] using ht)
    hR htop hp ![Q, S, t, κ, δ] hφ
  change p ∈ forcingFormula P R (forcingTopFormula.subst
    (fun i ↦ .bvar ((![0, 1, 2] : Fin 3 → Fin 5) i)))
    (standardTuple ![Q.val, S.val, t.val, κ.val, δ.val]) at hψ
  rw [forcingFormula_rename] at hψ
  exact hψ

/-- Every condition forces the empty function into the Woodin collapse poset once the
collapse cardinal name is forced nonzero. -/
theorem woodinCollapseName_forces_empty_member_of_member {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one) (hp : p ∈ P) (κ δ : ForcingName P)
    (hκ : p ∈ atomicMembership P R ∅ κ.val)
    (hδ : p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    p ∈ atomicMembership P R ∅ (woodinCollapseName P R κ.val δ.val) := by
  let Q : ForcingName P := ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩
  let S : ForcingName P := ⟨reverseInclusionOrderName P R Q.val, reverseInclusionOrderName_isName _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  have hh := woodinCollapse_empty_top_forced_of_member hR htop hp κ δ hκ hδ
  let ψ : SetTheorySemisentence 3 := nameMemberFormula.subst
    (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))
  have hm := forcingFormula_entailment forcingTopFormula ψ (by
    intro W _ _ _ v hv
    have ht : IsForcingTop (v 0) (v 1) (v 2) := (Defined.eval_iff v).mp hv
    simpa [ψ, nameMemberFormula, Semiformula.eval_substs] using ht.1)
    hR htop hp ![Q, S, t] hh
  dsimp only [ψ] at hm
  rw [forcingFormula_rename] at hm
  change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![∅, Q.val]) at hm
  rwa [forcingFormula_nameMember] at hm

/-- The saturated Woodin collapse is an iterand as soon as the collapse cardinal name is
forced nonzero and the restoration name is forced to be an ordinal. -/
theorem saturatedWoodinCollapse_empty_iterand_of_member {P R one U : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (κ δ : ForcingName P) (hU : (∅ : V) ∈ U)
    (hκ : ∀ p ∈ P, p ∈ atomicMembership P R ∅ κ.val)
    (hδ : ∀ p ∈ P, p ∈ forcingFormula P R IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterand P R (forcingSaturatedName P R U (woodinCollapseName P R κ.val δ.val))
      (reverseInclusionOrderName P R
        (forcingSaturatedName P R U (woodinCollapseName P R κ.val δ.val))) ∅ :=
  saturatedName_empty_iterand hR htop
    ⟨woodinCollapseName P R κ.val δ.val, woodinCollapseName_isName _ _ _ _⟩ hU
    (fun p hp ↦ woodinCollapseName_forces_empty_member_of_member hR htop hp κ δ (hκ p hp) (hδ p hp))

/-- The Hartogs number name is forced nonzero, with no hypothesis on the name it is taken of. -/
theorem hartogsNumberName_forces_empty_member {P R one p : V} (hR : IsForcingPreorder P R)
    (htop : IsForcingTop P R one) (hp : p ∈ P) (τ : ForcingName P) :
    p ∈ atomicMembership P R ∅ (hartogsNumberName P R τ.val) := by
  let κ : ForcingName P := ⟨hartogsNumberName P R τ.val, hartogsNumberName_isName _ _ _⟩
  let t : ForcingName P := ⟨∅, empty_forcingName P⟩
  let φ : SetTheorySemisentence 3 :=
    (hartogsNumberFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).and
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i)))
  let ψ : SetTheorySemisentence 3 := nameMemberFormula.subst
    (fun i ↦ .bvar ((![2, 0] : Fin 2 → Fin 3) i))
  have hφ : p ∈ forcingFormula P R φ (standardTuple ![κ.val, τ.val, t.val]) := by
    dsimp only [φ]
    rw [forcingFormula_and, mem_inter_iff, forcingFormula_rename, forcingFormula_rename]
    exact ⟨hartogsNumberName_forces hR htop hp τ, emptyName_forces hR htop hp⟩
  have hm := forcingFormula_entailment φ ψ (by
    intro W _ _ _ v hv
    change (hartogsNumberFormula.subst (fun i ↦ .bvar ((![0, 1] : Fin 2 → Fin 3) i))).Evalb v ∧
      (isEmpty.subst (fun i ↦ .bvar ((![2] : Fin 1 → Fin 3) i))).Evalb v at hv
    have hh : v 0 = hartogsNumber (v 1) ∧ v 2 = ∅ := by
      simpa [Semiformula.eval_substs] using hv
    have hz : v 2 ∈ v 0 := by
      rw [hh.1, hh.2]
      let := (hartogsNumber_initial (v 1)).1
      exact empty_mem_of_ordinal_ne_empty (hartogsNumber_ne_zero (v 1))
    simpa [ψ, nameMemberFormula, Semiformula.eval_substs] using hz)
    hR htop hp ![κ, τ, t] hφ
  dsimp only [ψ] at hm
  rw [forcingFormula_rename] at hm
  change p ∈ forcingFormula P R nameMemberFormula (standardTuple ![∅, κ.val]) at hm
  rwa [forcingFormula_nameMember] at hm

/-- Iterand form of the inverse-limit collapse that replaces the forced regularity of the
collapse cardinal name by the weaker demand that the name is forced nonzero. -/
theorem forcingInverseCollapse_iterand_of_member {θ s ζ : V} [IsOrdinal θ]
    (h : IsForcingIterationCode θ s) (h0 : ∅ ∈ θ)
    (κ δ : ForcingName (forcingInverseCodePoset θ s))
    (hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset θ s) ζ)
    (hκ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ atomicMembership (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s) ∅ κ.val)
    (hδ : ∀ p ∈ forcingInverseCodePoset θ s,
      p ∈ forcingFormula (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        IsOrdinal.dfn (standardTuple ![δ.val])) :
    IsForcingIterand (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
      (forcingInverseCollapseName θ s ζ κ.val δ.val)
      (reverseInclusionOrderName (forcingInverseCodePoset θ s) (forcingInverseCodeOrder θ s)
        (forcingInverseCollapseName θ s ζ κ.val δ.val)) ∅ := by
  have c := h.system.inverseColumn h0 h.subset_universe
  simp only [forcingInverseCollapseName, saturatedWoodinCollapseName]
  exact saturatedWoodinCollapse_empty_iterand_of_member c.order.preorder c.tops.top κ δ hz hκ hδ

/-- The packed inverse source stage at a limit coordinate with a non inaccessible stage
cardinal really is a two step extension of the inverse limit by an iterand. The forcing
statements about the limit cardinal that the construction of that stage used are not needed
again: the collapse poset name is built from a Hartogs number name, which is forced nonzero
outright, and the cutoff ordinal is inaccessible because the stage at `succ j` is valid. -/
theorem woodinInverseStage_iterand {δ θ j : V} [IsOrdinal θ]
    (hs : ∀ k ∈ θ, IsWoodinIteration δ (succ k) (kpair.π₁ (woodinIterationRec k))
      (kpair.π₂ (woodinIterationRec k)))
    (hj : j ∈ θ) (h0 : j ≠ ∅) (hlim : j ≠ succ (⋃ˢ j))
    (hinac : ¬IsChoicelessInaccessible (woodinLimitCardinal (woodinIterationCardinalPrefix j))) :
    IsForcingIterand (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingInverseCollapseName j (woodinIterationPrefix j)
        (forcingInverseSourceCutoff j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseHartogsName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
        (forcingInverseRestorationName j (woodinIterationPrefix j)
          (woodinLimitCardinal (woodinIterationCardinalPrefix j))))
      (reverseInclusionOrderName (forcingInverseCodePoset j (woodinIterationPrefix j))
        (forcingInverseCodeOrder j (woodinIterationPrefix j))
        (forcingInverseCollapseName j (woodinIterationPrefix j)
          (forcingInverseSourceCutoff j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseHartogsName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j)))
          (forcingInverseRestorationName j (woodinIterationPrefix j)
            (woodinLimitCardinal (woodinIterationCardinalPrefix j))))) ∅ := by
  let := IsOrdinal.of_mem hj
  set γ := woodinLimitCardinal (woodinIterationCardinalPrefix j) with hγ
  have hsub : j ⊆ θ := IsOrdinal.toIsTransitive.transitive _ hj
  have hcode : IsForcingIterationCode j (woodinIterationPrefix j) :=
    (woodinIterationPrefix_of_stages (fun k hk ↦ hs k (hsub k hk))).code
  have hzero : (∅ : V) ∈ j := empty_mem_of_ordinal_ne_empty h0
  have c := hcode.system.inverseColumn hzero hcode.subset_universe
  have ht : IsForcingTop (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseCodeOrder j (woodinIterationPrefix j))
      (forcingInverseCodeTop j (woodinIterationPrefix j)) := c.tops.top
  -- the cutoff ordinal is inaccessible, hence nonempty, because stage `succ j` is valid
  have hin := (hs j hj).inaccessible j (mem_succ_self j)
  simp only [woodinIterationRec_inverse h0 hlim hinac, kpair.π₂_kpair, woodinInverseCardinalNext,
    forcingFamilyNext_new] at hin
  have hcut : (∅ : V) ∈ forcingInverseSourceCutoff j (woodinIterationPrefix j) γ := by
    let := hin.1
    exact IsOrdinal.toIsTransitive.transitive _ hin.2.1 _ empty_mem_ω
  have hz : (∅ : V) ∈ forcingNameHierarchy (forcingInverseCodePoset j (woodinIterationPrefix j))
      (forcingInverseSourceCutoff j (woodinIterationPrefix j) γ) :=
    (mem_forcingNameHierarchy _ _ _).mpr ⟨∅, hcut, fun z hz ↦ (not_mem_empty hz).elim⟩
  let τ : ForcingName (forcingInverseCodePoset j (woodinIterationPrefix j)) :=
    ⟨checkName (forcingInverseCodeTop j (woodinIterationPrefix j)) γ, checkName_isName ht.1 _⟩
  let κ : ForcingName (forcingInverseCodePoset j (woodinIterationPrefix j)) :=
    ⟨forcingInverseHartogsName j (woodinIterationPrefix j) γ, hartogsNumberName_isName _ _ _⟩
  let ν : ForcingName (forcingInverseCodePoset j (woodinIterationPrefix j)) :=
    ⟨forcingInverseRestorationName j (woodinIterationPrefix j) γ, checkName_isName ht.1 _⟩
  exact forcingInverseCollapse_iterand_of_member hcode hzero κ ν hz
    (fun p hp ↦ hartogsNumberName_forces_empty_member c.order.preorder ht hp τ)
    (fun _ hp ↦ forces_checked_ordinal c.order.preorder ht inferInstance hp)

end ZFVP
