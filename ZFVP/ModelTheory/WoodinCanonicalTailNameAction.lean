import ZFVP.ModelTheory.WoodinSaturatedDisplacementForcing
import ZFVP.ModelTheory.WoodinSaturatedTailNameAction
import ZFVP.ModelTheory.WoodinCollapseEmptyIterand
import ZFVP.SetTheory.ForcingRenaming

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
universe u
variable {V : Type u} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem canonicalTailOutput_project {n : ℕ} (φ : SetTheorySemisentence n) (r : Fin n → Fin 8)
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ x : Fin 8 → W, collapseDisplacementOutputFormula.Evalb x → φ.Evalb (fun i ↦ x (r i)))
    {P R top p : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R φ (standardTuple (fun i ↦ (v (r i)).val)) := by
  have h := forcingFormula_entailment collapseDisplacementOutputFormula
    (φ.subst (fun i ↦ .bvar (r i))) (by
      intro W _ _ _ x hx
      simpa [Semiformula.eval_substs, Function.comp_def, Semiformula.Evalb] using hvalid W x hx) hR ht hp v ho
  rwa [forcingFormula_rename] at h

private theorem canonicalTail_vec4 {P : V} (v : Fin 8 → ForcingName P) (a b c d : Fin 8) :
    (fun i : Fin 4 ↦ (v (![a, b, c, d] i)).val) =
      ![(v a).val, (v b).val, (v c).val, (v d).val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
    (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j) i

private theorem canonicalTail_vec1 {P : V} (v : Fin 8 → ForcingName P) (a : Fin 8) :
    (fun i : Fin 1 ↦ (v (![a] i)).val) = ![(v a).val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i

theorem canonicalTailOutput_inverse {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![(v 0).val, (v 1).val, (v 6).val, (v 7).val]) := by
  have h := canonicalTailOutput_project tailInversePairFormula ![0, 1, 6, 7]
    (by
      intro W _ _ _ x hx
      have h := (eval_collapseDisplacementOutputFormula x).mp hx
      simpa [Defined.eval_iff, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using h.1)
    hR ht hp v ho
  rwa [canonicalTail_vec4] at h

theorem canonicalTailOutput_inverse_reverse {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R tailInversePairFormula
      (standardTuple ![(v 0).val, (v 1).val, (v 7).val, (v 6).val]) := by
  have h := canonicalTailOutput_project tailInversePairFormula ![0, 1, 7, 6]
    (by
      intro W _ _ _ x hx
      have h := (eval_collapseDisplacementOutputFormula x).mp hx
      simpa [Defined.eval_iff, Matrix.vecHead, Matrix.vecTail, Function.comp_def] using h.2.1)
    hR ht hp v ho
  rwa [canonicalTail_vec4] at h

theorem canonicalTailOutput_function {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R tailFunctionFormula (standardTuple ![(v 6).val]) := by
  have h := canonicalTailOutput_project tailFunctionFormula ![6]
    (by
      intro W _ _ _ x hx
      exact (Defined.eval_iff _).mpr ((eval_collapseDisplacementOutputFormula x).mp hx).2.2.1)
    hR ht hp v ho
  rwa [canonicalTail_vec1] at h

theorem canonicalTailOutput_function_reverse {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ forcingFormula P R tailFunctionFormula (standardTuple ![(v 7).val]) := by
  have h := canonicalTailOutput_project tailFunctionFormula ![7]
    (by
      intro W _ _ _ x hx
      exact (Defined.eval_iff _).mpr ((eval_collapseDisplacementOutputFormula x).mp hx).2.2.2.1)
    hR ht hp v ho
  rwa [canonicalTail_vec1] at h

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem canonicalTail_eval_rename {n m : ℕ} (φ : SetTheorySemisentence n)
    (r : Fin n → Fin m) (x : Fin m → V) :
    (φ.subst (fun j ↦ .bvar (r j))).Evalb x ↔ φ.Evalb (fun j ↦ x (r j)) := by
  simp [Semiformula.eval_substs, Function.comp_def, Semiformula.Evalb]

theorem canonicalTailOutput_empty_at (i : Fin 8)
    (hvalid : ∀ (W : Type u) [SetStructure W] [Nonempty W] [W↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
      ∀ x : Fin 8 → W, collapseDisplacementOutputFormula.Evalb x →
        IsFunction (x i) ∧ (x i) ‘ ∅ = ∅)
    {P R top p : V} (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun j ↦ (v j).val))) :
    p ∈ tailFunctionValueForcing P R (v i).val ∅ ∅ := by
  let w : Fin 9 → ForcingName P := ⟨∅, empty_forcingName P⟩ :> v
  let r : Fin 3 → Fin 9 := ![i.succ, 0, 0]
  let φ : SetTheorySemisentence 9 :=
    (collapseDisplacementOutputFormula.subst (fun j ↦ .bvar j.succ)).and
      (isEmpty.subst (fun _ : Fin 1 ↦ .bvar (0 : Fin 9)))
  let ψ : SetTheorySemisentence 9 := functionValueFormula.subst (fun j ↦ .bvar (r j))
  have hL : p ∈ forcingFormula P R
      (collapseDisplacementOutputFormula.subst (fun j ↦ .bvar j.succ))
      (standardTuple (fun j ↦ (w j).val)) := by
    rw [forcingFormula_rename]
    exact ho
  have hE : p ∈ forcingFormula P R (isEmpty.subst (fun _ : Fin 1 ↦ .bvar (0 : Fin 9)))
      (standardTuple (fun j ↦ (w j).val)) := by
    rw [forcingFormula_rename]
    have hw : (fun _ : Fin 1 ↦ (w 0).val) = ![(∅ : V)] := by
      funext j
      exact Fin.cases rfl (fun k ↦ Fin.elim0 k) j
    rw [hw]
    exact emptyName_forces hR ht hp
  have hφ : p ∈ forcingFormula P R φ (standardTuple (fun j ↦ (w j).val)) := by
    rw [show φ = _ from rfl, forcingFormula_and, mem_inter_iff]
    exact ⟨hL, hE⟩
  have h := forcingFormula_entailment φ ψ (by
    intro W _ _ _ x hx
    have hparts : (collapseDisplacementOutputFormula.subst (fun j ↦ .bvar j.succ)).Evalb x ∧
        (isEmpty.subst (fun _ : Fin 1 ↦ .bvar (0 : Fin 9))).Evalb x := hx
    rw [canonicalTail_eval_rename, canonicalTail_eval_rename] at hparts
    have hE : x 0 = ∅ := isEmpty_iff_eq_empty.mp ((Defined.eval_iff _).mp hparts.2)
    have hv := hvalid W (fun j ↦ x j.succ) hparts.1
    apply (canonicalTail_eval_rename functionValueFormula r x).mpr
    apply (eval_functionValueFormula (fun j ↦ x (r j))).mpr
    change IsFunction (x i.succ) ∧ (x i.succ) ‘ (x 0) = x 0
    rw [hE]
    exact hv)
    hR ht hp w hφ
  rw [show ψ = _ from rfl, forcingFormula_rename] at h
  have hw : (fun j : Fin 3 ↦ (w (r j)).val) = ![(v i).val, ∅, ∅] := by
    funext j
    exact Fin.cases rfl (fun k ↦ Fin.cases rfl
      (fun l ↦ Fin.cases rfl (fun m ↦ Fin.elim0 m) l) k) j
  rw [hw] at h
  exact h

theorem canonicalTailOutput_empty {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ tailFunctionValueForcing P R (v 6).val ∅ ∅ :=
  canonicalTailOutput_empty_at 6 (by
    intro W _ _ _ x hx
    have h := (eval_collapseDisplacementOutputFormula x).mp hx
    exact ⟨h.2.2.1, h.2.2.2.2.1⟩) hR ht hp v ho

theorem canonicalTailOutput_empty_reverse {P R top p : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top) (hp : p ∈ P)
    (v : Fin 8 → ForcingName P)
    (ho : p ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val))) :
    p ∈ tailFunctionValueForcing P R (v 7).val ∅ ∅ :=
  canonicalTailOutput_empty_at 7 (by
    intro W _ _ _ x hx
    have h := (eval_collapseDisplacementOutputFormula x).mp hx
    exact ⟨h.2.2.2.1, h.2.2.2.2.2.1⟩) hR ht hp v ho

def IsSparseTailAction (a C T F : V) : Prop :=
  IsForcingAutomorphism C T F ∧
  (∀ z ∈ C, (F ‘ z) ↾ a = z ↾ a) ∧
  (∀ z ∈ C, domain (F ‘ z) = domain z) ∧
  (∀ z ∈ C, z ‘ a = ∅ → F ‘ z = z)

theorem canonicalTailOutput_sparse_action_of_member_rank {a P R top δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ)
    (v : Fin 8 → ForcingName P)
    (ho : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (v i).val)))
    (hQr : ∀ τ : ForcingName P, top ∈ atomicMembership P R τ.val (v 0).val →
      top ∈ forcingFormula P R nameInHierarchyFormula (standardTuple ![τ.val, checkName top δ]))
    (hsp : ∀ p ∈ P, IsSparseFunctionOn a p) :
    IsSparseTailAction a (sparseNormalizedTwoStep a P R top δ (v 0).val)
      (sparseNormalizedTwoStepOrder a P R top δ (v 0).val (v 1).val)
      (sparseTailNameMap a P R top δ (v 0).val (v 6).val) := by
  have hi := canonicalTailOutput_inverse hR ht ht.1 v ho
  have hj := canonicalTailOutput_inverse_reverse hR ht ht.1 v ho
  have hf := canonicalTailOutput_function hR ht ht.1 v ho
  have hg := canonicalTailOutput_function_reverse hR ht ht.1 v ho
  have hf0 := canonicalTailOutput_empty hR ht ht.1 v ho
  have hg0 := canonicalTailOutput_empty_reverse hR ht ht.1 v ho
  have hn := normalizedTailTwoStepMap_automorphism_of_member_rank hR ht hδ hP
    (v 0) (v 1) (v 6) (v 7) hi hj hf hg hQr
  exact ⟨sparseTailNameMap_automorphism hsp hn,
    fun _ hz ↦ sparseTailNameMap_restrict hsp hn.1 hz,
    fun _ hz ↦ sparseTailNameMap_domain hR ht (v 0) (v 1) (v 6) (v 7)
      hi hf hg hf0 hg0 hsp hn.1 hz,
    fun _ hz hza ↦ sparseTailNameMap_empty_tail hR ht (v 6) hf hf0 hsp hn.1 hz hza⟩

private theorem canonicalTail_vec8 (P : V) (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ForcingName P) :
    (fun i ↦ (![x₀,x₁,x₂,x₃,x₄,x₅,x₆,x₇] i).val) =
      ![x₀.val,x₁.val,x₂.val,x₃.val,x₄.val,x₅.val,x₆.val,x₇.val] := by
  funext i
  exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.cases rfl
    (fun l ↦ Fin.cases rfl (fun m ↦ Fin.cases rfl (fun n ↦ Fin.cases rfl
    (fun o ↦ Fin.cases rfl (fun p ↦ Fin.cases rfl (fun q ↦ Fin.elim0 q) p) o) n) m) l) k) j) i

noncomputable def sparseCanonicalPrefixDisplacement (a P R top κ δ p q : V) : V :=
  sparseTailNameMap a P R top δ (saturatedWoodinPrefixPosetName P R top κ δ)
    (woodinCollapseDisplacementName P R (checkName top κ) (checkName top δ) p q)

noncomputable def sparseCanonicalHartogsDisplacement (a P R top γ δ p q : V) : V :=
  sparseTailNameMap a P R top δ (saturatedHartogsPosetName P R top γ δ)
    (woodinCollapseDisplacementName P R (hartogsNumberName P R (checkName top γ))
      (checkName top δ) p q)

theorem sparseCanonicalPrefixDisplacement_spec {a P R top κ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hκδ : κ ⊆ δ)
    (hκ : top ∈ forcingFormula P R regularCardinalFormula (standardTuple ![checkName top κ]))
    (p q : ForcingName P)
    (hp : top ∈ atomicMembership P R p.val (saturatedWoodinPrefixPosetName P R top κ δ))
    (hq : top ∈ atomicMembership P R q.val (saturatedWoodinPrefixPosetName P R top κ δ))
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z) :
    let Q := saturatedWoodinPrefixPosetName P R top κ δ
    let S := saturatedWoodinPrefixOrderName P R top κ δ
    IsSparseTailAction a (sparseNormalizedTwoStep a P R top δ Q)
      (sparseNormalizedTwoStepOrder a P R top δ Q S)
      (sparseCanonicalPrefixDisplacement a P R top κ δ p.val q.val) := by
  let Q : ForcingName P := ⟨_, saturatedWoodinPrefixPosetName_isName P R top κ δ⟩
  let S : ForcingName P := ⟨_, saturatedWoodinPrefixOrderName_isName P R top κ δ⟩
  let k : ForcingName P := ⟨_, checkName_isName ht.1 κ⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val p.val q.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have ho := saturatedPrefix_displacementName_forces_output hR ht hδ hP hκδ hκ p q hp hq
  have ho' : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (![Q,S,k,d,p,q,f,g] i).val)) := by
    rw [canonicalTail_vec8]
    exact ho
  exact canonicalTailOutput_sparse_action_of_member_rank hR ht hδ hP ![Q,S,k,d,p,q,f,g] ho'
    (fun τ hτ ↦ saturatedWoodinPrefix_member_forces_rank hR ht hδ hP hκδ τ hτ) hsp

theorem sparseCanonicalHartogsDisplacement_spec {a P R top γ δ : V}
    (hR : IsForcingPreorder P R) (ht : IsForcingTop P R top)
    (hδ : IsChoicelessInaccessible δ) (hP : P ∈ hierarchy δ) (hγδ : γ ∈ δ)
    (hγ : top ∈ forcingFormula P R regularCardinalFormula
      (standardTuple ![hartogsNumberName P R (checkName top γ)]))
    (p q : ForcingName P)
    (hp : top ∈ atomicMembership P R p.val (saturatedHartogsPosetName P R top γ δ))
    (hq : top ∈ atomicMembership P R q.val (saturatedHartogsPosetName P R top γ δ))
    (hsp : ∀ z ∈ P, IsSparseFunctionOn a z) :
    let Q := saturatedHartogsPosetName P R top γ δ
    let S := saturatedHartogsOrderName P R top γ δ
    IsSparseTailAction a (sparseNormalizedTwoStep a P R top δ Q)
      (sparseNormalizedTwoStepOrder a P R top δ Q S)
      (sparseCanonicalHartogsDisplacement a P R top γ δ p.val q.val) := by
  let Q : ForcingName P := ⟨_, saturatedHartogsPosetName_isName P R top γ δ⟩
  let S : ForcingName P := ⟨_, reverseInclusionOrderName_isName P R Q.val⟩
  let k : ForcingName P := ⟨_, hartogsNumberName_isName P R (checkName top γ)⟩
  let d : ForcingName P := ⟨_, checkName_isName ht.1 δ⟩
  let f : ForcingName P := ⟨_, woodinCollapseDisplacementName_isName P R k.val d.val p.val q.val⟩
  let g : ForcingName P := ⟨_, collapseConverseName_isName P R f.val⟩
  have ho := saturatedHartogs_displacementName_forces_output hR ht hδ hP hγδ hγ p q hp hq
  have ho' : top ∈ forcingFormula P R collapseDisplacementOutputFormula
      (standardTuple (fun i ↦ (![Q,S,k,d,p,q,f,g] i).val)) := by
    rw [canonicalTail_vec8]
    exact ho
  exact canonicalTailOutput_sparse_action_of_member_rank hR ht hδ hP ![Q,S,k,d,p,q,f,g] ho'
    (fun τ hτ ↦ saturatedHartogs_member_forces_rank hR ht hδ hP hγδ τ hτ) hsp

end ZFVP


