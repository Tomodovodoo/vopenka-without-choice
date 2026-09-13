import ZFVP.SetTheory.TwoStepForcing

namespace ZFVP

open LO LO.FirstOrder LO.FirstOrder.SetTheory

def twoStepDenseNamesFormula : SetTheorySemisentence 8 :=
  f“P R o Q S D t p. !forcingPreorderFormula P R ∧ !forcingTopFormula P R o ∧
    !forcingNameFormula P Q ∧ !forcingNameFormula P S ∧ !forcingNameFormula P D ∧
    !forcingNameFormula P t ∧ p ∈ P ∧
    !(tripleForcingTruthFormula forcingDenseFormula) p P R Q S D ∧
    p ∈ !atomicMembershipFormula P R t Q →
    ∀ q ∈ P, !kpair.dfn q p ∈ R → ∃ r ∈ P, ∃ s ∈ !domain.dfn Q,
      !kpair.dfn r q ∈ R ∧ r ∈ !atomicMembershipFormula P R s Q ∧
      r ∈ !atomicMembershipFormula P R s D ∧
      !(tripleForcingTruthFormula boundedPairMemberFormula) r P R S s t”

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem twoStep_dense_names_countable [Countable V] {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (Q S D t : ForcingName P) (_hp : p ∈ P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula (standardTuple ![Q.val, S.val, D.val]))
    (ht : p ∈ atomicMembership P R t.val Q.val) :
    ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ∃ σ ∈ domain Q.val,
      ⟨r, q⟩ₖ ∈ R ∧ r ∈ atomicMembership P R σ Q.val ∧ r ∈ atomicMembership P R σ D.val ∧
      r ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, σ, t.val]) := by
  intro q hq hqp
  obtain ⟨G, hG, hqG⟩ := exists_externalForcingGeneric hR hq
  let A : ForcingContext V := ⟨P, R, one, G, hR, htop, hG⟩
  have hqD := (forcingFormula_regular hR forcingDenseFormula _).2.1 p hD q hq hqp
  have hdense : ForcingDense (A.ofName Q) (A.ofName S) (A.ofName D) :=
    (Defined.eval_iff _).mp ((A.formula_truth forcingDenseFormula ![Q, S, D]).mpr ⟨q, hqG, hqD⟩)
  have hqt := atomicMembership_mono hR ht hq hqp
  have hqt' : q ∈ forcingFormula P R nameMemberFormula (standardTuple ![t.val, Q.val]) := by
    rwa [forcingFormula_nameMember]
  have htA : A.ofName t ∈ A.ofName Q := by
    have he := (A.formula_truth nameMemberFormula ![t, Q]).mpr ⟨q, hqG, hqt'⟩
    simpa [nameMemberFormula] using he
  obtain ⟨x, hxD, hxt⟩ := hdense.2 _ htA
  obtain ⟨σ, s, hsG, hσs, rfl⟩ := (A.mem_ofName_iff Q x).mp (hdense.1 x hxD)
  have hσD : nameMemberFormula.Evalb (fun i ↦ A.ofName (![σ, D] i)) := by
    simpa [nameMemberFormula] using hxD
  have hσt : boundedPairMemberFormula.Evalb (fun i ↦ A.ofName (![S, σ, t] i)) :=
    (Defined.eval_iff _).mpr hxt
  obtain ⟨u, huG, hu⟩ := (A.formula_truth nameMemberFormula ![σ, D]).mp hσD
  obtain ⟨v, hvG, hv⟩ := (A.formula_truth boundedPairMemberFormula ![S, σ, t]).mp hσt
  change u ∈ forcingFormula P R nameMemberFormula (standardTuple ![σ.val, D.val]) at hu
  rw [forcingFormula_nameMember] at hu
  obtain ⟨a, haG, has, haq⟩ := hG.1.2.2.2 s hsG q hqG
  obtain ⟨b, hbG, hba, hbu⟩ := hG.1.2.2.2 a haG u huG
  obtain ⟨r, hrG, hrb, hrv⟩ := hG.1.2.2.2 b hbG v hvG
  have hr := hG.1.1 r hrG
  have hra := hR.2.2 r hr b (hG.1.1 b hbG) a (hG.1.1 a haG) hrb hba
  refine ⟨r, hr, σ.val, mem_domain_of_kpair_mem hσs,
    hR.2.2 r hr a (hG.1.1 a haG) q hq hra haq, ?_, ?_, ?_⟩
  · exact atomicMembership_mono hR (atomicMembership_of_pair hR (hG.1.1 s hsG) hσs) hr
      (hR.2.2 r hr a (hG.1.1 a haG) s (hG.1.1 s hsG) hra has)
  · exact atomicMembership_mono hR hu hr
      (hR.2.2 r hr b (hG.1.1 b hbG) u (hG.1.1 u huG) hrb hbu)
  · exact (forcingFormula_regular hR boundedPairMemberFormula _).2.1 v hv r hr hrv

private theorem forall_six_eq {α : Type*} (a b c d e f : α) (F : α → α → α → α → α → α → Prop) :
    (∀ u v w x y z, u = a → v = b → w = c → x = d → y = e → z = f → F u v w x y z) ↔ F a b c d e f :=
  ⟨fun h ↦ h a b c d e f rfl rfl rfl rfl rfl rfl,
    fun h u v w x y z hu hv hw hx hy hz ↦ by subst u v w x y z; exact h⟩

private theorem forall_three_eq {α : Type*} (a b c : α) (F : α → α → α → Prop) :
    (∀ u v w, u = a → v = b → w = c → F u v w) ↔ F a b c :=
  ⟨fun h ↦ h a b c rfl rfl rfl,
    fun h u v w hu hv hw ↦ by subst u v w; exact h⟩

theorem eval_twoStepDenseNamesFormula (v : Fin 8 → V) : twoStepDenseNamesFormula.Evalb v ↔
    (IsForcingPreorder (v 0) (v 1) → IsForcingTop (v 0) (v 1) (v 2) →
      IsForcingName (v 0) (v 3) → IsForcingName (v 0) (v 4) → IsForcingName (v 0) (v 5) →
      IsForcingName (v 0) (v 6) → v 7 ∈ v 0 →
      v 7 ∈ forcingFormula (v 0) (v 1) forcingDenseFormula (standardTuple ![v 3, v 4, v 5]) →
      v 7 ∈ atomicMembership (v 0) (v 1) (v 6) (v 3) →
      ∀ q ∈ v 0, ⟨q, v 7⟩ₖ ∈ v 1 → ∃ r ∈ v 0, ∃ σ ∈ domain (v 3),
        ⟨r, q⟩ₖ ∈ v 1 ∧ r ∈ atomicMembership (v 0) (v 1) σ (v 3) ∧
        r ∈ atomicMembership (v 0) (v 1) σ (v 5) ∧
        r ∈ forcingFormula (v 0) (v 1) boundedPairMemberFormula (standardTuple ![v 4, σ, v 6])) := by
  simp [twoStepDenseNamesFormula, Semiformula.eval_nestFormulae, Matrix.vecForall_iff,
    Fin.forall_fin_succ, forall_six_eq, forall_three_eq]

theorem twoStep_dense_names {P R one p : V}
    (hR : IsForcingPreorder P R) (htop : IsForcingTop P R one)
    (Q S D t : ForcingName P) (hp : p ∈ P)
    (hD : p ∈ forcingFormula P R forcingDenseFormula (standardTuple ![Q.val, S.val, D.val]))
    (ht : p ∈ atomicMembership P R t.val Q.val) :
    ∀ q ∈ P, ⟨q, p⟩ₖ ∈ R → ∃ r ∈ P, ∃ σ ∈ domain Q.val,
      ⟨r, q⟩ₖ ∈ R ∧ r ∈ atomicMembership P R σ Q.val ∧ r ∈ atomicMembership P R σ D.val ∧
      r ∈ forcingFormula P R boundedPairMemberFormula (standardTuple ![S.val, σ, t.val]) := by
  have hh := eval_of_countable_zf twoStepDenseNamesFormula (by
    intro W _ _ _ _ v
    apply (eval_twoStepDenseNamesFormula v).mpr
    intro hR htop hQ hS hD ht hp hf hm
    exact twoStep_dense_names_countable hR htop ⟨v 3, hQ⟩ ⟨v 4, hS⟩ ⟨v 5, hD⟩ ⟨v 6, ht⟩ hp hf hm)
    ![P, R, one, Q.val, S.val, D.val, t.val, p]
  exact (eval_twoStepDenseNamesFormula _).mp hh hR htop Q.property S.property D.property t.property hp hD ht

end ZFVP
