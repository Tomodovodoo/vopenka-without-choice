import ZFVP.SetTheory.WoodinClosedContainers
import ZFVP.SetTheory.BoundedStarDependentChoice
import ZFVP.SetTheory.BoundedDomainRelativization
import ZFVP.Syntax.LevyPackParameters

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory

def starCertificateEnvelopeFormula (ψ : SetTheorySemisentence 3) : SetTheorySemisentence 2 :=
  “aD B. !IsTransitive.dfn B ∧ ∃ a ∈ B, ∃ D ∈ B, !boundedKpairFormula aD a D ∧
    ∃ b ∈ B, ∃ c ∈ B, !boundedFunctionClosedFormula B D b ∧ !ψ a b c”

theorem starCertificateEnvelopeFormula_bounded {ψ : SetTheorySemisentence 3}
    (hψ : IsBoundedSetFormula ψ) : IsBoundedSetFormula (starCertificateEnvelopeFormula ψ) :=
  .and (isTransitiveFormula_bounded.subst _) (.exs (.bvar 1) (.exs (.bvar 2)
    (.and (boundedKpairFormula_bounded.subst _) (.exs (.bvar 3) (.exs (.bvar 4)
      (.and (boundedFunctionClosedFormula_bounded.subst _) (hψ.subst _)))))))

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem eval_starCertificateEnvelopeFormula (ψ : SetTheorySemisentence 3) (a D B : V) :
    (starCertificateEnvelopeFormula ψ).Evalb ![⟨a, D⟩ₖ, B] ↔
      IsTransitive B ∧ a ∈ B ∧ D ∈ B ∧ ∃ b ∈ B, ∃ c ∈ B,
        IsBoundedFunctionClosed B D b ∧ ψ.Evalb ![a, b, c] := by
  simp [starCertificateEnvelopeFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]

theorem IsSigmaOneStarCorrect.reflect_rankClosed_certificate {δ γ α a : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ)
    (ha : a ∈ hierarchy γ) {ψ : SetTheorySemisentence 3} (hψ : IsBoundedSetFormula ψ)
    (hex : ∃ b c : V, IsRankFunctionClosed α b ∧ ψ.Evalb ![a, b, c]) :
    ∃ b ∈ hierarchy γ, ∃ c ∈ hierarchy γ,
      IsRankFunctionClosed α b ∧ ψ.Evalb ![a, b, c] := by
  let := hγ.1.ordinal
  let := IsOrdinal.of_mem hα
  have hD : hierarchy α ∈ hierarchy γ := hγ.1.hierarchy_closed inferInstance
    (ordinal_mem_hierarchy_iff.mpr hα)
  have hpair := kpair_mem_hierarchy_limit hγ.1.successor_closed ha hD
  have henv : ∃ B : V, IsRankFunctionClosed α B ∧
      (starCertificateEnvelopeFormula ψ).Evalb ![⟨a, hierarchy α⟩ₖ, B] := by
    obtain ⟨b, c, hb, hc⟩ := hex
    obtain ⟨B, hB, hp, ht⟩ := hδ.exists_functionClosed_container α ⟨⟨a, hierarchy α⟩ₖ, ⟨b, c⟩ₖ⟩ₖ
    let := ht
    obtain ⟨hap, hbc⟩ := kpair_components_mem_transitive hp
    obtain ⟨haB, hDB⟩ := kpair_components_mem_transitive hap
    obtain ⟨hbB, hcB⟩ := kpair_components_mem_transitive hbc
    refine ⟨B, hB, (eval_starCertificateEnvelopeFormula ψ a (hierarchy α) B).mpr
      ⟨ht, haB, hDB, b, hbB, c, hcB, ?_, hc⟩⟩
    exact fun f _ hf ↦ hb f hf
  obtain ⟨B, hBγ, hclosed, henv⟩ := hγ.reflect hα hpair
    (starCertificateEnvelopeFormula_bounded hψ) henv
  obtain ⟨ht, _, _, b, hb, c, hc, hf, hψbc⟩ :=
    (eval_starCertificateEnvelopeFormula ψ a (hierarchy α) B).mp henv
  refine ⟨b, (hierarchy_transitive γ).mem_trans hb hBγ,
    c, (hierarchy_transitive γ).mem_trans hc hBγ, ?_, hψbc⟩
  intro f hff
  exact hf f (hclosed f (mem_function_of_mem_function_of_subset hff (ht.transitive b hb))) hff

def starSigmaOneSupportFormula (φ : SetTheorySemisentence 2) : SetTheorySemisentence 3 :=
  “a b T. !IsTransitive.dfn T ∧ a ∈ T ∧ b ∈ T ∧
    !(boundedDomainRelativize φ (.bvar 2) (Rew.subst ![.bvar 0, .bvar 1])) a b T”

theorem starSigmaOneSupportFormula_bounded (φ : SetTheorySemisentence 2) :
    IsBoundedSetFormula (starSigmaOneSupportFormula φ) :=
  .and (isTransitiveFormula_bounded.subst _) (.and (.rel _ _) (.and (.rel _ _)
    ((boundedDomainRelativize_bounded φ _ _).subst _)))

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem eval_starSigmaOneSupportFormula (φ : SetTheorySemisentence 2) (a b T : V) :
    (starSigmaOneSupportFormula φ).Evalb ![a, b, T] ↔
      IsTransitive T ∧ ∃ ha : a ∈ T, ∃ hb : b ∈ T,
        φ.Evalb (![⟨a, ha⟩, ⟨b, hb⟩] : Fin 2 → SetDomain T) := by
  simp [starSigmaOneSupportFormula, Matrix.comp_vecCons', Function.comp_def, Matrix.constant_eq_singleton]
  intro _
  change (a ∈ T ∧ b ∈ T ∧
    (boundedDomainRelativize φ (.bvar 2) (Rew.subst ![.bvar 0, .bvar 1])).Evalb ![a, b, T]) ↔ _
  constructor
  · rintro ⟨ha, hb, hφ⟩
    refine ⟨ha, hb, ?_⟩
    apply (eval_boundedDomainRelativize φ _ _ ![⟨a, ha⟩, ⟨b, hb⟩] ![a, b, T] rfl ?_).mp hφ
    intro s
    cases s with
    | bvar i => exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    | fvar e => exact Empty.elim e
    | func f ts => exact Empty.elim f
  · rintro ⟨ha, hb, hφ⟩
    refine ⟨ha, hb, ?_⟩
    apply (eval_boundedDomainRelativize φ _ _ ![⟨a, ha⟩, ⟨b, hb⟩] ![a, b, T] rfl ?_).mpr hφ
    intro s
    cases s with
    | bvar i => exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
    | fvar e => exact Empty.elim e
    | func f ts => exact Empty.elim f

theorem IsSigmaOneStarCorrect.reflect_rankClosed_sigmaOne {δ γ α a : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ)
    (ha : a ∈ hierarchy γ) {φ : SetTheorySemisentence 2} (hφ : IsSigmaFormula 1 φ)
    (hex : ∃ b : V, IsRankFunctionClosed α b ∧ φ.Evalb ![a, b]) :
    ∃ b ∈ hierarchy γ, IsRankFunctionClosed α b ∧ φ.Evalb ![a, b] := by
  have hw : ∃ b T : V, IsRankFunctionClosed α b ∧
      (starSigmaOneSupportFormula φ).Evalb ![a, b, T] := by
    obtain ⟨b, hc, hb⟩ := hex
    obtain ⟨T, ht, hn, hv, hs⟩ := (sigmaOneTruth_correct hφ ![a, b]).mpr hb
    have haT : a ∈ T := standardTuple_values_mem ![a, b] hv 0
    have hbT : b ∈ T := standardTuple_values_mem ![a, b] hv 1
    exact ⟨b, T, hc, (eval_starSigmaOneSupportFormula φ a b T).mpr
      ⟨ht, haT, hbT, (membershipSatisfies_encode hn φ ![⟨a, haT⟩, ⟨b, hbT⟩]).mp hs⟩⟩
  obtain ⟨b, hb, T, _, hc, ht⟩ := hγ.reflect_rankClosed_certificate hδ hα ha
    (starSigmaOneSupportFormula_bounded φ) hw
  obtain ⟨hT, haT, hbT, hs⟩ := (eval_starSigmaOneSupportFormula φ a b T).mp ht
  let := hT
  refine ⟨b, hb, hc, ?_⟩
  have hu := sigma_one_upward T hφ ![⟨a, haT⟩, ⟨b, hbT⟩] hs
  have hv : (fun i ↦ ((![⟨a, haT⟩, ⟨b, hbT⟩] : Fin 2 → SetDomain T) i).val) = ![a, b] := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ Fin.elim0 k) j) i
  rwa [hv] at hu

theorem IsSigmaOneStarCorrect.reflect_rankClosed_sigmaOne_parameters {δ γ α : V}
    (hδ : IsWoodinSupercompact δ) (hγ : IsSigmaOneStarCorrect γ) (hα : α ∈ γ)
    {n : ℕ} {φ : SetTheorySemisentence (n + 1)} (hφ : IsSigmaFormula 1 φ)
    (v : Fin n → V) (hv : ∀ i, v i ∈ hierarchy γ)
    (hex : ∃ b : V, IsRankFunctionClosed α b ∧ φ.Evalb (b :> v)) :
    ∃ b ∈ hierarchy γ, IsRankFunctionClosed α b ∧ φ.Evalb (b :> v) := by
  let := hγ.1.ordinal
  let ψ : SetTheorySemisentence 2 := (levyPackParameters .sigma φ).subst ![.bvar 1, .bvar 0]
  have hψ : IsSigmaFormula 1 ψ := (levyPackParameters_levy hφ (by omega)).subst _
  have he (b : V) : ψ.Evalb ![standardTuple v, b] ↔ φ.Evalb (b :> v) := by
    simpa only [ψ, Semiformula.eval_substs, Matrix.comp_vecCons', Function.comp_def,
      Matrix.constant_eq_singleton, Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_eq] using
      eval_levyPackParameters .sigma φ b v
  have hp := standardTuple_mem_hierarchy_limit hγ.1.omega_lt hγ.1.successor_closed v hv
  obtain ⟨b, hb, hc, ht⟩ := hγ.reflect_rankClosed_sigmaOne hδ hα hp hψ (by
    obtain ⟨b, hc, ht⟩ := hex
    exact ⟨b, hc, (he b).mpr ht⟩)
  exact ⟨b, hb, hc, (he b).mp ht⟩

end ZFVP
