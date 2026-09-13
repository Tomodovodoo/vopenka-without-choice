import ZFVP.ModelTheory.InfinitaryExistentialWitness
import ZFVP.ModelTheory.InfinitaryBooleanHenkin
import ZFVP.ModelTheory.InfinitaryLanguageDerivation

namespace ZFVP.Infinitary
open LO LO.FirstOrder
namespace KeislerDerivation
variable {L : Language} [L.Eq]

/-- A Boolean decision and its conjunction witness are followed by one genuinely
fresh existential witness, in the language with one more constant. -/
structure HenkinStep (Γ : Set (Sentence L)) (φ : Sentence L)
    (Δ : Set (Sentence (WithConstants L Unit))) : Prop where
  includes : Formula.lMap (Language.Hom.add₁ L (Language.constant Unit)) '' Γ ⊆ Δ
  countable : Γ.Countable → Δ.Countable
  consistent : Consistent Δ
  decides : φ.lMap (Language.Hom.add₁ L (Language.constant Unit)) ∈ Δ ∨
    .neg (φ.lMap (Language.Hom.add₁ L (Language.constant Unit))) ∈ Δ
  conjunction_witness : ∀ f : ℕ → Sentence L, φ = .conj f →
    (.conj (fun i ↦ (f i).lMap (Language.Hom.add₁ L (Language.constant Unit)))) ∈ Δ ∨
      ∃ i, .neg ((f i).lMap (Language.Hom.add₁ L (Language.constant Unit))) ∈ Δ
  existential_witness : ∀ f : Formula L 1, φ = .exs f →
    .neg (.exs (f.lMap (Language.Hom.add₁ L (Language.constant Unit)))) ∈ Δ ∨
      ExistentialWitness.sentence f ∈ Δ

/-- One scheduled sentence can be decided and witnessed while keeping full
syntactic consistency at this successor stage. -/
theorem exists_henkinStep (Γ : Set (Sentence L)) (hc : Consistent Γ) (φ : Sentence L) :
    ∃ Δ, HenkinStep Γ φ Δ := by
  classical
  obtain ⟨B, hB⟩ := exists_booleanStep Γ hc φ
  let η := Language.Hom.add₁ L (Language.constant Unit)
  let B' : Set (Sentence (WithConstants L Unit)) := Formula.lMap η '' B
  have hcB' : Consistent B' := ExistentialWitness.consistent_lMap hB.2.2.1
  have hbuild (Δ : Set (Sentence (WithConstants L Unit))) (hinc : B' ⊆ Δ)
      (hcount : B.Countable → Δ.Countable) (hcons : Consistent Δ)
      (hw : ∀ f : Formula L 1, φ = .exs f → .neg (.exs (f.lMap η)) ∈ Δ ∨
        ExistentialWitness.sentence f ∈ Δ) : HenkinStep Γ φ Δ := by
    refine ⟨?_, fun hg ↦ hcount (hB.2.1 hg), hcons, ?_, ?_, hw⟩
    · rintro _ ⟨ψ, hψ, rfl⟩
      exact hinc ⟨ψ, hB.1 hψ, rfl⟩
    · rcases hB.2.2.2.1 with hp | hn
      · exact Or.inl (hinc ⟨φ, hp, rfl⟩)
      · exact Or.inr (hinc ⟨.neg φ, hn, rfl⟩)
    · intro f hf
      rcases hB.2.2.2.2 f hf with hp | ⟨i, hi⟩
      · exact Or.inl (hinc ⟨.conj f, hp, rfl⟩)
      · exact Or.inr ⟨i, hinc ⟨.neg (f i), hi, rfl⟩⟩
  by_cases hex : ∃ f : Formula L 1, φ = .exs f
  · obtain ⟨f, rfl⟩ := hex
    rcases hB.2.2.2.1 with hp | hn
    · refine ⟨insert (ExistentialWitness.sentence f) B', hbuild _ (Set.subset_insert _ _) ?_ ?_ ?_⟩
      · intro hb
        exact (hb.image _).insert _
      · exact ExistentialWitness.consistent hB.2.2.1 f (of_mem hp)
      · intro g hg
        cases Formula.exs.inj hg
        exact Or.inr (Set.mem_insert _ _)
    · refine ⟨B', hbuild _ (Set.Subset.refl _) (fun hb ↦ hb.image _) hcB' ?_⟩
      intro g hg
      cases Formula.exs.inj hg
      exact Or.inl ⟨.neg (.exs f), hn, rfl⟩
  · refine ⟨B', hbuild _ (Set.Subset.refl _) (fun hb ↦ hb.image _) hcB' ?_⟩
    intro f hf
    exact (hex ⟨f, hf⟩).elim

end KeislerDerivation
end ZFVP.Infinitary
