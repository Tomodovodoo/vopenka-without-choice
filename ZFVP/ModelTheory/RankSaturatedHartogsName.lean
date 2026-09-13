import ZFVP.ModelTheory.RankInternalHartogsName
import ZFVP.ModelTheory.RankForcingNameHierarchy
import ZFVP.ModelTheory.TransitiveZFSaturatedName
import ZFVP.ModelTheory.SaturatedNameGenericEquality
import ZFVP.ModelTheory.SaturatedHartogsFormulas

namespace ZFVP
open LO LO.FirstOrder LO.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [Countable V]
variable {ξ : V} [IsOrdinal ξ] [Nonempty (SetDomain (hierarchy ξ))]
  [(SetDomain (hierarchy ξ))↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem rank_saturatedHartogsPosetName_val_countable (hξ : IsChoicelessInaccessible ξ)
    (P R one κ γ : SetDomain (hierarchy ξ)) (hR : IsForcingPreorder P R)
    (ht : IsForcingTop P R one) (hγ : IsOrdinal γ) :
    (saturatedHartogsPosetName P R one κ γ).val =
      saturatedHartogsPosetName P.val R.val one.val κ.val γ.val := by
  let := hierarchy_transitive ξ
  let := (TransitiveZF.ordinal_iff (hierarchy ξ) γ).mp hγ
  have hR' := (TransitiveZF.forcingPreorder_iff (hierarchy ξ) P R).mp hR
  have ht' := (TransitiveZF.forcingTop_iff (hierarchy ξ) P R one).mp ht
  let Q : ForcingName P.val := ⟨(woodinCollapseName P R (hartogsNumberName P R (checkName one κ)) (checkName one γ)).val,
    (TransitiveZF.forcingName_iff (hierarchy ξ) P _).mp (woodinCollapseName_isName _ _ _ _)⟩
  let Q' : ForcingName P.val := ⟨woodinCollapseName P.val R.val (hartogsNumberName P.val R.val (checkName one.val κ.val)) (checkName one.val γ.val),
    woodinCollapseName_isName _ _ _ _⟩
  unfold saturatedHartogsPosetName saturatedWoodinCollapseName
  rw [TransitiveZF.forcingSaturatedName_val,
    rank_forcingNameHierarchy_val (fun _ hb ↦ regularCardinal_succ_closed hξ.regular hb) P γ hγ]
  apply forcingSaturatedName_eq_of_all_values hR' ht' _ Q Q'
  intro G hG
  let A : ForcingContext V := ⟨P.val, R.val, one.val, G, hR', ht', hG⟩
  have hi : A.ofName Q = woodinCollapse (hartogsNumber (A.check κ.val)) (A.check γ.val) :=
    A.rankInternalHartogsCollapse_value hξ P R one κ γ rfl rfl rfl ht.1 hγ
  let τ : ForcingName P.val := ⟨checkName one.val κ.val, checkName_isName ht'.1 κ.val⟩
  let cκ := A.hartogsName τ
  let cγ : ForcingName P.val := ⟨checkName one.val γ.val, checkName_isName ht'.1 γ.val⟩
  let : IsOrdinal (A.ofName cγ) := by change IsOrdinal (A.check γ.val); infer_instance
  have ho : A.ofName Q' = woodinCollapse (hartogsNumber (A.check κ.val)) (A.check γ.val) := by
    have hh := A.collapseName_value_of_ordinal cκ cγ
    have hk : A.ofName cκ = hartogsNumber (A.check κ.val) := A.hartogsName_value τ
    rw [hk] at hh
    exact hh
  exact hi.trans ho.symm

end ZFVP
