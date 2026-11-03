import Blotto.GeneralPaperCheckedBranchSize

/-! The actual returned pair carries the short-entry theorem on whichever
defender was modified. Unchanged dictionaries retain the earlier source
height route; a full compiler/bit/space price is not inferred here.
-/
namespace Blotto.GeneralPaperCheckedPairEndpointSize
open GeneralPaperProxyParameters GeneralPaperEndpointDictionarySize
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem run_contract {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,GeneralPaperCheckedSourcePair.run k Qv hQv weights hp hs b=some pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair ∧
      ((GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich →
        ∀ j l,RationalHeight (pair.rich.anchor j l) (width m k)) ∧
      ((GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor →
        ∀ j l,RationalHeight (pair.poor.anchor j l) (width m k)) := by
  obtain ⟨pair,hr,hc⟩ := GeneralPaperCheckedSourcePair.run_contract k Qv hm hQv weights hp hs b hb
  refine ⟨pair,hr,hc,?_,?_⟩
  · intro hModify
    obtain ⟨d,hd,hsz⟩ := GeneralPaperCheckedBranchSize.rich_modified k Qv hm hQv weights hp hs b hb hModify
    have hPair : some pair=some (GeneralPaperSourcePairRun.Pair.mk d (GeneralPaperSourceUnchangedDictionary.run k Qv weights b true)) := by
      rw [←hr]
      simp only [GeneralPaperCheckedSourcePair.run,hModify,hd,Option.map_some]
    have he := congrArg GeneralPaperSourcePairRun.Pair.rich (Option.some.inj hPair)
    rw [he]
    exact hsz
  · intro hModify
    obtain ⟨d,hd,hsz⟩ := GeneralPaperCheckedBranchSize.poor_modified k Qv hm hQv weights hp hs b hb hModify
    have hPair : some pair=some (GeneralPaperSourcePairRun.Pair.mk (GeneralPaperSourceUnchangedDictionary.run k Qv weights b false) d) := by
      rw [←hr]
      simp only [GeneralPaperCheckedSourcePair.run,hModify,hd,Option.map_some]
      rfl
    have he := congrArg GeneralPaperSourcePairRun.Pair.poor (Option.some.inj hPair)
    rw [he]
    exact hsz

end Blotto.GeneralPaperCheckedPairEndpointSize
