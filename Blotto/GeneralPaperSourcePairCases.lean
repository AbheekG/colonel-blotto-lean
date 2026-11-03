import Blotto.GeneralPaperSourcePairContract

/-! All three ACTUAL classifier branches instantiate the pair contract:
none, rich modification, or poor modification. The source and budget
inequalities are derived, rather than supplied as transfer premises.
-/
namespace Blotto.GeneralPaperSourcePairCases
open GeneralPaperProxyParameters GeneralPaperDictionary GeneralPaperSourcePairRun GeneralPaperSourcePairContract
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem unchanged {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=none) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ Contract k Qv hQv weights hp hs b pair := by
  have hUA := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb false
  have hUB := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb true
  have hA := GeneralPaperSourceUnchangedDictionary.bound k Qv hm hQv weights hp hs b hb false b hb.1.le
    (GeneralPaperUnchangedBudgetDirections.none_rich m k b hb hModify)
  have hB := GeneralPaperSourceUnchangedDictionary.bound k Qv hm hQv weights hp hs b hb true (1/b) (one_div_pos.mpr hb.1).le
    (GeneralPaperUnchangedBudgetDirections.none_poor m k b hb hModify)
  refine ⟨⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,
    GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩,?_,hUA,hUB,?_,?_,?_⟩
  · simp only [run,hModify]
  · exact congrArg (fun d => d.label) (GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b false)
  · exact congrArg (fun d => d.label) (GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b true)
  · dsimp only
    rw [show (2:ℝ)/((prepare m k).K:ℝ)=1/((prepare m k).K:ℝ)+1/((prepare m k).K:ℝ) by ring]
    simp only [one_div] at hA hB ⊢
    have hn : (0:ℝ)≤(m:ℝ)/((prepare m k).S:ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hh := (add_le_add hA hB).trans (le_add_of_nonneg_right hn)
    have hh' : @LE.le ℝ Real.instLE _ _ := hh
    convert hh' using 1 <;> first | rfl | ac_rfl

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ Contract k Qv hQv weights hp hs b pair := by
  obtain ⟨d,hRun,hUA,hLabels,hA⟩ := GeneralPaperSourceModifiedDictionary.rich k Qv hm hQv weights hp hs b hb hModify
  have hUB := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb true
  have hB := GeneralPaperSourceUnchangedDictionary.bound k Qv hm hQv weights hp hs b hb true (1/b) (one_div_pos.mpr hb.1).le
    (GeneralPaperUnchangedBudgetDirections.modify_rich m k b hb hModify)
  refine ⟨⟨d,GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩,?_,hUA,hUB,hLabels,?_,?_⟩
  · simp only [run,hModify,hRun,Option.map_some]
  · exact congrArg (fun d => d.label) (GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b true)
  · dsimp only
    rw [show (2:ℝ)/((prepare m k).K:ℝ)=1/((prepare m k).K:ℝ)+1/((prepare m k).K:ℝ) by ring]
    simp only [one_div] at hA hB ⊢
    have hh : @LE.le ℝ Real.instLE _ _ := add_le_add hA hB
    convert hh using 1 <;> first | rfl | ac_rfl

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ Contract k Qv hQv weights hp hs b pair := by
  obtain ⟨d,hRun,hUB,hLabels,hB⟩ := GeneralPaperSourceModifiedDictionary.poor k Qv hm hQv weights hp hs b hb hModify
  have hUA := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb false
  have hA := GeneralPaperSourceUnchangedDictionary.bound k Qv hm hQv weights hp hs b hb false b hb.1.le
    (GeneralPaperUnchangedBudgetDirections.modify_poor m k b hb hModify)
  refine ⟨⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,d⟩,?_,hUA,hUB,?_,hLabels,?_⟩
  · simp only [run,hModify,hRun,Option.map_some]
  · exact congrArg (fun d => d.label) (GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b false)
  · dsimp only
    rw [show (2:ℝ)/((prepare m k).K:ℝ)=1/((prepare m k).K:ℝ)+1/((prepare m k).K:ℝ) by ring]
    simp only [one_div] at hA hB ⊢
    have hh : @LE.le ℝ Real.instLE _ _ := add_le_add hA hB
    convert hh using 1 <;> first | rfl | ac_rfl

end Blotto.GeneralPaperSourcePairCases
