import Blotto.GeneralPaperEndpointDictionaryUnit

/-! Security of the actual decoded zero/endpoint dictionary against ALL
real deviations. Original row identity, repeated labels and half ties are
preserved. Exactly m/S is added for this one modified defender.
-/
namespace Blotto.GeneralPaperEndpointContractSecurity
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperSourceEndpointBranch
open GeneralPaperEndpointDictionary GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperTransferPreparation
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem replacement {T m K : ℕ} (old : Dictionary T m K) (result : Result T m K)
    (hLabels : result.labels=old.label) : dictionary result=replace old (dictionary result).anchor :=
  congrArg (fun ls : Fin T → Fin m → Fin K => (⟨ls,(dictionary result).anchor⟩ : Dictionary T m K)) hLabels

theorem zero_replacement {T m K : ℕ} (old : Dictionary T m K) (ls : Fin T → Fin m → Fin K)
    (hLabels : ls=old.label) : dictionary (⟨ls,.zero⟩ : Result T m K)=replace old (fun _ _ => 0) := by
  have hh := replacement old (⟨ls,.zero⟩ : Result T m K) hLabels
  have he : (dictionary (⟨ls,.zero⟩ : Result T m K)).anchor=(fun _ _ => 0) := by
    funext j l
    exact zero_anchors ls j l
  rwa [he] at hh

theorem bound {T m K : ℕ} (old : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hu : UnitDictionary old hT hK) (v : RationalFieldSelector m) (S : ℕ) (hS : 0<S)
    (oldBudget : ℚ) (hOldBudget : 0<oldBudget) (h : ℕ) (hThreshold : threshold old oldBudget v S=h)
    (budget : ℝ) (hBudget : 0≤budget) (result : Result T m K) (hc : Contract old v S h budget result) :
    security v.values budget (law (dictionary result) hT).law≤
      security v.values (oldBudget:ℝ) (law old hT).law+(m:ℝ)/(S:ℝ) := by
  have hNew := GeneralPaperEndpointDictionaryUnit.contract_unit old v S h budget result hT hK hc hu.balanced
  rcases result with ⟨ls,choice⟩
  cases choice with
  | zero =>
    rw [zero_replacement old ls hc.1]
    apply empty_bad_security_bound old hT hK hu.balanced v S hS hu.ordered hu.nonnegative hu.zero oldBudget hOldBudget
      _ budget hBudget
    intro labels
    rw [hThreshold]
    exact hc.2 labels
  | endpoint gamma point =>
    have hFull : GeneralPaperAffineConstraintRows.Feasible ls (score v S) h (gamma:ℝ)
        (fun a => (coordinates (⟨ls,.endpoint gamma point⟩ : Result T m K) a:ℝ)) := hc.2.2
    have hHigh := GeneralPaperEndpointDictionarySemantics.high_tuples (⟨ls,.endpoint gamma point⟩ : Result T m K) hK
      (score v S) h (gamma:ℝ) ((GeneralPaperAffineConstraintSemantics.feasible_iff ls (score v S) h (gamma:ℝ) _).mp hFull).2.2.2
    rw [replacement old _ hc.1]
    apply endpoint_security_bound old _ hT hK hu.balanced v S hS oldBudget hOldBudget hu.ordered hu.nonnegative hu.zero
      hNew.ordered hNew.zero budget (gamma:ℝ) hBudget hc.2.1
    intro labels hScore
    have hScore' : h<totalScore v S labels := by rwa [hThreshold] at hScore
    have hh := hHigh ⟨labels,hScore'⟩
    rwa [replacement old _ hc.1] at hh

end Blotto.GeneralPaperEndpointContractSecurity
