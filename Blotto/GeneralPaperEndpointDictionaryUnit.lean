import Blotto.GeneralPaperEndpointDictionarySemantics

/-! Literal decoded dictionaries have hard at-most-one budgets on EVERY
whole retained row. UnitDictionary also records balance, zero labels,
monotone bounded anchors and support of the canonical whole-row law.
-/
namespace Blotto.GeneralPaperEndpointDictionaryUnit
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperSourceEndpointBranch
open GeneralPaperEndpointDictionary GeneralPaperDictionary GeneralPaperEndpointDictionarySemantics
open GeneralPaperTransferPreparation
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem from_feasible {T m K : ℕ} (result : Result T m K) (hT : 0<T) (hK : 0<K)
    (hBalanced : Balanced (dictionary result)) (scores : Fin m → Fin K → ℕ) (h : ℕ) (gamma : ℝ)
    (hFull : GeneralPaperAffineConstraintRows.Feasible result.labels scores h gamma (fun a => (coordinates result a:ℝ))) :
    UnitDictionary (dictionary result) hT hK := by
  have hs := (GeneralPaperAffineConstraintSemantics.feasible_iff result.labels scores h gamma _).mp hFull
  have hBounds := anchor_bounds result hs.1
  have hRows := rows result hK hs.2.2.1
  refine ⟨hBalanced,zero_label result hK,ordered result hK hs.2.1,fun j l => (hBounds j l).1,
    fun j l => (hBounds j l).2,?_,?_⟩
  · intro i
    refine ⟨?_,hRows i⟩
    intro j
    change (0:ℝ)≤((dictionary result).anchor j ((dictionary result).label i j):ℝ)
    exact_mod_cast (hBounds j ((dictionary result).label i j)).1
  · exact GeneralPaperDictionary.law_supported (dictionary result) hT 1 (fun j l => (hBounds j l).1) hRows

theorem zero_unit {T m K : ℕ} (ls : Fin T → Fin m → Fin K) (hT : 0<T) (hK : 0<K)
    (hBalanced : Balanced (dictionary (⟨ls,.zero⟩ : Result T m K))) :
    UnitDictionary (dictionary (⟨ls,.zero⟩ : Result T m K)) hT hK := by
  have hOrder : ∀ j,Monotone ((dictionary (⟨ls,.zero⟩ : Result T m K)).anchor j) := by
    intro j a b _
    rw [zero_anchors,zero_anchors]
  have hRows : ∀ i,∑ j,((dictionary (⟨ls,.zero⟩ : Result T m K)).anchor j (ls i j):ℝ)≤1 := by
    intro i
    simp only [zero_anchors,Rat.cast_zero,Finset.sum_const_zero,zero_le_one]
  refine ⟨hBalanced,zero_label _ hK,hOrder,?_,?_,?_,?_⟩
  · intro j l
    rw [zero_anchors]
  · intro j l
    rw [zero_anchors]
    norm_num
  · intro i
    refine ⟨?_,hRows i⟩
    intro j
    change (0:ℝ)≤((dictionary (⟨ls,.zero⟩ : Result T m K)).anchor j (ls i j):ℝ)
    simp only [zero_anchors,Rat.cast_zero,le_refl]
  · exact GeneralPaperDictionary.law_supported _ hT 1 (fun j l => by rw [zero_anchors]) hRows

theorem contract_balanced {T m K : ℕ} (old : Dictionary T m K) (v : RationalFieldSelector m)
    (S h : ℕ) (budget : ℝ) (result : Result T m K) (hContract : Contract old v S h budget result)
    (hBalanced : Balanced old) : Balanced (dictionary result) := by
  intro j l
  change (∑ i : Fin T,if result.labels i j=l then 1/(T:ℝ) else 0)=1/(K:ℝ)
  rw [hContract.1]
  exact hBalanced j l

theorem contract_unit {T m K : ℕ} (old : Dictionary T m K) (v : RationalFieldSelector m)
    (S h : ℕ) (budget : ℝ) (result : Result T m K) (hT : 0<T) (hK : 0<K)
    (hContract : Contract old v S h budget result) (hBalanced : Balanced old) :
    UnitDictionary (dictionary result) hT hK := by
  have hb := contract_balanced old v S h budget result hContract hBalanced
  rcases result with ⟨ls,choice⟩
  cases choice with
  | zero => exact zero_unit ls hT hK hb
  | endpoint gamma point => exact from_feasible _ hT hK hb (GeneralPaperStrictScore.score v S) h (gamma:ℝ) hContract.2.2

end Blotto.GeneralPaperEndpointDictionaryUnit
