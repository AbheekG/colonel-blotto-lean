import Blotto.GeneralPaperTransferDeterminantBounds

/-! The actual normalized dictionary from the actual strict-score DP is
a feasible point of the constructed affine transfer polytope. Its zero
anchors are removed without changing any original row or high-score tuple.
This is the proxy feasible point, before the rational interior initializer
and nonsingular original-basis endpoint continuation are constructed.
-/
namespace Blotto.GeneralPaperTransferPolytopePoint
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperAffineConstraintSemantics
open GeneralPaperDictionary GeneralPaperStrictScore
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

def positiveLabel {K : ℕ} (l : Fin (K-1)) : Fin K := ⟨l.val+1,by omega⟩

noncomputable def coordinates {T m K : ℕ} (d : Dictionary T m K) : Variable m K → ℝ :=
  fun v => (d.anchor v.1 (positiveLabel v.2):ℝ)

theorem coordinate_reference {T m K : ℕ} (d : Dictionary T m K) (hK : 0<K)
    (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) (j : Fin m) (l : Fin K) :
    refValue (coordinates d) (tupleReference j l)=(d.anchor j l:ℝ) := by
  by_cases hz : l.val=0
  · have he : l=⟨0,hK⟩ := Fin.ext hz
    subst l
    simp [tupleReference,reference,refValue,hZero]
  · have hk : l.val≠K := Nat.ne_of_lt l.isLt
    simp only [tupleReference,reference,dite_eq_right hz,dite_eq_right hk,refValue,coordinates]
    congr 1
    apply congrArg (d.anchor j)
    apply Fin.ext
    change (l.val-1)+1=l.val
    omega

theorem tuple_sum {T m K : ℕ} (d : Dictionary T m K) (hK : 0<K)
    (hZero : ∀ j,d.anchor j ⟨0,hK⟩=0) (l : Fin m → Fin K) :
    tupleSum (coordinates d) l=cost d l := by
  unfold tupleSum cost
  exact Finset.sum_congr rfl (fun j _ => coordinate_reference d hK hZero j (l j))

theorem dictionary_feasible {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) (hK : 0<K)
    (hu : GeneralPaperTransferPreparation.UnitDictionary d hT hK)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (gamma : ℝ)
    (hBad : ∀ l : HighTuple scores h,gamma≤cost d l.val) :
    GeneralPaperAffineConstraintRows.Feasible d.label scores h gamma (coordinates d) := by
  apply (feasible_iff d.label scores h gamma (coordinates d)).mpr
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have hl := hu.nonnegative v.1 (positiveLabel v.2)
    have hr := hu.bounded v.1 (positiveLabel v.2)
    change (0:ℝ)≤(d.anchor v.1 (positiveLabel v.2):ℝ) ∧ (d.anchor v.1 (positiveLabel v.2):ℝ)≤1
    exact ⟨by exact_mod_cast hl,by exact_mod_cast hr⟩
  · intro j l
    change refValue (coordinates d) (tupleReference j (⟨l.val,by omega⟩:Fin K))≤
      refValue (coordinates d) (tupleReference j (positiveLabel l))
    rw [coordinate_reference d hK hu.zero,coordinate_reference d hK hu.zero]
    exact_mod_cast hu.ordered j (show (⟨l.val,by omega⟩:Fin K)≤positiveLabel l by change l.val≤l.val+1; omega)
  · intro i
    rw [tuple_sum d hK hu.zero]
    exact (hu.feasible i).2
  · intro l
    rw [tuple_sum d hK hu.zero]
    exact hBad l

theorem prepared_feasible {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (hOwn : 0<ownBudget) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Blotto.Feasible (ownBudget:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    GeneralPaperAffineConstraintRows.Feasible p.dictionary.label (score v S) p.threshold
      ((opposingProxy/ownBudget:ℚ):ℝ) (coordinates p.dictionary) := by
  dsimp only
  let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
  have hu := GeneralPaperTransferPreparation.prepared_unit hT hK hDiv rows ownBudget opposingProxy hOwn v S hRows
  apply dictionary_feasible p.dictionary hT hK hu (score v S) p.threshold _
  intro l
  have hCost : opposingProxy/ownBudget≤rationalCost p.dictionary l.val := by
    by_contra hn
    have hc : rationalCost p.dictionary l.val<opposingProxy/ownBudget := lt_of_not_ge hn
    have hm : l.val∈slackTuples p.dictionary (opposingProxy/ownBudget) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
    have hs : totalScore v S l.val≤GeneralPaperStrictScore.threshold p.dictionary (opposingProxy/ownBudget) v S :=
      Finset.le_sup hm
    have ht := GeneralPaperTransferPreparation.reference_threshold hT hK hDiv rows ownBudget opposingProxy v S
    change GeneralPaperStrictScore.threshold p.dictionary (opposingProxy/ownBudget) v S=p.threshold at ht
    rw [ht] at hs
    have hh : p.threshold<totalScore v S l.val := l.property
    omega
  rw [← rationalCost_cast]
  exact_mod_cast hCost

end Blotto.GeneralPaperTransferPolytopePoint
