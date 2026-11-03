import Blotto.GeneralPaperInitializerSelectedControls

/-! Actual strict-score preparation at the classified proxy supplies the
stored N-grid auxiliary-polytope point in both defender normalizations.
Input rows retain their original whole-allocation identities; the source
already proves their required hard budgets. No supplied high-tuple/slack
or auxiliary-feasibility oracle is used here.
-/
namespace Blotto.GeneralPaperInitializerPreparedPoint
open GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperTransferPreparation
open GeneralPaperInitializerSelectedControls GeneralPaperAffineConstraintRows
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def ownBudget (m k : ℕ) (b : ℝ) (reciprocal : Bool) : ℚ :=
  if reciprocal then (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value else 1

noncomputable def opposingBudget (m k : ℕ) (b : ℝ) (reciprocal : Bool) : ℚ :=
  if reciprocal then 1 else (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value

theorem own_positive (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) : 0<ownBudget m k b reciprocal := by
  cases reciprocal
  · exact zero_lt_one
  · exact (GeneralPaperProxyClassifier.proxy_unit m k b hb).1

theorem beta_normalized (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    (controls m k b reciprocal).beta=opposingBudget m k b reciprocal/ownBudget m k b reciprocal := by
  rw [beta_value]
  cases reciprocal <;> simp only [ownBudget,opposingBudget,Bool.false_eq_true,ite_false,ite_true,div_one]

theorem prepared {T m K : ℕ} (k : ℕ) (hm : 0<m) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (v : RationalFieldSelector m) (S : ℕ)
    (hRows : ∀ i,Blotto.Feasible (ownBudget m k b reciprocal:ℝ) (fun j => ((rows.read i).read j:ℝ))) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) v S
    let c := controls m k b reciprocal
    let initial := GeneralPaperInitializerDictionary.build p.dictionary c.N c.depth
    UnitDictionary initial hT hK ∧
      GeneralPaperAffineConstraintRows.Feasible p.dictionary.label (score v S) p.threshold
        (c.auxiliary:ℝ) (GeneralPaperTransferPolytopePoint.coordinates initial) ∧
      ∀ j l,OnRationalLattice c.N (initial.anchor j l) := by
  dsimp only
  let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) v S
  let c := controls m k b reciprocal
  have hc := positive m k hm b hb reciprocal
  have hCap := depth_cap m k b reciprocal
  have hu := prepared_unit hT hK hDiv rows (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (own_positive m k b hb reciprocal) v S hRows
  have hOriginal := GeneralPaperTransferPolytopePoint.prepared_feasible hT hK hDiv rows (ownBudget m k b reciprocal)
    (opposingBudget m k b reciprocal) (own_positive m k b hb reciprocal) v S hRows
  change GeneralPaperAffineConstraintRows.Feasible p.dictionary.label (score v S) p.threshold
    ((opposingBudget m k b reciprocal/ownBudget m k b reciprocal:ℚ):ℝ) (GeneralPaperTransferPolytopePoint.coordinates p.dictionary) at hOriginal
  have hBad (l : HighTuple (score v S) p.threshold) : (c.beta:ℝ)≤cost p.dictionary l.val := by
    have hh := (GeneralPaperAffineConstraintSemantics.feasible_iff _ _ _ _ _).mp hOriginal
    have he := hh.2.2.2 l
    rw [GeneralPaperTransferPolytopePoint.tuple_sum p.dictionary hK hu.zero] at he
    rw [beta_normalized]
    exact he
  have hFeasible := GeneralPaperInitializerDictionary.auxiliary_feasible hm p.dictionary hT hK hu (score v S) p.threshold c.beta hBad
    c.N c.depth hc.1 hCap
  have hAux : c.auxiliary=c.beta-(m:ℚ)/c.N := rfl
  have hAuxR : (c.auxiliary:ℝ)=(c.beta:ℝ)-(m:ℝ)/c.N := by
    have he := congrArg (fun q : ℚ => (q:ℝ)) hAux
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_natCast] using he
  refine ⟨GeneralPaperInitializerDictionary.unit p.dictionary hT hK hu c.N c.depth hc.1 hCap,?_,?_⟩
  · rw [hAuxR]
    exact hFeasible
  · intro j l
    exact GeneralPaperInitializerDictionary.lattice p.dictionary c.N c.depth hc.1 j l

end Blotto.GeneralPaperInitializerPreparedPoint
