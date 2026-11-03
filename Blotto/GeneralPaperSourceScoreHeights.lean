import Blotto.GeneralPaperSharedBasisBits
import Blotto.GeneralPaperScoreMatrixBits

/-! Actual integer source values and closed candidate anchors supply the
score matrix's height premises. Invalid decoded codes give zero. Candidates
are closed, so their bounds do not include the open-response shift. The
original integer value denominator stays explicit until the input join.
-/
namespace Blotto.GeneralPaperSourceScoreHeights
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem weight_le {m : ℕ} (Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (hs : ∑ j,weights.read j=Qv) (j : Fin m) : weights.read j≤Qv := by
  rw [←hs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem value_height {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (j : Fin m) :
    RationalHeight ((GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).weight j)
      (binaryWordWidth Qv) := by
  have hh := RationalHeight.fraction (weights.read j:ℤ) Qv (binaryWordWidth Qv) hQv
    (by simpa only [Int.natAbs_natCast] using (weight_le Qv weights hs j).trans_lt (lt_pow_binaryWordWidth Qv))
    (lt_pow_binaryWordWidth Qv)
  simpa only [GeneralPaperNativeRationalValues.selector,Int.cast_natCast] using hh

theorem decoded_height (m qbar : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (code : ℕ) :
    RationalHeight (GeneralPaperCatalogueRationalTrajectory.decodeValue m qbar a code) (binaryWordWidth a.C) := by
  cases hd : (GeneralPaperCodeDecode.decode a false code).choice with
  | none =>
    rw [GeneralPaperCatalogueRationalTrajectory.decodeValue,hd]
    exact GeneralPaperQuantizedHeight.zero_height _ (binaryWordWidth_pos _)
  | some choice =>
    have hc := GeneralPaperCodeDecodeSound.candidate_closed a code choice hd
    have hDen := (Farey.value_den_le choice.threshold).trans
      (GeneralPaperCodeDecodeSound.decode_sound a false code choice hd).2
    have hu := GeneralPaperCodeOrder.decoded_threshold_le_one a false code choice hd
    have hAbs : |choice.threshold.value|≤(1:ℚ) := by
      rw [abs_of_nonneg (Farey.value_nonnegative _)]
      exact hu
    have hNum := rationalLattice_abs_numerator_le (M:=1) choice.threshold.value.den_pos
      (show OnRationalLattice choice.threshold.value.den choice.threshold.value from dvd_refl _) hAbs
    simp only [one_mul] at hNum
    simp only [GeneralPaperCatalogueRationalTrajectory.decodeValue,hd,GeneralPaperCodeAlphabet.Choice.physical,hc,
      Bool.false_eq_true,ite_false,add_zero]
    exact ⟨(hNum.trans hDen).trans_lt (lt_pow_binaryWordWidth _),hDen.trans_lt (lt_pow_binaryWordWidth _)⟩

theorem rows_height {m : ℕ} (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool)
    (i : Fin (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) (j : Fin m) :
    RationalHeight (((GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal).read i).read j)
      (binaryWordWidth (alphabet m k).C) := by
  simp only [GeneralPaperSourceInitializer.sourceRows,GeneralPaperCatalogueRationalTrajectory.rows,FixedArrayTable.read_ofFn]
  exact decoded_height _ _ _ _

theorem proxy_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) :
    RationalHeight (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value (binaryWordWidth (prepare m k).qbar) := by
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hn : f.num≤(prepare m k).qbar := hf.2.1.le.trans hf.2.2
  exact RationalHeight.fraction (f.num:ℤ) f.den _ f.den_pos
    (by simpa only [Int.natAbs_natCast] using hn.trans_lt (lt_pow_binaryWordWidth _))
    (hf.2.2.trans_lt (lt_pow_binaryWordWidth _))

theorem own_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    RationalHeight (ownBudget m k b reciprocal) (binaryWordWidth (prepare m k).qbar) := by
  cases reciprocal with
  | false =>
    change RationalHeight 1 _
    have hh : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
    exact hh.mono (binaryWordWidth_pos _)
  | true => exact proxy_height m k b hb

def anchorHeight (m k : ℕ) : ℕ := binaryWordWidth (alphabet m k).C+binaryWordWidth (prepare m k).qbar

theorem prepared_anchors {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (j : Fin m) (l : Fin (prepare m k).K) :
    RationalHeight ((GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary.anchor j l)
      (anchorHeight m k) := by
  exact GeneralPaperQuantizedHeight.prepared_height
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal)
    (opposingBudget m k b reciprocal) (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S _ _
    (rows_height k Qv weights b reciprocal) (own_height m k b hb reciprocal) j l

end Blotto.GeneralPaperSourceScoreHeights
