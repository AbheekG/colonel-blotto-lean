import Blotto.GeneralPaperInitializerGridPrice

/-! The actual selected source and classifier discharge every rounded-grid
input/height/local-capacity premise. This prices the initializer's arrays
and packing on supplied constructed controls; the construction of those
controls and the auxiliary budget numerator is still a separate obligation.
-/
namespace Blotto.GeneralPaperInitializerGridActual
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

theorem source_unit {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    GeneralPaperTransferPreparation.UnitDictionary
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k) := by
  exact GeneralPaperTransferPreparation.prepared_unit
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (own_positive m k b hb reciprocal) (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
    (GeneralPaperSourceInitializer.source_rows_feasible k Qv hm hQv weights hs b hb reciprocal)

def word (m k N depth : ℕ) : ℕ := GeneralPaperScoreBasisControls.word m k+depth+binaryWordWidth N+8

theorem capacities (m k N depth : ℕ) :
    1≤word m k N depth ∧ binaryWordWidth (m*((prepare m k).K-1)+3)≤word m k N depth ∧
    binaryWordWidth ((prepare m k).S+2)≤word m k N depth ∧
    binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤word m k N depth ∧
    binaryWordWidth ((prepare m k).S+4)≤word m k N depth ∧
    depth+2≤word m k N depth ∧ binaryWordWidth N≤word m k N depth := by
  have hc := GeneralPaperScoreBasisControls.capacities m k
  unfold word
  omega

theorem actual_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let c := controls m k b reciprocal
    (GeneralPaperInitializerGridPrice.run model W c.N c.depth prep.dictionary).1=
      (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.initialGrid) := by
  dsimp only
  exact GeneralPaperInitializerGridPrice.data model W _ _ _ (positive m k hm b hb reciprocal).1

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let c := controls m k b reciprocal
    (GeneralPaperInitializerGridPrice.run model W c.N c.depth prep.dictionary).2≤
      GeneralPaperInitializerGridPrice.profile model W c.N c.depth (GeneralPaperSourceScoreHeights.anchorHeight m k) m (prepare m k).K := by
  dsimp only
  have hu := source_unit k Qv hm hQv weights hp hs b hb reciprocal
  have hc := GeneralPaperBasisBitEnvelope.index_capacities m k W hm hDim
  exact GeneralPaperInitializerGridPrice.work model W _ _ _ _ (positive m k hm b hb reciprocal).1 (depth_cap m k b reciprocal)
    (fun j l => ⟨hu.nonnegative j l,hu.bounded j l⟩)
    (GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal) hW hc.2.1 hc.2.2 hc.1

theorem actual_word_bound (m k : ℕ) (hm : 0<m) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    word m k (controls m k b reciprocal).N (controls m k b reciprocal).depth≤
      32*(binaryWordWidth (m*((prepare m k).K-1)+3)+binaryWordWidth ((prepare m k).S+4)+
        binaryWordWidth m+binaryWordWidth (prepare m k).H+binaryWordWidth (prepare m k).qbar+1) := by
  have hw := GeneralPaperScoreBasisControls.word_bound m k hm
  have hd := depth_width m k b reciprocal
  have hn := N_width m k b hb reciprocal
  unfold word
  omega

theorem actual_operand_width (m k : ℕ) (b : ℝ) (reciprocal : Bool) :
    GeneralPaperInitializerGridPrice.width (GeneralPaperSourceScoreHeights.anchorHeight m k)
      (controls m k b reciprocal).N (controls m k b reciprocal).depth m (prepare m k).K≤
        32*((alphabet m k).lambda+binaryWordWidth (controls m k b reciprocal).N+binaryWordWidth (m*((prepare m k).K-1)+1)+1) := by
  have ha := GeneralPaperSourceAlphabetLower.anchor_height m k
  have hd := depth_width m k b reciprocal
  unfold GeneralPaperInitializerGridPrice.width GeneralPaperInitializerRoundingBits.width
  omega

end Blotto.GeneralPaperInitializerGridActual
