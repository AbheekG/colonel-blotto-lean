import Blotto.GeneralPaperBasisEntryPrice

/-! The actual selected source/proxy supplies every premise of the
complete basis entry, including control construction. Unit and bit calls
return the same native controls, auxiliary numerator, rounded dictionary,
shared matrix, final state and invariant. H/proxy/source preparation before
this entry, final compiler/rechecks and simultaneous space remain separate.
-/
namespace Blotto.GeneralPaperBasisEntryActual
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls GeneralPaperBasisStoredProducts
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

def word (m k N depth : ℕ) : ℕ := GeneralPaperInitializerGridActual.word m k N depth+64

theorem capacities (m k N depth : ℕ) :
    1≤word m k N depth ∧ binaryWordWidth (m*((prepare m k).K-1)+3)≤word m k N depth ∧
    binaryWordWidth ((prepare m k).S+2)≤word m k N depth ∧
    binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤word m k N depth ∧
    binaryWordWidth ((prepare m k).S+4)≤word m k N depth ∧ binaryWordWidth N+64≤word m k N depth := by
  have hc := GeneralPaperInitializerGridActual.capacities m k N depth
  unfold word
  omega

theorem control_counters (primitive : ℕ → ℕ) (m k N depth p : ℕ) (hp : 0<p) :
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k N depth) N p hp).1.doublings+1)≤word m k N depth ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k N depth) N p hp).1.work+192)≤word m k N depth :=
  GeneralPaperInitializerControlCounters.loop_counters primitive _ N p hp (capacities m k N depth).2.2.2.2.2

theorem actual_unit_data {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (GeneralPaperBasisEntryPrice.unit (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).1=
      ((controls m k b reciprocal,inputs.betaN),
        (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,GeneralPaperSharedBasisInputs.basis prep inputs)) := by
  dsimp only
  have hc := GeneralPaperInitializerControlWork.data m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
  have hi := GeneralPaperInitializedBasisWork.actual_data k Qv hm hQv weights hp hs b hb reciprocal
  dsimp only at hi
  dsimp only [GeneralPaperBasisEntryPrice.unit]
  rw [hc]
  apply Prod.ext
  · rfl
  · exact hi

theorem actual_bits_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    (GeneralPaperBasisEntryPrice.bits model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).1=
      ((controls m k b reciprocal,inputs.betaN),
        (GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,GeneralPaperSharedBasisInputs.basis prep inputs)) := by
  dsimp only
  exact (GeneralPaperBasisEntryPrice.data model W _ _ _ _ reciprocal _ _ (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperScoreScaleParameters.score_cap m k)).trans (actual_unit_data k Qv hm hQv weights hp hs b hb reciprocal)

def unitProfile (T m K S scoreDepth N depth : ℕ) : ℕ :=
  12*binaryWordWidth N+194+GeneralPaperInitializedBasisWork.profile T m K S scoreDepth depth+24

def bitProfile (model : RationalCostModel) (W m k Qv N depth : ℕ) : ℕ :=
  1024*(binaryWordWidth N+1)*(W+model.rat (96+64*binaryWordWidth N))+
    GeneralPaperInitializedBasisBits.profile model W m k Qv N depth+24*W

theorem actual_unit_work {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let c := controls m k b reciprocal
    (GeneralPaperBasisEntryPrice.unit (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).2≤
      unitProfile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
        (GeneralPaperScoreScaleParameters.prepare m k).depth c.N c.depth := by
  dsimp only
  have hc := GeneralPaperInitializerControlWork.data m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
  have hcCost := GeneralPaperInitializerControlWork.work m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
  change (GeneralPaperInitializerControlWork.run m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal).2≤
      12*binaryWordWidth (controls m k b reciprocal).N+194 at hcCost
  have hiCost := GeneralPaperInitializedBasisWork.actual_work k Qv hm hQv weights hp hs b hb reciprocal
  change (GeneralPaperInitializedBasisWork.run _ _ _ (controls m k b reciprocal)
    (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal)).2≤_ at hiCost
  dsimp only [GeneralPaperBasisEntryPrice.unit]
  rw [hc]
  dsimp only
  change (GeneralPaperInitializerControlWork.run _ _ _ _ reciprocal).2+
    (GeneralPaperInitializedBasisWork.run _ _ _ (controls m k b reciprocal) _).2+24≤_
  unfold unitProfile
  omega

theorem actual_bits_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W) (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let c := controls m k b reciprocal
    (GeneralPaperBasisEntryPrice.bits model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).2≤
      bitProfile model W m k Qv c.N c.depth := by
  dsimp only
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hc := (GeneralPaperInitializerControlBits.data model W m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal).trans
      (GeneralPaperInitializerControlWork.data m (prepare m k).H
        (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal)
  have hcCost := GeneralPaperInitializerControlBits.positive_work model W m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal
    hm (H_positive m k) hf.1 (hf.1.trans hf.2.1)
  change (GeneralPaperInitializerControlBits.run model W m (prepare m k).H
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal).2≤
      1024*(binaryWordWidth (controls m k b reciprocal).N+1)*(W+model.rat (96+64*binaryWordWidth (controls m k b reciprocal).N)) at hcCost
  have hiCost := GeneralPaperInitializedBasisBits.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinal
  change (GeneralPaperInitializedBasisBits.run model W _ _ _ (controls m k b reciprocal)
    (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den reciprocal)).2≤_ at hiCost
  dsimp only [GeneralPaperBasisEntryPrice.bits]
  rw [hc]
  dsimp only
  change (GeneralPaperInitializerControlBits.run model W _ _ _ _ reciprocal).2+
    (GeneralPaperInitializedBasisBits.run model W _ _ _ (controls m k b reciprocal) _).2+24*W≤_
  unfold bitProfile
  omega

theorem actual_returns {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let c := controls m k b reciprocal
    let W := word m k c.N c.depth
    ∃ state,
      (GeneralPaperBasisEntryPrice.unit (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).1=
        ((c,inputs.betaN),(GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,some state)) ∧
      (GeneralPaperBasisEntryPrice.bits model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).1=
        ((c,inputs.betaN),(GeneralPaperSourceInitializer.initial k Qv hQv weights hp hs b reciprocal,inputs.matrix,some state)) ∧
      GeneralPaperBasisInvariant.Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      (GeneralPaperBasisEntryPrice.unit (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).2≤
        unitProfile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
          (GeneralPaperScoreScaleParameters.prepare m k).depth c.N c.depth ∧
      (GeneralPaperBasisEntryPrice.bits model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).H f.num f.den reciprocal prep v).2≤
        bitProfile model W m k Qv c.N c.depth := by
  dsimp only
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  have hu := actual_unit_data k Qv hm hQv weights hp hs b hb reciprocal
  have hd := actual_bits_data model (word m k (controls m k b reciprocal).N (controls m k b reciprocal).depth)
    k Qv hm hQv weights hp hs b hb reciprocal
  dsimp only at hu hd
  rw [hr] at hu hd
  have hw := capacities m k (controls m k b reciprocal).N (controls m k b reciprocal).depth
  exact ⟨state,hu,hd,inv,actual_unit_work k Qv hm hQv weights hp hs b hb reciprocal,
    actual_bits_work model _ k Qv hm hQv weights hp hs b hb reciprocal hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1⟩

end Blotto.GeneralPaperBasisEntryActual
