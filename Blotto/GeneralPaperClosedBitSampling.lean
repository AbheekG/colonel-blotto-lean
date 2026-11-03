import Blotto.GeneralPaperCachedBitSampling

/-! Actual returned closed samplers inherit bounded output heights and
full operand-sensitive bit work from their native physical columns.
The local price reference is erased analysis, not a runtime size pass.
Global preparation/space reference composition remains a separate join. -/
namespace Blotto.GeneralPaperClosedBitSampling
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperOriginalDrawEquilibrium
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def outputHeight {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (B H : ℕ) : ℕ :=
  (B+1)+(binaryWordWidth o.representatives+2*binaryWordWidth o.classified.lightWeight+H)

def profile {n : ℕ} (model : RationalCostModel) (A Rb k B H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperCachedBitSampling.profile model A Rb (k+6) o.representatives o.classified.lightWeight
      (GeneralPaperNativeSelectedSecurity.count k) (B+1) H n o.classified.light.size o.classified.heavy.size+
    GeneralPaperCachedBitSampling.directProfile model A Rb (k+6) (B+1) H n+128*A

theorem scale_height (b : ℚ) (B : ℕ) (hB : RationalHeight b B) (reciprocal : Bool) :
    RationalHeight (if reciprocal then b else 1) (B+1) := by
  cases reciprocal
  · exact (show RationalHeight (1:ℚ) 1 by norm_num [RationalHeight]).mono (by omega)
  · exact hB.mono (by omega)

theorem source_sampler_bounds {n : ℕ} (model : RationalCostModel) (Wv k Ap A B H : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hB : RationalHeight b B) (hA : 1≤A) :
    let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ (physical : Columns t.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K),
      (∀ j l,RationalHeight ((physical.rich.read j).anchors.read l) H) →
      (∀ j l,RationalHeight ((physical.poor.read j).anchors.read l) H) →
      1+binaryWordWidth (2*n+o.representatives+2)≤A → binaryWordWidth (t.rows+1)≤A →
      let description := (make model.rat (fun w => w) Ap o
        (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
        (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1
      let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
        ⟨o,b,GeneralPaperSamplingControls.specification t.rows t.rowBits k hRows,description⟩
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).work≤profile model A t.rowBits k B H o ∧
        ∀ j,RationalHeight ((GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).output.read j) (outputHeight o B H) := by
  dsimp only
  intro physical hRich hPoor hCapacity hRow reciprocal fresh
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values
  let c := if reciprocal then b else 1
  have hCapacity' : 1+binaryWordWidth (2*n+o.representatives+2)≤A := hCapacity
  have hc := scale_height b B hB reciprocal
  have hColumns : ∀ j l,RationalHeight ((((if reciprocal then physical.poor else physical.rich).read j).anchors).read l) H := by
    cases reciprocal <;> assumption
  by_cases hReplace:o.replaced=true
  · obtain ⟨hm,_⟩ := GeneralPaperNativeReductionShape.original_shape true model Wv k values hReplace
    rw [make_circle model.rat (fun w => w) Ap o _ _ _ physical hReplace hm]
    dsimp only [GeneralPaperStoredStrategySampler.run,GeneralPaperStrategyDescription.run,
      GeneralPaperSamplingControls.specification,castDescription]
    have hW := GeneralPaperCircleActualWeights.original_total_positive true model Wv k values v hv
      (GeneralPaperNativeCircleLoss.original_light_positive true model Wv k values hReplace)
    have hCost := GeneralPaperCachedBitSampling.run_work model A (B+1) H hA model.rat (fun w => w) Ap
      t.rowBits (k+6) t.rows (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k)
      o hm hR hW c hc physical reciprocal hColumns (GeneralPaperCircleActualWeights.original_sum true model Wv k values)
      (GeneralPaperLightFieldIndexEquiv.original_bijective true model Wv k values) hCapacity hRow fresh
    constructor
    · dsimp only [profile,o,t,c,hR,hRows] at hCost ⊢
      omega
    · intro j
      exact GeneralPaperCachedBitSampling.run_height model A (B+1) H model.rat (fun w => w) Ap
        t.rowBits (k+6) t.rows (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k)
        o hm hR c hc physical reciprocal hColumns (GeneralPaperCircleActualWeights.original_sum true model Wv k values)
        (GeneralPaperLightFieldIndexEquiv.original_bijective true model Wv k values) fresh j
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    obtain ⟨hm,_⟩ := GeneralPaperUnreplacedShape.original_shape true model Wv k values hFalse
    rw [make_direct model.rat (fun w => w) Ap o _ _ _ physical hFalse hm]
    dsimp only [GeneralPaperStoredStrategySampler.run,GeneralPaperStrategyDescription.run,
      GeneralPaperSamplingControls.specification,castDescription,rationalPrice,indexPrice]
    simp only [ite_true]
    have hIndex (i : ℕ) (hi : i≤n) : binaryWordWidth (i+1)≤A :=
      (binaryWordWidth_mono (by omega : i+1≤2*n+o.representatives+2)).trans (by omega)
    have hCost := GeneralPaperCachedBitSampling.direct_work model A (B+1) H t.rowBits (k+6) t.rows
      (GeneralPaperNativeSelectedSecurity.count k) hA hRows (GeneralPaperNativeSelectedSecurity.count_power k) hm c hc
      (if reciprocal then physical.poor else physical.rich) hColumns hIndex fresh
    constructor
    · dsimp only [profile,o,t,c,hRows] at hCost ⊢
      omega
    · intro j
      let i := Fin.cast hRows.symm (bitIndex t.rowBits (firstBitBlock t.rowBits (k+6) fresh))
      have hh := GeneralPaperDirectRowSampler.height model.rat (fun w => w) A hm c
        (if reciprocal then physical.poor else physical.rich) (B+1) H hc hColumns i j
      have hData := GeneralPaperDirectRowSampler.data model.rat (fun w => w) model.rat A t.rowBits (k+6) t.rows
        (GeneralPaperNativeSelectedSecurity.count k) hRows (GeneralPaperNativeSelectedSecurity.count_power k) hm c
        (if reciprocal then physical.poor else physical.rich) fresh
      have hOutput := congrArg (fun row : FixedArrayTable n ℚ => RationalHeight (row.read j) ((B+1)+H)) hData
      exact (Eq.mpr hOutput hh).mono (by unfold outputHeight;omega)


def outputBits {n : ℕ} (row : FixedArrayTable n ℚ) : ℕ := ∑ j,rationalWordWidth (row.read j)

theorem bits_of_height {n : ℕ} (row : FixedArrayTable n ℚ) (H : ℕ)
    (h : ∀ j,RationalHeight (row.read j) H) : outputBits row≤n*(1+2*H) := by
  calc
    _≤∑ _j : Fin n,(1+2*H) := Finset.sum_le_sum (fun j _ => rationalWordWidth_of_height (h j))
    _=_ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem original_output_height {n : ℕ} (model : RationalCostModel) (Wv k B H : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    outputHeight (GeneralPaperOriginalValueReduction.run true model Wv k values).1 B H≤B+H+3*k+2*binaryWordWidth n+26 := by
  have hR : binaryWordWidth (GeneralPaperOriginalValueReduction.run true model Wv k values).1.representatives≤k+5 := by
    rw [GeneralPaperNativeReductionShape.original_representatives]
    unfold GeneralPaperLightFieldReduction.representatives
    have h := binaryWordWidth_mul 8 (2^k)
    rw [show binaryWordWidth 8=4 by decide,
      show binaryWordWidth (2^k)=k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at h
    omega
  have hW := (binaryWordWidth_mono (GeneralPaperNativeCircleLoss.original_mass_bound true model Wv k values)).trans
    (GeneralPaperOriginalValueReduction.denominator_word true model Wv k values v hv)
  unfold outputHeight
  omega

def reference (n m k : ℕ) : ℕ :=
  1+binaryWordWidth (2*n+GeneralPaperLightFieldReduction.representatives k+2)+
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows+1)

theorem bit_return_bounds {n : ℕ} (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := reference n o.m k
    ∃ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).work≤
          profile model A (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rowBits k B H o ∧
        (∀ j,RationalHeight ((GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).output.read j) (outputHeight o B H)) ∧
        outputBits (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).output≤n*(1+2*outputHeight o B H) ∧
        (GeneralPaperStoredStrategySampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*sampler.controls.shifts) := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  let A := reference n o.m k
  obtain ⟨physical,hSource,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model Wv Ws k values v hv b hb
  have hDescription := GeneralPaperOriginalStrategyDriver.bit_description model Wv Ws Ap k values v hv b hb physical hSource
  let made : Description o t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
    (make model.rat (fun w => w) Ap o (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
      (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1
  let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
    ⟨o,b,GeneralPaperSamplingControls.specification _ t.rowBits k
      (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k),made⟩
  dsimp only
  refine ⟨sampler,GeneralPaperClosedStrategyDriver.close_some (fun w => w) Ap raw made hDescription,?_⟩
  intro reciprocal fresh
  have hA : 1≤A := by unfold A reference;omega
  have hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A := by
    dsimp only [o]
    rw [GeneralPaperNativeReductionShape.original_representatives]
    unfold A reference
    omega
  have hRow : binaryWordWidth (t.rows+1)≤A := by unfold A reference;dsimp only [t];omega
  have h := source_sampler_bounds model Wv k Ap A B H values v hv b hB hA physical hRich hPoor hCapacity hRow reciprocal fresh
  exact ⟨h.1,h.2,bits_of_height _ _ h.2,logarithmic_bits true model.rat A model sampler reciprocal fresh⟩

end Blotto.GeneralPaperClosedBitSampling
