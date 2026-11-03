import Blotto.GeneralPaperOriginalSourceDataCalibration

/-! One closed reserve for complete word/framed preparation, rejected input,
source address ranges and original/accuracy input indices. Fixed template
data determine the word before execution. No census or new pass executes. -/
namespace Blotto.GeneralPaperFullPreparationReference
open GeneralPaperSourceWordGrowth GeneralPaperReferenceCapacity GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

noncomputable def bitProfile {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperClosedStrategyConstructionStorage.profile W n (GeneralPaperOriginalStrategyConstructionStorage.rows k red)
    (GeneralPaperProxyParameters.prepare red.m k).K k red.m
    (GeneralPaperAccuracyStrategyConstructionStorage.profile model C d W E k S Qv B H red)
    (GeneralPaperAccuracyStrategyConstructionStorage.price model C d W E k S Qv B H red)

noncomputable def frameProfile {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperClosedStrategyConstructionStorage.frameProfile W E n (GeneralPaperOriginalStrategyConstructionStorage.rows k red)
    (GeneralPaperProxyParameters.prepare red.m k).K k red.m
    (GeneralPaperFramedStrategyConstructionStorage.profile model C d W E k S Qv B H red)
    (GeneralPaperFramedStrategyConstructionStorage.price model C d W E k S Qv B H red)

def rejectedProfile (W E n S B : ℕ) : ℕ :=
  GeneralPaperClosedStrategyConstructionStorage.rejectedProfile W n
    (GeneralPaperFramedStrategyConstructionStorage.rejectedProfile W E n S B)
    (GeneralPaperFramedStrategyConstructionStorage.rejectedPrice W E)

def indexSize (n E k S Qv : ℕ) : ℕ := n+E+S+k+Qv+1

noncomputable def reserve {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) : ℕ :=
  bitProfile model C d W E k S Qv B H red+frameProfile model C d W E k S Qv B H red+
    rejectedProfile W E n S B+GeneralPaperFastDriverReference.profile C d W x+indexSize n E k S Qv*W

@[fun_prop]
theorem bit_scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    Scale (fun W => bitProfile model C d W E k S Qv B H red) := by unfold bitProfile;fun_prop

@[fun_prop]
theorem frame_scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    Scale (fun W => frameProfile model C d W E k S Qv B H red) := by unfold frameProfile;fun_prop

@[fun_prop]
theorem rejected_scaling (E n S B : ℕ) : Scale (fun W => rejectedProfile W E n S B) := by unfold rejectedProfile;fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    Scale (fun W => reserve model C d W E k S Qv B H red x) := by
  have h := GeneralPaperFastDriverReference.scaling C d x
  unfold reserve
  fun_prop

noncomputable def width {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) : ℕ :=
  referenceWord (reserve model C d 1 E k S Qv B H red x)+
    (GeneralPaperFastDriverReference.width C d x+binaryWordWidth (n+1)+1+binaryWordWidth (E+1))

theorem positive {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) : 1≤width model C d E k S Qv B H red x := by
  unfold width
  omega

theorem source_floor {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    GeneralPaperFastDriverReference.width C d x≤width model C d E k S Qv B H red x := by unfold width;omega

theorem original_index_floor {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    binaryWordWidth (n+1)≤width model C d E k S Qv B H red x := by unfold width;omega

theorem accuracy_floor {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    1+binaryWordWidth (E+1)≤width model C d E k S Qv B H red x := by unfold width;omega

theorem capacity {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    let W := width model C d E k S Qv B H red x
    reserve model C d W E k S Qv B H red x<2^W :=
  padded_profile_capacity _ (scaling model C d E k S Qv B H red x) _

theorem bit_le {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    bitProfile model C d W E k S Qv B H red≤reserve model C d W E k S Qv B H red x := by unfold reserve;omega

theorem frame_le {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    frameProfile model C d W E k S Qv B H red≤reserve model C d W E k S Qv B H red x := by unfold reserve;omega

theorem rejected_le {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    rejectedProfile W E n S B≤reserve model C d W E k S Qv B H red x := by unfold reserve;omega

theorem source_le {n : ℕ} (model : RationalCostModel) (C d W E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) :
    GeneralPaperFastDriverReference.profile C d W x≤reserve model C d W E k S Qv B H red x := by unfold reserve;omega

theorem address_word {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) (address : ℕ)
    (h : address≤reserve model C d (width model C d E k S Qv B H red x) E k S Qv B H red x) :
    binaryWordWidth address≤width model C d E k S Qv B H red x :=
  binaryWordWidth_le_of_lt_pow (positive model C d E k S Qv B H red x)
    (h.trans_lt (capacity model C d E k S Qv B H red x))

theorem input_index {n : ℕ} (model : RationalCostModel) (C d E k S Qv B H : ℕ)
    (red : GeneralPaperReducedValuesDriver.Output n) (x : Input) (address : ℕ) (h : address≤ indexSize n E k S Qv) :
    binaryWordWidth address≤width model C d E k S Qv B H red x := by
  apply address_word model C d E k S Qv B H red x address
  have hm := Nat.mul_le_mul_left (indexSize n E k S Qv) (positive model C d E k S Qv B H red x)
  unfold reserve
  omega

end Blotto.GeneralPaperFullPreparationReference
