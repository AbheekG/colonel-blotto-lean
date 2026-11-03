import Blotto.BinaryTerminalPrefixLifetime
import Blotto.BinaryTerminalCacheLifetime
import Blotto.BinaryPRGHeapRequestLifetime
import Blotto.BinaryPRGRawRequestLifetime
import Blotto.BinaryPRGFrameCostJoin
import Blotto.BinaryPRGSeedRequestBound

/-! The selected terminal classification charge follows the reached resource
state from an accepted original frame. It covers its three arithmetic
comparisons per coordinate; packing and route source work are separate. -/
namespace Blotto.BinaryTerminalPrefixMeasuredRaw
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork BinaryPRGTerminalWork

theorem selected_raw_classification_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndClassificationWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        400000*(frame.length+1)^3 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalPrefixLifetime.prefixWithTraceAndWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  rw [BinaryTerminalPrefixLifetime.prefixWithTraceAndWork_charge] at hMeasured
  rw [BinaryTerminalCacheLifetime.cacheWithTraceAndClassificationWork_charge]
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  calc
    _ ≤ 6000*parsed.1.1*(parsed.1.2.request.source.originalInputWordWidth+2)^2 :=
      hMeasured
    _ ≤ 6000*L*(parsed.1.2.request.source.originalInputWordWidth+2)^2 := by
      gcongr
    _ ≤ 6000*L*(8*(L+1))^2 := by gcongr
    _ ≤ 6000*(L+1)*(8*(L+1))^2 := by gcongr; omega
    _ = 384000*(L+1)^3 := by ring
    _ ≤ 400000*(L+1)^3 := by gcongr; omega

theorem selected_raw_arithmetic_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndArithmeticWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        85000000*(frame.length+1)^4 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  rw [BinaryTerminalPrefixLifetime.prefixWithTraceAndArithmeticWork_charge] at hMeasured
  rw [BinaryTerminalCacheLifetime.cacheWithTraceAndArithmeticWork_charge]
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  calc
    _ ≤ 166000*parsed.1.1*(parsed.1.2.request.source.originalInputWordWidth+2)^3 :=
      hMeasured
    _ ≤ 166000*L*(parsed.1.2.request.source.originalInputWordWidth+2)^3 := by
      gcongr
    _ ≤ 166000*L*(8*(L+1))^3 := by gcongr
    _ ≤ 166000*(L+1)*(8*(L+1))^3 := by gcongr; omega
    _ = 84992000*(L+1)^4 := by ring
    _ ≤ 85000000*(L+1)^4 := by gcongr; omega

theorem selected_raw_pivot_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndPivotWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        135000000*(frame.length+1)^4 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalCacheLifetime.cacheWithTraceAndPivotWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  have hN : 166000*parsed.1.1+96000 ≤ 262000*(L+1) := by
    dsimp only [L]
    omega
  calc
    _ ≤ (166000*parsed.1.1+96000)*
        (parsed.1.2.request.source.originalInputWordWidth+2)^3 := hMeasured
    _ ≤ 262000*(L+1)*(8*(L+1))^3 :=
      Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 3)
    _ = 134144000*(L+1)^4 := by ring
    _ ≤ 135000000*(L+1)^4 := by gcongr; omega

theorem selected_raw_route_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndRouteWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        282000000*(frame.length+1)^4 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalCacheLifetime.cacheWithTraceAndRouteWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  have hN : 454000*parsed.1.1+96000 ≤ 550000*(L+1) := by
    dsimp only [L]
    omega
  calc
    _ ≤ (454000*parsed.1.1+96000)*
        (parsed.1.2.request.source.originalInputWordWidth+2)^3 := hMeasured
    _ ≤ 550000*(L+1)*(8*(L+1))^3 :=
      Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 3)
    _ = 281600000*(L+1)^4 := by ring
    _ ≤ 282000000*(L+1)^4 := by gcongr; omega

theorem selected_raw_patch_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndPatchWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        282000000*(frame.length+1)^4 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalCacheLifetime.cacheWithTraceAndPatchWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  have hN : 454000*parsed.1.1+96000 ≤ 550000*(L+1) := by
    dsimp only [L]
    omega
  have hBase : (454000*parsed.1.1+96000)*
      (parsed.1.2.request.source.originalInputWordWidth+2)^3 ≤
      281600000*(L+1)^4 := by
    calc
      _ ≤ 550000*(L+1)*(8*(L+1))^3 :=
        Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 3)
      _ = _ := by ring
  have hPatch : 3*parsed.1.1*(parsed.1.1+1)+1 ≤ 4*(L+1)^4 := by
    have hA : parsed.1.1 ≤ L+1 := by dsimp only [L]; omega
    have hB : parsed.1.1+1 ≤ L+1 := by dsimp only [L]; omega
    have hMul := Nat.mul_le_mul hA hB
    have hPow : (L+1)^2 ≤ (L+1)^4 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith only [hMul,hPow]
  calc
    _ ≤ (454000*parsed.1.1+96000)*
        (parsed.1.2.request.source.originalInputWordWidth+2)^3 +
        3*parsed.1.1*(parsed.1.1+1)+1 := hMeasured
    _ ≤ 281600000*(L+1)^4 + 4*(L+1)^4 := by
      nlinarith only [hBase,hPatch]
    _ ≤ 282000000*(L+1)^4 := by nlinarith

theorem selected_raw_list_work_bound
    (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : BinarySeedLookupTree.Store)
    (state : BinaryResourcePair.Certified
      (resourceInput parsed.1.2.request rich).length)
    (hState : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.request rich).1.1 =
      some state) :
    (BinaryTerminalCacheLifetime.cacheWithTraceAndListWork
      (terminalInput parsed.1.2.request rich state)).2 ≤
        282000000*(frame.length+1)^4 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hWidth := BinaryPRGFrameCostJoin.read_source_width frame parsed hOld
  have hNative : (BinaryPRGWordControllerResource.requestRun seed
      parsed.1.2.request rich).1 = some state := by
    rw [← BinaryPRGHeapRequestLifetime.run_erasure]
    exact hState
  have hResource : (resourceWork parsed.1.2.request rich seed.cap.value
      (BinaryWordIndexCoinController.reader seed)).1.1 = some state := by
    have h := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state
      seed parsed.1.2.request rich)
    exact h.symm.trans hNative
  have hMeasured := BinaryTerminalCacheLifetime.cacheWithTraceAndListWork_reached_bound
    parsed.1.2.request rich seed.cap.value (BinaryWordIndexCoinController.reader seed)
    state hResource
  let L := frame.length
  have hW : parsed.1.2.request.source.originalInputWordWidth+2 ≤ 8*(L+1) := by
    dsimp only [L]
    omega
  have hN : 454000*parsed.1.1+96000 ≤ 550000*(L+1) := by
    dsimp only [L]
    omega
  have hBase : (454000*parsed.1.1+96000)*
      (parsed.1.2.request.source.originalInputWordWidth+2)^3 ≤
      281600000*(L+1)^4 := by
    calc
      _ ≤ 550000*(L+1)*(8*(L+1))^3 :=
        Nat.mul_le_mul hN (Nat.pow_le_pow_left hW 3)
      _ = _ := by ring
  have hControl : 3*parsed.1.1*(parsed.1.1+1)+7*parsed.1.1+12 ≤
      22*(L+1)^4 := by
    have hA : parsed.1.1 ≤ L+1 := by dsimp only [L]; omega
    have hB : parsed.1.1+1 ≤ L+1 := by dsimp only [L]; omega
    have hMul := Nat.mul_le_mul hA hB
    have hOne : 1 ≤ L+1 := by omega
    have hPow : (L+1)^2 ≤ (L+1)^4 :=
      Nat.pow_le_pow_right hOne (by omega)
    have hLinear : L+1 ≤ (L+1)^4 := by
      simpa using (Nat.pow_le_pow_right hOne (show 1 ≤ 4 by omega))
    have hUnit : 1 ≤ (L+1)^4 := by nlinarith only [hLinear,hOne]
    nlinarith only [hMul,hPow,hLinear,hUnit,hA]
  calc
    _ ≤ (454000*parsed.1.1+96000)*
        (parsed.1.2.request.source.originalInputWordWidth+2)^3 +
        3*parsed.1.1*(parsed.1.1+1)+7*parsed.1.1+12 := hMeasured
    _ ≤ 281600000*(L+1)^4 + 22*(L+1)^4 := by
      nlinarith only [hBase,hControl]
    _ ≤ 282000000*(L+1)^4 := by nlinarith

end Blotto.BinaryTerminalPrefixMeasuredRaw
