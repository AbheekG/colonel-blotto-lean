import Blotto.BinaryPRGHeapInitialLifetimeBound
import Blotto.BinaryPRGHeapResourceRequest
import Blotto.BinaryPRGRawRequestLifetime
import Blotto.BinaryPRGSeedRequestBound
import Blotto.BinaryPRGHeapResourcePolynomial

/-! The comparison charge of the heap initializer selected by the complete
sampler is bounded first by the prepared original request and then by the
accepted raw frame. The physical lookup/control and later resource-loop
charges remain separate. -/
namespace Blotto.BinaryPRGHeapInitialComparisonRequest
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork
set_option maxHeartbeats 1500000

theorem request_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialComparisonWork
      (resourceInput request rich).length (resourceInput request rich).resource ≤
      1000*n*(6+2*request.source.originalInputWordWidth)^2 := by
  let D := request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  obtain ⟨hCapacity,hResource⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega
  have hMeasured := BinaryPRGHeapInitialLifetimeBound.initialComparisonWork_bound
    (resourceInput request rich).length (resourceInput request rich).resource W
    hW hCapacity hResource
  have hD := request.source.normalized_lattice_wordWidth_original
  have hWidth : W+1 ≤ 6+2*request.source.originalInputWordWidth := by
    unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
    omega
  have hPower := Nat.pow_le_pow_left hWidth 2
  calc
    _ ≤ n*1000*(W+1)^2 := hMeasured
    _ ≤ n*1000*(6+2*request.source.originalInputWordWidth)^2 :=
      Nat.mul_le_mul_left (n*1000) hPower
    _ = 1000*n*(6+2*request.source.originalInputWordWidth)^2 := by ring

theorem full_scan_request_bound {n : ℕ}
    (request : BinaryPRGRequest.Request n) (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
      (resourceInput request rich).length (resourceInput request rich).resource ≤
      BinaryPRGHeapResourceInputBounds.preparationBound n
        (BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
          request.source.normalizedInput.latticeDenominator) := by
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    request.source.normalizedInput.latticeDenominator
  obtain ⟨hCapacity,hResource⟩ := BinaryPRGHeapResourceRequest.input_widths request rich
  have hW : 1 ≤ W := by unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound; omega
  have hScan := BinaryPRGHeapInitialLifetimeBound.initialPhysicalScanWork_bound
    (resourceInput request rich).length (resourceInput request rich).resource W
    hW hCapacity hResource
  dsimp only [W] at hScan
  unfold BinaryPRGHeapResourceInputBounds.preparationBound
  dsimp only
  exact hScan.trans (by omega)

theorem parsed_bound {n : ℕ} (frame suffix : List Bool)
    (request : BinaryPRGRequest.Request n)
    (hRead : BinaryPRGRequest.read frame = some (⟨n,request⟩,suffix))
    (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialComparisonWork
      (resourceInput request rich).length (resourceInput request rich).resource ≤
      1000*n*(6+2*((frame.length+2)*(4*frame.length+13)))^2 := by
  have hMeasured := request_bound request rich
  have hOriginal := BinaryPRGResourceWork.parsed_original_wordWidth frame suffix request hRead
  have hWidth : 6+2*request.source.originalInputWordWidth ≤
      6+2*((frame.length+2)*(4*frame.length+13)) := by omega
  exact hMeasured.trans (Nat.mul_le_mul_left (1000*n) (Nat.pow_le_pow_left hWidth 2))

theorem selected_raw_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialComparisonWork
      (resourceInput parsed.1.2.request rich).length
      (resourceInput parsed.1.2.request rich).resource ≤
      1000*parsed.1.1*(6+2*((frame.length+2)*(4*frame.length+13)))^2 := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hOriginal := BinaryPRGAccuracyRulerRequest.read_state frame
  rw [hOld] at hOriginal
  have hRead : BinaryPRGRequest.read frame =
      some (⟨parsed.1.1,parsed.1.2.request⟩,parsed.2) := by
    simpa only [Option.map_some,BinaryPRGAccuracyRulerRequest.forget] using hOriginal.symm
  exact parsed_bound frame parsed.2 parsed.1.2.request hRead rich

theorem selected_raw_dimension_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    parsed.1.1 ≤ frame.length := by
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  exact BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hAccuracy.symm

theorem selected_raw_closed_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialComparisonWork
      (resourceInput parsed.1.2.request rich).length
      (resourceInput parsed.1.2.request rich).resource ≤
      1000*frame.length*(6+2*((frame.length+2)*(4*frame.length+13)))^2 := by
  have hCharge := selected_raw_bound frame parsed hParsed rich
  have hn := selected_raw_dimension_bound frame parsed hParsed
  calc
    _ ≤ 1000*parsed.1.1*(6+2*((frame.length+2)*(4*frame.length+13)))^2 := hCharge
    _ = parsed.1.1*(1000*(6+2*((frame.length+2)*(4*frame.length+13)))^2) := by ring
    _ ≤ frame.length*(1000*(6+2*((frame.length+2)*(4*frame.length+13)))^2) :=
      Nat.mul_le_mul_right _ hn
    _ = 1000*frame.length*(6+2*((frame.length+2)*(4*frame.length+13)))^2 := by ring

theorem selected_raw_polynomial_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hParsed : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) :
    BinaryPRGHeapInitialLifetime.initialComparisonWork
      (resourceInput parsed.1.2.request rich).length
      (resourceInput parsed.1.2.request rich).resource ≤
      100000*(frame.length+3)^5 := by
  let L := frame.length
  have hClosed := selected_raw_closed_bound frame parsed hParsed rich
  have hA : (L+2)*(4*L+13) ≤ 4*(L+3)^2 := by nlinarith
  have hSix : 6 ≤ (L+3)^2 := by nlinarith
  have hBase : 6+2*((L+2)*(4*L+13)) ≤ 9*(L+3)^2 := by omega
  have hPow := Nat.pow_le_pow_left hBase 2
  have hLength : L ≤ L+3 := by omega
  calc
    _ ≤ 1000*L*(6+2*((L+2)*(4*L+13)))^2 := hClosed
    _ ≤ 1000*L*(9*(L+3)^2)^2 := Nat.mul_le_mul_left (1000*L) hPow
    _ ≤ 1000*(L+3)*(9*(L+3)^2)^2 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000 hLength)
    _ = 81000*(L+3)^5 := by ring
    _ ≤ 100000*(L+3)^5 := Nat.mul_le_mul_right _ (by omega)

theorem selected_raw_full_scan_polynomial : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
      (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ rich : Bool,
      BinaryPRGHeapInitialLifetime.initialPhysicalScanWork
        (resourceInput parsed.1.2.request rich).length
        (resourceInput parsed.1.2.request rich).resource ≤
        C*(frame.length+3)^d := by
  rcases BinaryPRGHeapResourcePolynomial.nativeBound_polynomial with ⟨C,d,hPoly⟩
  refine ⟨C*100^d,2*d,?_⟩
  intro frame parsed hParsed rich
  let n := parsed.1.1
  let request := parsed.1.2.request
  let D := request.source.normalizedInput.latticeDenominator
  let W := BinaryPRGWordControllerBooleanResourceLoopWork.widthBound D
  let L := frame.length
  let B := (L+2)*(4*L+13)
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hParsed] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  have hOriginal := BinaryPRGAccuracyRulerRequest.read_state frame
  rw [hOld] at hOriginal
  have hRead : BinaryPRGRequest.read frame = some (⟨n,request⟩,parsed.2) := by
    simpa only [n,request,Option.map_some,BinaryPRGAccuracyRulerRequest.forget] using hOriginal.symm
  have hN : n ≤ L := selected_raw_dimension_bound frame parsed hParsed
  have hInput : request.source.originalInputWordWidth ≤ B :=
    BinaryPRGResourceWork.parsed_original_wordWidth frame parsed.2 request hRead
  have hD : binaryWordWidth D ≤ 1+request.source.originalInputWordWidth :=
    request.source.normalized_lattice_wordWidth_original
  have hW : W ≤ 5+2*B := by
    unfold W BinaryPRGWordControllerBooleanResourceLoopWork.widthBound
    omega
  have hDB : binaryWordWidth D ≤ 1+B := by omega
  have hQuadratic : L+8+3*B ≤ 100*(L+3)^2 := by
    dsimp only [B]
    nlinarith
  have hSize : n+W+binaryWordWidth D+1 ≤ 100*(L+3)^2 := by omega
  have hCharge := full_scan_request_bound request rich
  have hNative : BinaryPRGHeapResourceInputBounds.preparationBound n W ≤
      BinaryPRGHeapResourceInputCost.nativeBound n W D 0 0 := by
    unfold BinaryPRGHeapResourceInputCost.nativeBound
    omega
  have hPolyHere := hPoly ⟨n,W,D,0,0⟩
  change BinaryPRGHeapResourceInputCost.nativeBound n W D 0 0 ≤
    C*(n+W+binaryWordWidth D+1)^d at hPolyHere
  have hPow := Nat.pow_le_pow_left hSize d
  calc
    _ ≤ BinaryPRGHeapResourceInputBounds.preparationBound n W := hCharge
    _ ≤ BinaryPRGHeapResourceInputCost.nativeBound n W D 0 0 := hNative
    _ ≤ C*(n+W+binaryWordWidth D+1)^d := hPolyHere
    _ ≤ C*(100*(L+3)^2)^d := Nat.mul_le_mul_left C hPow
    _ = (C*100^d)*(L+3)^(2*d) := by rw [mul_pow,pow_mul]; ring

end Blotto.BinaryPRGHeapInitialComparisonRequest
