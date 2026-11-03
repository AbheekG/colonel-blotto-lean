import Blotto.BinaryPRGHeapRequestLifetime
import Blotto.BinaryPRGHeapRawWorkBound
import Blotto.BinaryPRGRawRequestLifetime

/-! The complete selected request's native physical source-work charge is
bounded from the accepted original frame and reached seed tables. -/
namespace Blotto.BinaryPRGHeapRequestMeasuredRaw
open BinarySeedLookupTree

theorem uniform_request_work_bound : ∃ C d : ℕ,
    ∀ {n : ℕ} (seed : BinarySeedLookupTree.Store)
      (request : BinaryPRGRequest.Request n) (rich : Bool),
      (BinaryPRGHeapRequestLifetime.runWithTraceAndWork seed request rich).2 ≤
        C * (n + request.source.originalInputWordWidth +
          seed.width + seed.cap.value + 1)^d := by
  rcases BinaryPRGHeapResourceRequest.uniform_request_work_bound with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n seed request rich
  rw [BinaryPRGHeapRequestLifetime.runWithTraceAndWork_charge]
  exact hBound seed request rich

theorem selected_raw_resource_work_bound : ∃ C d : ℕ,
    ∀ (frame : List Bool)
      (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
      (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (rich : Bool)
        (tables : BinaryPRGSeedBlocks.Tables parsed.1.1 parsed.1.2.request.precision),
        (BinaryPRGHeapRequestLifetime.runWithTraceAndWork
          (prepare (List.ofFn tables.choice.read)) parsed.1.2.request rich).2 ≤
          C * (frame.length + 1)^d := by
  rcases BinaryPRGHeapRawWorkBound.read_resource_work_bound with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro frame parsed hSelected rich tables
  have hAccuracy := BinaryPRGRawRequestLifetime.readWithTrace_state frame
  rw [hSelected] at hAccuracy
  have hOld : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed := hAccuracy.symm
  rw [BinaryPRGHeapRequestLifetime.runWithTraceAndWork_charge]
  exact hBound frame parsed hOld rich tables

end Blotto.BinaryPRGHeapRequestMeasuredRaw
