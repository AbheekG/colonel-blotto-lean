import Blotto.BinaryNativeEmissionTransport
import Blotto.BinaryCacheTraceSparsity
import Blotto.BinaryTerminalPhysicalAllowanceCache
import Blotto.FareySourceUniverses

/-! Actual request/cache records carry all previously returned charges plus
their own wrapper emission. Accepted-frame and uniform source-ledger bounds
preserve every earlier field; they are not full native machine-cost joins. -/
namespace Blotto.BinaryRequestCacheCharges
open BinarySeedPreparationSpace BinaryExecutionCharges
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {n : ℕ}

theorem run_trace_length (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    (BinaryPhysicalHeapAllowanceRequest.run seed request rich).1.2.length ≤
      26*(BinaryPhysicalHeapAllowanceRequest.run seed request rich).2+
        (BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+7 := by
  let pc := BinaryWordIndexCoinController.zeroIndex seed
  have hp : pc.value ≤ seed.cap.value := by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega
  have ht := BinaryPhysicalHeapAllowanceRequest.native_trace_length seed request rich pc hp
  have hs := BinaryResourceTraceLength.source_length seed request rich pc hp
  have hsw := BinaryPhysicalHeapAllowanceRequest.nativeAt_source_work_le seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceRequest.native_work_le_run seed request rich
  have he : (BinaryPhysicalHeapAllowanceRequest.run seed request rich).1.2.length =
      (BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).1.2.length+5 := by
    rw [BinaryPhysicalHeapAllowanceRequest.run_eq_reference]
    dsimp only [pc]
    simp only [BinaryPhysicalHeapAllowanceRequest.runReference,BinaryPRGHeapTraceUsage.wrapList,
      BinaryPRGHeapTraceUsage.wrap,BinaryPRGHeapTraceUsage.combine,List.length_append,
      BinaryResourceTraceLength.under_length,List.length_cons,List.length_nil]
    omega
  dsimp only [pc] at ht hs hsw he
  omega

theorem run_total (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    let produced := BinaryPhysicalHeapAllowanceRequest.runWithCharges seed request rich
    produced.1.2+total produced.2 ≤
      358*produced.1.2+15*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+80 := by
  let pc := BinaryWordIndexCoinController.zeroIndex seed
  have hp : pc.value ≤ seed.cap.value := by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega
  let child := BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed request rich pc hp
  have hn := BinaryNativeEmissionTransport.native_record_total seed request rich pc hp
  have he := BinaryPhysicalHeapAllowanceRequest.runWithCharges_wrapper_emission seed request rich
  have ht := BinaryPhysicalHeapAllowanceRequest.native_trace_length seed request rich pc hp
  have hs := BinaryResourceTraceLength.source_length seed request rich pc hp
  have hsw := BinaryPhysicalHeapAllowanceRequest.nativeAt_source_work_le seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceRequest.native_work_le_run seed request rich
  have hf := BinaryPhysicalHeapAllowanceRequest.runWithCharges_fields seed request rich
  dsimp only [child,pc] at hf
  rcases hf with ⟨hf1,hf2,hf3,hf4⟩
  have hCharges : total (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed request rich).2 =
      child.1.1.2.1+child.1.1.2.2+child.1.2+child.2+
        (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed request rich).2.wrappers := by
    simp only [total,hf1,hf2,hf3,hf4]
    rfl
  change (BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
    child.1.1.2.1+child.1.1.2.2+child.1.2+child.2 ≤
      228*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
        10*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+30 at hn
  dsimp only
  change (BinaryPhysicalHeapAllowanceRequest.run seed request rich).2+
    total (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed request rich).2 ≤
      358*(BinaryPhysicalHeapAllowanceRequest.run seed request rich).2+
        15*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+80
  dsimp only [child,pc] at hn ht hs hsw hCharges
  omega

theorem accepted_run_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.1.2 rich
        produced.1.2+total produced.2 ≤ 358*produced.1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨4*C,d,?_⟩
  intro frame parsed hParsed seed rich
  have h := run_total seed parsed.1.2 rich
  have ho := hOverhead frame parsed hParsed rich
  dsimp only at h ⊢
  simp only [Nat.mul_assoc]
  omega

theorem reached_cache_length (frame : List Bool) (parsed : (Σ n,Request n) × List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (state : BinaryResourcePair.Certified
      (BinaryPRGResourceWork.resourceInput parsed.1.2.logical.request rich).length)
    (hState : (BinaryPhysicalHeapAllowanceRequest.run seed parsed.1.2 rich).1.1.1.1 = some state) :
    (BinaryTerminalPhysicalRouteLifetime.cacheWithTraceAndWork
      (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
      parsed.1.2.physical.lengthStore).1.2.length ≤ (2^62+1)*(frame.length+3)^8 := by
  have hd := congrArg Prod.fst (BinaryPhysicalHeapAllowanceRequest.run_data seed parsed.1.2 rich)
  have he := congrArg (fun output => output.1.1)
    (BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_erases seed parsed.1.2 rich)
  have hl := congrArg Prod.fst (BinaryPhysicalHeapRequestLifetime.run_erasure seed parsed.1.2 rich)
  have hLogical : (BinaryPRGHeapRequestLifetime.run seed parsed.1.2.logical.request rich).1.1 = some state := by
    exact hl.symm.trans (he.symm.trans (hd.symm.trans hState))
  exact BinaryCacheTraceSparsity.accepted_reached_cache_length frame parsed hParsed rich seed state hLogical

theorem cache_total (parsed : Σ n,Request n) (seed : BinarySeedLookupTree.Store) (rich : Bool)
    (B : ℕ) (hCache : ∀ state,
      (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).1.1.1.1 = some state →
      (BinaryTerminalPhysicalRouteLifetime.cacheWithTraceAndWork
        (BinaryPRGTerminalWork.terminalInput parsed.2.logical.request rich state)
        parsed.2.physical.lengthStore).1.2.length ≤ B) :
    let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich
    produced.1.2+total produced.2 ≤
      488*produced.1.2+20*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.2 rich).1.2.length+
        16*parsed.1+150+5*B := by
  have hr := run_total seed parsed.2 rich
  have ht := run_trace_length seed parsed.2 rich
  have hc := BinaryTerminalPhysicalAllowanceCache.runWithCharges_total_bound parsed seed rich B hCache
  have hw := BinaryTerminalPhysicalAllowanceCache.request_work_le_run parsed seed rich
  dsimp only at hr ⊢
  change (BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).2+
    total (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.2 rich).2 ≤
      358*(BinaryPhysicalHeapAllowanceRequest.run seed parsed.2 rich).2+
        15*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.2 rich).1.2.length+16*parsed.1+80 at hr
  change (BinaryTerminalPhysicalAllowanceCache.run parsed seed rich).2+
    total (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed seed rich).2 ≤
      488*(BinaryTerminalPhysicalAllowanceCache.run parsed seed rich).2+
        20*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.2 rich).1.2.length+16*parsed.1+150+5*B
  omega

theorem accepted_cache_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
        produced.1.2+total produced.2 ≤ 488*produced.1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨8*C+5*(2^62+1),max d 8,?_⟩
  intro frame parsed hParsed seed rich
  have h := cache_total parsed.1 seed rich ((2^62+1)*(frame.length+3)^8)
    (fun state hState => reached_cache_length frame parsed hParsed seed rich state hState)
  have ho := hOverhead frame parsed hParsed rich
  have hi : 20*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest parsed.1.2 rich).1.2.length+
      16*parsed.1.1+150 ≤ (8*C)*(frame.length+3)^d := by
    simp only [Nat.mul_assoc]
    omega
  have hd := Nat.mul_le_mul_left (8*C)
    (Nat.pow_le_pow_right (by omega : 0 < frame.length+3) (Nat.le_max_left d 8))
  have he := Nat.mul_le_mul_left (5*(2^62+1))
    (Nat.pow_le_pow_right (by omega : 0 < frame.length+3) (Nat.le_max_right d 8))
  dsimp only at h ⊢
  nlinarith only [h,hi,hd,he]

theorem uniform_envelope (L A B W cost K C P d e : ℕ)
    (hWork : W ≤ C*(L+A+B+3)^d) (hCost : cost ≤ K*W+P*(L+3)^e) :
    cost ≤ (K*C+P)*(L+A+B+3)^(max d e) := by
  have hQ : 0 < L+A+B+3 := by omega
  have hd := Nat.pow_le_pow_right hQ (Nat.le_max_left d e)
  have he := (Nat.pow_le_pow_left (by omega : L+3 ≤ L+A+B+3) e).trans
    (Nat.pow_le_pow_right hQ (Nat.le_max_right d e))
  have hw := Nat.mul_le_mul_left K hWork
  have hwd := Nat.mul_le_mul_left (K*C) hd
  have hpe := Nat.mul_le_mul_left P he
  nlinarith only [hCost,hw,hwd,hpe]

theorem accepted_run_uniform : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.1.2 rich
        produced.1.2+total produced.2 ≤ C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalAllowanceCache.accepted_uniform_work
  obtain ⟨P,e,hNew⟩ := accepted_run_total
  refine ⟨358*C+P,max d e,?_⟩
  intro frame parsed hParsed seed rich
  have ho := hOld frame parsed hParsed seed rich
  have hw := BinaryTerminalPhysicalAllowanceCache.request_work_le_run parsed.1 seed rich
  have hWork : (BinaryPhysicalHeapAllowanceRequest.runWithCharges seed parsed.1.2 rich).1.2 ≤
      C*(frame.length+seed.width+seed.cap.value+3)^d := by
    change (BinaryPhysicalHeapAllowanceRequest.run seed parsed.1.2 rich).2 ≤ _
    omega
  exact uniform_envelope frame.length seed.width seed.cap.value _ _ 358 C P d e
    hWork (hNew frame parsed hParsed seed rich)

theorem accepted_cache_uniform : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
        produced.1.2+total produced.2 ≤ C*(frame.length+seed.width+seed.cap.value+3)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalAllowanceCache.accepted_uniform_work
  obtain ⟨P,e,hNew⟩ := accepted_cache_total
  refine ⟨488*C+P,max d e,?_⟩
  intro frame parsed hParsed seed rich
  have ho := hOld frame parsed hParsed seed rich
  have hWork : (BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich).1.2 ≤
      C*(frame.length+seed.width+seed.cap.value+3)^d := by
    change (BinaryTerminalPhysicalAllowanceCache.run parsed.1 seed rich).2 ≤ _
    omega
  exact uniform_envelope frame.length seed.width seed.cap.value _ _ 488 C P d e
    hWork (hNew frame parsed hParsed seed rich)

theorem accepted_cache_charge_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
        binaryWordWidth (produced.1.2+total produced.2) ≤
          binaryWordWidth (C*(frame.length+seed.width+seed.cap.value+3)^d) := by
  obtain ⟨C,d,hBound⟩ := accepted_cache_uniform
  exact ⟨C,d,fun frame parsed hParsed seed rich =>
    binaryWordWidth_mono (hBound frame parsed hParsed seed rich)⟩

theorem accepted_cache_scalar_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool),
        let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
        ∀ counter ∈ [produced.1.2,produced.2.primitive,produced.2.coinSource,
          produced.2.write,produced.2.native,produced.2.wrappers],
          binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth
            (frame.length+seed.width+seed.cap.value+3) := by
  obtain ⟨C,d,hBound⟩ := accepted_cache_uniform
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich
  let produced := BinaryTerminalPhysicalAllowanceCache.runWithCharges parsed.1 seed rich
  have hb := hBound frame parsed hParsed seed rich
  have hf := fields_le_total produced.2
  dsimp only [produced] at hf
  have hm := binaryWordWidth_mul C ((frame.length+seed.width+seed.cap.value+3)^d)
  have hp := Farey.binaryWordWidth_power (frame.length+seed.width+seed.cap.value+3) d
  have hWidth := binaryWordWidth_mono hb
  dsimp only
  intro counter hCounter
  have hc : counter ≤ produced.1.2+total produced.2 := by
    dsimp only [produced]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  dsimp only [produced] at hw
  omega

end Blotto.BinaryRequestCacheCharges
