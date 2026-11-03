import Blotto.BinaryPRGFullRawLaw
import Blotto.FreshBitSeedLifetime

/-! The raw request is parsed once. Only an accepted request with empty tail
draws its scheduled fresh bits; the actual generated list feeds seed validation
and physical output directly. Every created seed cell is owned by this trace,
not counted again as borrowed input. The entropy primitive has a named unit
interface; its private state is external. This is still a retained source-cell/
activation contract, not a native bit-machine or compiler certificate. -/
namespace Blotto.BinaryPRGFreshRawLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open FreshBitSeedLifetime
set_option maxHeartbeats 3000000

def runWithTrace {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (Option (List Bool) × S) × Trace :=
  let decoded := BinaryPRGRawRequestLifetime.readWithTrace frame
  match decoded.1 with
  | none => ((none,state),wrap 24 2 [decoded.2])
  | some parsed =>
      if parsed.2 = [] then
        let seed := generateWithTrace fresh (sampleBitBudget parsed.1.1 parsed.1.2.request.precision) state
        let output := BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1
        ((output.1,seed.1.2),wrap 48 2 [decoded.2,seed.2,output.2])
      else ((none,state),wrap 32 2 [decoded.2])

-- Semantic observer only; the executable runner does not call/reparse this.
def drawCount (frame : List Bool) : ℕ :=
  match (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none => 0
  | some parsed => if parsed.2 = [] then sampleBitBudget parsed.1.1 parsed.1.2.request.precision else 0

theorem drawCount_bound (frame : List Bool) : drawCount frame ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length := by
  unfold drawCount
  split
  · exact Nat.zero_le _
  · rename_i parsed hRead
    split
    · exact BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
        ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)
    · exact Nat.zero_le _

theorem runWithTrace_counted {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) (calls : ℕ) :
    (runWithTrace (countedFresh fresh) rich frame (state,calls)).1 =
      ((runWithTrace fresh rich frame state).1.1,((runWithTrace fresh rich frame state).1.2,calls+drawCount frame)) := by
  unfold runWithTrace drawCount
  dsimp only
  split
  · simp only [Nat.add_zero]
  · split
    · rw [generate_counted]
    · simp only [Nat.add_zero]

theorem reject_none {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (h : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = none) :
    (runWithTrace fresh rich frame state).1 = (none,state) := by simp only [runWithTrace,h]

theorem reject_tail {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (h : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) (hTail : parsed.2 ≠ []) :
    (runWithTrace fresh rich frame state).1 = (none,state) := by simp only [runWithTrace,h,ite_eq_right hTail]

theorem runWithTrace_tape (rich : Bool) (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (tape : ℕ → Bool) (position : ℕ) :
    (runWithTrace (tapeFresh tape) rich frame position).1 =
      (some (prepared.2.request.output rich (fun i => tape (position+i.val))),
        position+sampleBitBudget prepared.1 prepared.2.request.precision) := by
  simp only [runWithTrace,hRead,ite_true,generate_tape,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem runWithTrace_vector (rich : Bool) (frame : List Bool) (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool) :
    (runWithTrace (tapeFresh (vectorTape bits)) rich frame 0).1 =
      (some (prepared.2.request.output rich bits),sampleBitBudget prepared.1 prepared.2.request.precision) := by
  rw [runWithTrace_tape rich frame prepared hRead]
  simp only [Nat.zero_add,vectorTape,dite_eq_left (Fin.isLt _),Fin.eta]

theorem accepted_returns {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[])) (state : S) :
    ∃ bits : Fin (sampleBitBudget prepared.1 prepared.2.request.precision) → Bool,
      (runWithTrace fresh rich frame state).1.1 = some (prepared.2.request.output rich bits) := by
  obtain ⟨bits,hBits⟩ := generate_ofFn fresh (sampleBitBudget prepared.1 prepared.2.request.precision) state
  refine ⟨bits,?_⟩
  simp only [runWithTrace,hRead,ite_true,hBits,BinaryPRGSeedOutputLaw.runWithTrace_ofFn]

theorem runWithTrace_returned_budget {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S)
    (bytes : List Bool) (h : (runWithTrace fresh rich frame state).1.1 = some bytes) :
    ∃ parsed : Σ n,BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords frame =
        some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) bytes := by
  unfold runWithTrace at h
  dsimp only at h
  split at h
  · cases h
  · rename_i parsed hRead
    split at h
    · rename_i hTail
      have hOld : (BinaryPRGFullRawLifetime.runWithTrace rich frame
          (generateWithTrace fresh (sampleBitBudget parsed.1.1 parsed.1.2.request.precision) state).1.1).1 = some bytes := by
        simpa only [BinaryPRGFullRawLifetime.runWithTrace,hRead,ite_eq_left hTail] using h
      exact BinaryPRGFullRawLifetime.runWithTrace_returned_budget _ _ _ _ hOld
    · cases h

theorem insert_usage (a seed b : Trace) :
    usage (wrap 48 2 [a,seed,b]) ≤ usage (wrap 32 2 [a,b])+usage seed+32 := by
  have hSeed := framePeak_under 2 seed
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells_append,arraySlots_append,
    listCells_under,arraySlots_under,framePeak_append,listCells,arraySlots,framePeak] at *
  omega

theorem reject_usage (slots : ℕ) (a : Trace) : usage (wrap (slots+8) 2 [a]) ≤ usage (wrap slots 2 [a])+8 := by
  simp only [usage,BinaryPRGHeapPrimitiveLifetime.cells,wrap,combine,listCells_append,arraySlots_append,
    listCells_under,arraySlots_under,framePeak_append,listCells,arraySlots,framePeak]
  omega

theorem usage_comparison {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    ∃ seed : List Bool,usage (runWithTrace fresh rich frame state).2 ≤
      usage (BinaryPRGFullRawLifetime.runWithTrace rich frame seed).2+
        24*BinaryPRGSeedRequestBound.seedCountBound frame.length+64 := by
  cases hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      refine ⟨[],?_⟩
      have h := reject_usage 16 (BinaryPRGRawRequestLifetime.readWithTrace frame).2
      norm_num only at h
      simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead]
      omega
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · let seed := generateWithTrace fresh (sampleBitBudget parsed.1.1 parsed.1.2.request.precision) state
        refine ⟨seed.1.1,?_⟩
        have hn := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed
          ((BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead)
        have hg := generate_usage fresh (sampleBitBudget parsed.1.1 parsed.1.2.request.precision) state
        have hi := insert_usage (BinaryPRGRawRequestLifetime.readWithTrace frame).2 seed.2
          (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2
        change usage seed.2 ≤ _ at hg
        simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead,ite_eq_left hTail]
        change usage (wrap 48 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,seed.2,
          (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2]) ≤
          usage (wrap 32 2 [(BinaryPRGRawRequestLifetime.readWithTrace frame).2,
            (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed.1.1).2])+
              24*BinaryPRGSeedRequestBound.seedCountBound frame.length+64
        omega
      · refine ⟨[],?_⟩
        have h := reject_usage 24 (BinaryPRGRawRequestLifetime.readWithTrace frame).2
        norm_num only at h
        simp only [runWithTrace,BinaryPRGFullRawLifetime.runWithTrace,hRead,ite_eq_right hTail]
        omega

theorem uniform_usage : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    usage (runWithTrace fresh rich frame state).2 ≤ C*(frame.length+1)^d := by
  rcases BinaryPRGFullRawLifetime.uniform_usage with ⟨C,d,hBound⟩
  refine ⟨C+24*3033+64,d+1,?_⟩
  intro S fresh rich frame state
  obtain ⟨seed,hCompare⟩ := usage_comparison fresh rich frame state
  have hOld := hBound rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hUp := Nat.pow_le_pow_right hX (show d ≤ d+1 by omega)
  have hLinear : frame.length+1 ≤ (frame.length+1)^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d+1 by omega)
  have hOne := Nat.one_le_pow (d+1) (frame.length+1) hX
  have hScale := Nat.mul_le_mul_left C hUp
  unfold BinaryPRGSeedRequestBound.seedCountBound at hCompare
  nlinarith

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {S : Type*} (fresh : S → Bool × S) (rich : Bool) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    retainedHeap (borrowed+frame.length) (runWithTrace fresh rich frame state).2 steps ≤
      borrowed+frame.length+C*(frame.length+1)^d ∧
    framePeak ((runWithTrace fresh rich frame state).2.take steps) ≤ C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun fresh rich frame state borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound fresh rich frame state) _ steps⟩

end Blotto.BinaryPRGFreshRawLifetime
