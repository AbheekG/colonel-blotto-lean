import Blotto.BinaryTerminalPhysicalEmissionSeed
import Blotto.BinaryTerminalPhysicalOutputGenerated
import Blotto.BooleanFreshSeedAmortized

/-! Complete generated and consecutive-player callers consume measured seed
preparation, terminal emission/fallback and physical output. Original bytes,
allowances, fresh-call counts, whole laws and every-path budgets are preserved.
The enlarged source trace has original-frame polynomial every-prefix bounds.
Group factory/draw, row projection, complete parser and native model prices
remain separate; the charge is not a complete terminal runtime contract. -/

namespace Blotto.BinaryTerminalPhysicalEmissionGenerated
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
open BinaryTerminalPhysicalGeneratedWork (generationCoefficient generator_bound)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def run {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((Option (List Bool) × S) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => ((((none,state),[]),wrap 24 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
        let output := BinaryTerminalPhysicalEmissionSeed.run
          frame parsed hParsed rich generated.1.1.1
        ((((output.1.1.1,generated.1.1.2),output.1.1.2),
          wrap 48 2 [decoded.2,generated.1.2,output.1.2]),output.2+generated.2+8)
      else ((((none,state),[]),wrap 32 2 [decoded.2]),0)

theorem run_reference_data {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (run next rich frame state).1.1 = (BinaryTerminalPhysicalOutputGenerated.run next rich frame state).1.1 := by
  unfold run BinaryTerminalPhysicalOutputGenerated.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i parsed hSome
      cases hNone.symm.trans hSome
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,BinaryTerminalPhysicalEmissionSeed.run_data]
      · simp only [ite_eq_right hTail]

theorem run_data {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (run next rich frame state).1.1 =
      (BinaryTerminalPhysicalPreparedRaw.fresh next rich frame state).1.1 := by
  rw [run_reference_data,BinaryTerminalPhysicalOutputGenerated.run_data]

theorem reject_none {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    run next rich frame state =
      ((((none,state),[]),wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]),0) := by
  unfold run
  dsimp only
  split
  · rfl
  · rename_i parsed hSome
    rw [hRead] at hSome
    cases hSome

theorem reject_tail {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    run next rich frame state =
      ((((none,state),[]),wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]),0) := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_right hTail]

theorem accepted_charge {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
    let output := BinaryTerminalPhysicalEmissionSeed.run
      frame parsed hRead rich generated.1.1.1
    (run next rich frame state).2+BinaryBigEndian.littleValue (run next rich frame state).1.1.2 =
      output.2+BinaryBigEndian.littleValue output.1.1.2+generated.2+8 := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail]
    omega

theorem run_counted {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (run (FreshBitSeedLifetime.countedFresh next) rich frame (state,calls)).1.1.1 =
      ((run next rich frame state).1.1.1.1,((run next rich frame state).1.1.1.2,
        calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [run_data,BinaryTerminalPhysicalPreparedRaw.fresh_counted]

theorem uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    (run next rich frame state).2+
      BinaryBigEndian.littleValue
        (run next rich frame state).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := BinaryTerminalPhysicalEmissionSeed.accepted_uniform_work
  let D := max d 1
  refine ⟨C+400008,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp only [D]; omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp only [D]; omega)
  have hScaled := Nat.mul_le_mul_left 400000 hLinear
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  unfold run
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
      let output := BinaryTerminalPhysicalEmissionSeed.run
        frame parsed hParsed rich generated.1.1.1
      have ho := hOutput frame parsed hParsed rich generated.1.1.1
      have hg := BooleanFreshSeedAmortized.physical_generation_linear next frame parsed hParsed state
      change output.2+generated.2+8+BinaryBigEndian.littleValue output.1.1.2 ≤ _
      change output.2+BinaryBigEndian.littleValue output.1.1.2 ≤ _ at ho
      change generated.2 ≤ _ at hg
      nlinarith only [ho,hg,hd,hScaled,hOne]
    · exact Nat.zero_le _

theorem uniform_usage : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    usage (run next rich frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hOutput⟩ := BinaryTerminalPhysicalEmissionSeed.accepted_uniform_usage
  obtain ⟨C₂,d₂,hParser⟩ := BinaryTerminalPhysicalRawPolynomial.uniform_envelope
  let D := max (max d₁ d₂) 2
  refine ⟨C₁+C₂+generationCoefficient+128,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hRead := (BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame).trans
    (hParser frame.length)
  have h1 := Nat.mul_le_mul_left C₁ (Nat.pow_le_pow_right hX (show d₁ ≤ D by dsimp only [D]; omega))
  have h2 := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_right hX (show d₂ ≤ D by dsimp only [D]; omega))
  have hgUp := Nat.mul_le_mul_left generationCoefficient
    (Nat.pow_le_pow_right hX (show 2 ≤ D by dsimp only [D]; omega))
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  unfold run
  dsimp only
  split
  · have hw := wrap_usage 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    nlinarith only [hw,hRead,h2,hOne]
  · rename_i parsed hParsed
    split
    · let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
      let output := BinaryTerminalPhysicalEmissionSeed.run
        frame parsed hParsed rich generated.1.1.1
      have ho := hOutput frame parsed hParsed rich generated.1.1.1
      have hg := (generator_bound next frame parsed hParsed state).2
      have hw := wrap_usage 48 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,generated.1.2,output.1.2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage output.1.2 ≤ _ at ho
      change usage generated.1.2 ≤ _ at hg
      change usage (wrap 48 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,generated.1.2,output.1.2]) ≤ _
      nlinarith only [hw,hRead,ho,hg,h1,h2,hgUp,hOne]
    · have hw := wrap_usage 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      nlinarith only [hw,hRead,h2,hOne]

theorem all_prefixes : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (run next rich frame state).1.2 steps ≤
        borrowed+frame.length+B ∧
      framePeak ((run next rich frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  exact ⟨C,d,fun next rich frame state borrowed steps =>
    all_prefix _ _ (hBound next rich frame state) (borrowed+frame.length) steps⟩

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ :=
  let rich := run next true frame state
  let poor := run next false frame rich.1.1.1.2
  let data := ((rich.1.1.1.1,poor.1.1.1.1),poor.1.1.1.2)
  (((data,(rich.1.1.2,poor.1.1.2)),wrap 64 2 [rich.1.2,poor.1.2]),rich.2+poor.2)

theorem pair_data {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1.1 =
      (BinaryTerminalPhysicalPreparedRaw.pair next frame state).1.1 := by
  simp only [pair,BinaryTerminalPhysicalPreparedRaw.pair,run_data]

theorem pair_counted {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (pair (FreshBitSeedLifetime.countedFresh next) frame (state,calls)).1.1.1 =
      ((pair next frame state).1.1.1.1,((pair next frame state).1.1.1.2,
        calls+2*BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [pair_data,BinaryTerminalPhysicalPreparedRaw.pair_erases,
    BinaryTerminalPhysicalAllowanceFresh.pair_counted]

theorem pair_uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S),
    (pair next frame state).2+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.1+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_work
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (run next true frame state).1.1.1.2
  unfold pair
  dsimp only
  nlinarith only [hr,hp]

theorem pair_uniform_usage : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S), usage (pair next frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_usage
  refine ⟨2*C+128,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (run next true frame state).1.1.1.2
  have hw := wrap_usage 64 2 [(run next true frame state).1.2,
    (run next false frame (run next true frame state).1.1.1.2).1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  change usage (wrap 64 2 [_,_]) ≤ _
  nlinarith only [hr,hp,hw,hOne]

theorem pair_all_prefixes : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (pair next frame state).1.2 steps ≤
        borrowed+frame.length+B ∧
      framePeak ((pair next frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := pair_uniform_usage
  exact ⟨C,d,fun next frame state borrowed steps =>
    all_prefix _ _ (hBound next frame state) (borrowed+frame.length) steps⟩

theorem kernel_operational (rich : Bool) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.kernel rich frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (run (FreshBitSeedLifetime.tapeFresh
          (FreshBitSeedLifetime.vectorTape bits)) rich frame 0).1.1.1.1) := by
  simpa only [run_data] using
    BinaryTerminalPhysicalPreparedRaw.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel (sampleBitBudget prepared.1 prepared.2.request.precision+
        sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (pair (FreshBitSeedLifetime.tapeFresh
          (FreshBitSeedLifetime.vectorTape bits)) frame 0).1.1.1.1) := by
  simpa only [pair_data] using
    BinaryTerminalPhysicalPreparedRaw.pairKernel_operational frame prepared hRead f

theorem every_path_fullBudget {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (rich : Bool) (state : S) :
    FullBudget (if rich then (prepared.2.request.source.a : ℝ)
      else (prepared.2.request.source.b : ℝ))
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((run next rich frame state).1.1.1.1.getD []) j : ℝ)) := by
  rw [run_data,BinaryTerminalPhysicalPreparedRaw.fresh_erases]
  exact BinaryTerminalPhysicalAllowanceLaw.every_path_fullBudget next frame prepared hRead rich state

theorem pair_every_path_fullBudget {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (state : S) :
    FullBudget (prepared.2.request.source.a : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((pair next frame state).1.1.1.1.1.getD []) j : ℝ)) ∧
    FullBudget (prepared.2.request.source.b : ℝ)
      (fun j => (BinaryPRGSeedOutputLaw.readback prepared.1
        ((pair next frame state).1.1.1.1.2.getD []) j : ℝ)) := by
  rw [pair_data,BinaryTerminalPhysicalPreparedRaw.pair_erases]
  exact BinaryTerminalPhysicalAllowanceLaw.pair_every_path_fullBudget next frame prepared hRead state

end Blotto.BinaryTerminalPhysicalEmissionGenerated
