import Blotto.BinaryTerminalPhysicalPreparationWork
import Blotto.BinaryTerminalPhysicalAllowanceLaw

/-! Complete raw/fresh/pair callers consume measured seed preparation once.
Their natural work fields cover validation, physical choice-store preparation
and the prior cache prefix. Seed generation, terminal runtime and native
observer evaluation remain separate prices. -/

namespace Blotto.BinaryTerminalPhysicalPreparedRaw
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage RationalLottoResourceSystem
open BinaryTerminalPhysicalAllowanceCache (PhysicalRequest Parsed)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def raw (rich : Bool) (frame seed : List Bool) :
    ((Option (List Bool) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => (((none,[]),wrap 16 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let output := BinaryTerminalPhysicalPreparationWork.run frame parsed hParsed rich seed
        ((output.1.1,wrap 32 2 [decoded.2,output.1.2]),output.2)
      else (((none,[]),wrap 24 2 [decoded.2]),0)

theorem raw_erases (rich : Bool) (frame seed : List Bool) :
    (raw rich frame seed).1 = (BinaryTerminalPhysicalAllowanceRaw.run rich frame seed).1 := by
  unfold raw BinaryTerminalPhysicalAllowanceRaw.run
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
      · simp only [ite_eq_left hTail,BinaryTerminalPhysicalPreparationWork.run_erases]
      · simp only [ite_eq_right hTail]

theorem raw_accepted_charge (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (raw rich frame seed).2+BinaryBigEndian.littleValue (raw rich frame seed).1.1.2 =
      BinaryTerminalPhysicalAllowanceRaw.carriedCharge rich frame seed+
        (BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed).2 := by
  unfold raw
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail,BinaryTerminalPhysicalAllowanceRaw.carriedCharge,
      hRead,Option.map_some,Option.getD_some,BinaryTerminalPhysicalAllowanceRaw.seedCharge]
    exact BinaryTerminalPhysicalPreparationWork.run_prefix_preparation_charge
      frame parsed hRead rich seed

theorem raw_uniform_work : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    (raw rich frame seed).2+BinaryBigEndian.littleValue (raw rich frame seed).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalPreparationWork.accepted_uniform_work
  refine ⟨C,d,?_⟩
  intro rich frame seed
  unfold raw
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · exact hBound frame parsed hParsed rich seed
    · exact Nat.zero_le _

theorem raw_uniform_usage : ∃ C d : ℕ, ∀ (rich : Bool) (frame seed : List Bool),
    usage (raw rich frame seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceRaw.uniform_usage
  refine ⟨C,d,?_⟩
  intro rich frame seed
  rw [raw_erases]
  exact hBound rich frame seed

theorem raw_all_prefix : ∃ C d : ℕ,
    ∀ (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ),
      let B := C*(frame.length+1)^d
      retainedHeap (borrowed+frame.length+seed.length) (raw rich frame seed).1.2 steps ≤
          borrowed+frame.length+seed.length+B ∧
        framePeak ((raw rich frame seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hUsage⟩ := raw_uniform_usage
  exact ⟨C,d,fun rich frame seed borrowed steps =>
    all_prefix _ _ (hUsage rich frame seed) (borrowed+frame.length+seed.length) steps⟩

def fresh {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) : (((Option (List Bool) × S) × List Bool) × Trace) × ℕ :=
  let decoded := BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame
  match hParsed : decoded.1 with
  | none => ((((none,state),[]),wrap 24 2 [decoded.2]),0)
  | some parsed =>
      if parsed.2 = [] then
        let generated := BinaryPRGSeedCountLifetime.generateWithTrace next
          parsed.1.2.logical.request state
        let output := BinaryTerminalPhysicalPreparationWork.run
          frame parsed hParsed rich generated.1.1
        ((((output.1.1.1,generated.1.2),output.1.1.2),
          wrap 48 2 [decoded.2,generated.2,output.1.2]),output.2)
      else ((((none,state),[]),wrap 32 2 [decoded.2]),0)

theorem fresh_erases {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (fresh next rich frame state).1 =
      (BinaryTerminalPhysicalAllowanceFresh.run next rich frame state).1 := by
  unfold fresh BinaryTerminalPhysicalAllowanceFresh.run
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
      · simp only [ite_eq_left hTail,BinaryTerminalPhysicalPreparationWork.run_erases]
      · simp only [ite_eq_right hTail]

theorem fresh_accepted_charge {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    (fresh next rich frame state).2+
      BinaryBigEndian.littleValue (fresh next rich frame state).1.1.2 =
      BinaryTerminalPhysicalAllowanceFresh.carriedCharge next rich frame state+
        (BinarySeedPreparationMeasured.prepare parsed.1.2.logical
          (BinaryPRGSeedCountLifetime.generateWithTrace next
            parsed.1.2.logical.request state).1.1).2 := by
  unfold fresh
  dsimp only
  split
  · rename_i hNone
    rw [hRead] at hNone
    cases hNone
  · rename_i other hOther
    have he := Option.some.inj (hOther.symm.trans hRead)
    subst other
    simp only [ite_eq_left hTail,BinaryTerminalPhysicalAllowanceFresh.carriedCharge,
      hRead,Option.map_some,Option.getD_some,BinaryTerminalPhysicalAllowanceRaw.seedCharge]
    exact BinaryTerminalPhysicalPreparationWork.run_prefix_preparation_charge
      frame parsed hRead rich _

theorem fresh_counted {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (calls : ℕ) :
    (fresh (FreshBitSeedLifetime.countedFresh next) rich frame (state,calls)).1.1.1 =
      ((fresh next rich frame state).1.1.1.1,((fresh next rich frame state).1.1.1.2,
        calls+BinaryPRGFreshRawLifetime.drawCount frame)) := by
  simp only [fresh_erases,BinaryTerminalPhysicalAllowanceFresh.run_counted]

theorem fresh_uniform_work : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (fresh next rich frame state).2+
      BinaryBigEndian.littleValue (fresh next rich frame state).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalPreparationWork.accepted_uniform_work
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  unfold fresh
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hParsed
    split
    · exact hBound frame parsed hParsed rich _
    · exact Nat.zero_le _

theorem fresh_uniform_usage : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    usage (fresh next rich frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceFresh.uniform_usage
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  rw [fresh_erases]
  exact hBound next rich frame state

theorem fresh_all_prefix : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (rich : Bool) (frame : List Bool)
    (state : S) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length) (fresh next rich frame state).1.2 steps ≤
        borrowed+frame.length+B ∧
      framePeak ((fresh next rich frame state).1.2.take steps) ≤ B := by
  obtain ⟨C,d,hBound⟩ := fresh_uniform_usage
  exact ⟨C,d,fun next rich frame state borrowed steps =>
    all_prefix _ _ (hBound next rich frame state) (borrowed+frame.length) steps⟩

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ :=
  let rich := fresh next true frame state
  let poor := fresh next false frame rich.1.1.1.2
  let data := ((rich.1.1.1.1,poor.1.1.1.1),poor.1.1.1.2)
  (((data,(rich.1.1.2,poor.1.1.2)),wrap 64 2 [rich.1.2,poor.1.2]),rich.2+poor.2)

theorem pair_erases {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = (BinaryTerminalPhysicalAllowanceFresh.pair next frame state).1 := by
  simp only [pair,BinaryTerminalPhysicalAllowanceFresh.pair,fresh_erases]

theorem pair_uniform_work : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (frame : List Bool) (state : S),
    (pair next frame state).2+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.1+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := fresh_uniform_work
  refine ⟨2*C,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (fresh next true frame state).1.1.1.2
  unfold pair
  dsimp only
  nlinarith only [hr,hp]

theorem pair_uniform_usage : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (frame : List Bool) (state : S),
    usage (pair next frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalAllowanceFresh.pair_uniform_usage
  refine ⟨C,d,?_⟩
  intro S next frame state
  rw [pair_erases]
  exact hBound next frame state

theorem pair_all_prefix : ∃ C d : ℕ, ∀ {S : Type*}
    (next : S → Bool × S) (frame : List Bool) (state : S) (borrowed steps : ℕ),
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
      (fairBitKernel
        (sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (fresh (FreshBitSeedLifetime.tapeFresh
          (FreshBitSeedLifetime.vectorTape bits)) rich frame 0).1.1.1.1) := by
  simpa only [fresh_erases] using
    BinaryTerminalPhysicalAllowanceLaw.kernel_operational rich frame prepared hRead f

theorem pairKernel_operational (frame : List Bool)
    (prepared : Σ n,BinaryPRGAccuracyRulerRequest.Request n)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some (prepared,[]))
    (f : Option (List Bool) × Option (List Bool) → ℝ) :
    (BinaryPRGFreshRawLaw.pairKernel frame).mean f =
      (fairBitKernel
        (sampleBitBudget prepared.1 prepared.2.request.precision+
          sampleBitBudget prepared.1 prepared.2.request.precision)).mean
        (fun bits => f (pair (FreshBitSeedLifetime.tapeFresh
          (FreshBitSeedLifetime.vectorTape bits)) frame 0).1.1.1.1) := by
  simpa only [pair_erases] using
    BinaryTerminalPhysicalAllowanceLaw.pairKernel_operational frame prepared hRead f

end Blotto.BinaryTerminalPhysicalPreparedRaw
