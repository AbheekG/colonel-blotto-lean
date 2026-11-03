import Blotto.BinaryTerminalPhysicalCompleteGeneratedMeasured

/-! Complete measured generated single/pair source work and all-prefix storage
are polynomial in the original raw frame length. Existing measured Boolean
fresh-bit generation joins the complete validator/terminal/fallback/output
charge; parser/native-machine and observer obligations remain distinct. -/
namespace Blotto.BinaryTerminalPhysicalCompleteGeneratedBounds
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open RationalLottoResourceSystem BinaryTerminalPhysicalCompleteGeneratedMeasured
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryTerminalPhysicalGeneratedWork (generationCoefficient generator_bound)
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    (run next rich frame state).2+
      BinaryBigEndian.littleValue
        (run next rich frame state).1.1.2 ≤
      C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := BinaryTerminalPhysicalCompleteSeedBounds.accepted_uniform_work
  let D := max d 1
  refine ⟨C+400008,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp only [D]; omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp only [D]; omega)
  have hScaled := Nat.mul_le_mul_left 400000 hLinear
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · change 4+0 ≤ _; nlinarith only [hOne]
  · rename_i parsed hParsed
    split
    · let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
      let output := BinaryTerminalPhysicalCompleteSeedMeasured.run
        frame parsed hParsed rich generated.1.1.1
      have ho := hOutput frame parsed hParsed rich generated.1.1.1
      have hg := BooleanFreshSeedAmortized.physical_generation_linear next frame parsed hParsed state
      change output.2+generated.2+8+BinaryBigEndian.littleValue output.1.1.2 ≤ _
      change output.2+BinaryBigEndian.littleValue output.1.1.2 ≤ _ at ho
      change generated.2 ≤ _ at hg
      nlinarith only [ho,hg,hd,hScaled,hOne]
    · change 4+0 ≤ _; nlinarith only [hOne]

theorem uniform_usage : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (rich : Bool) (frame : List Bool) (state : S),
    usage (run next rich frame state).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C₁,d₁,hOutput⟩ := BinaryTerminalPhysicalCompleteSeedBounds.accepted_uniform_usage
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
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · have hw := wrap_usage 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    nlinarith only [hw,hRead,h2,hOne]
  · rename_i parsed hParsed
    split
    · let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
      let output := BinaryTerminalPhysicalCompleteSeedMeasured.run
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

theorem pair_uniform_work : ∃ C d : ℕ, ∀ {S : Type*} (next : S → Bool × S)
    (frame : List Bool) (state : S),
    (pair next frame state).2+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.1+
      BinaryBigEndian.littleValue (pair next frame state).1.1.2.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := uniform_work
  refine ⟨2*C+8,d,?_⟩
  intro S next frame state
  have hr := hBound next true frame state
  have hp := hBound next false frame (run next true frame state).1.1.1.2
  have hOne := Nat.one_le_pow d (frame.length+1) (by omega)
  rw [pair_eq_reference]
  unfold pairReference
  dsimp only
  nlinarith only [hr,hp,hOne]

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
  rw [pair_eq_reference]
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

end Blotto.BinaryTerminalPhysicalCompleteGeneratedBounds
