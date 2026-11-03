import Blotto.BinaryWordTerminalEmissionMeasured
import Blotto.BinaryTerminalPhysicalAllowanceFramed

/-! The actual physical certified prefix feeds measured terminal emission.
Global exhaustion consumes the measured original budget/zero fallback. Charges
include the existing prefix, emission, fallback and wrapper control; group
factory/draw work, row projection, parser and native model prices are separate.
Encoded allowances, cursor and returned row remain exactly the old selected data. -/

namespace Blotto.BinaryTerminalPhysicalEmissionFixed
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight BinaryMeasuredEmissionGrowth
set_option autoImplicit false
set_option maxHeartbeats 3500000

def draw (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ((BinaryPRGWordControllerTerminal.Result seed parsed.1.1 × List Bool) × Trace) × ℕ :=
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich
  match hs : observed.1.1.1.1 with
  | none => ((((none,observed.1.1.1.2),observed.1.1.2),wrap 16 2 [observed.1.2]),observed.2+4)
  | some result =>
      let drawn := BinaryWordTerminalEmissionMeasured.run seed result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hs))
        K outer scalar observed.1.1.1.2 (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
      (((drawn.1.1,observed.1.1.2),wrap 32 2 [observed.1.2,drawn.1.2]),observed.2+drawn.2+8)

theorem draw_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).1.1 =
      (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.1 := by
  unfold draw BinaryTerminalPhysicalAllowanceDraw.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i result hSome
      cases hNone.symm.trans hSome
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      simp only [BinaryWordTerminalEmissionMeasured.run_data]

def drawDelta (n : ℕ) : ℕ := BinaryWordTerminalEmissionMeasured.delta n+4

theorem draw_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    Growth (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.2
      (draw frame parsed hParsed seed rich K outer scalar).1.2 (drawDelta parsed.1.1) := by
  unfold draw BinaryTerminalPhysicalAllowanceDraw.run
  dsimp only
  split
  · rename_i hNone
    split
    · exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _⟩
    · rename_i result hSome
      cases hNone.symm.trans hSome
  · rename_i result hSome
    split
    · rename_i hNone
      cases hSome.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans hOther)
      subst other
      have h := wrap_pair 32 2
        (BinaryTerminalPhysicalAllowanceCertified.run frame parsed hParsed seed rich).1.2 _ _ _
        (BinaryWordTerminalEmissionMeasured.run_growth seed result.2
        (terminal_canonical parsed.1.2.logical.request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible seed parsed.1.2.logical.request rich result
          (BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hSome))
        K outer scalar _ (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich))
      exact growth_mono _ _ _ _ h (by unfold drawDelta; omega)

theorem draw_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (draw frame parsed hParsed seed rich K outer scalar).2 ≤
      (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).2+
        BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K+8 := by
  rw [BinaryTerminalPhysicalAllowanceDraw.run_carried_work]
  unfold draw
  dsimp only
  split
  · omega
  · rename_i result hSome
    let hSuccess := BinaryTerminalPhysicalAllowanceDraw.logical_success frame parsed hParsed seed rich result hSome
    have hs : 3 ≤ inputHeight parsed.1.2.logical.request := by unfold inputHeight; omega
    have h := BinaryWordTerminalEmissionMeasured.run_work seed result.2
      (terminal_canonical parsed.1.2.logical.request rich result.1)
      (BinaryPRGHeapCertifiedPrefixProperties.admissible seed parsed.1.2.logical.request rich result hSuccess)
      (inputHeight parsed.1.2.logical.request) hs
      (BinaryPRGHeapCertifiedPrefixProperties.uniform_height seed parsed.1.2.logical.request rich result hSuccess)
      (BinaryPRGHeapCertifiedPrefixProperties.mixed_height seed parsed.1.2.logical.request rich result hSuccess)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height seed parsed.1.2.logical.request rich result hSuccess)
      K outer scalar _ (BinaryTerminalPhysicalAllowanceDraw.cursor_bound frame parsed hParsed seed rich)
    change _+_+8 ≤ _
    omega

def fixed (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (((FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord seed.width) × List Bool) × Trace) × ℕ :=
  let drawn := draw frame parsed hParsed seed rich K outer scalar
  match drawn.1.1.1.1 with
  | some row => ((((row,drawn.1.1.1.2),drawn.1.1.2),wrap 24 2 [drawn.1.2]),drawn.2+4)
  | none =>
      let fallback := BinaryPRGGlobalFallbackMeasured.prepare (resourceInput parsed.1.2.logical.request rich)
      ((((fallback.1.1,drawn.1.1.1.2),drawn.1.1.2),wrap 32 2 [drawn.1.2,fallback.1.2]),drawn.2+fallback.2+8)

theorem fixed_data (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).1.1 =
      (BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar).1.1 := by
  unfold fixed BinaryTerminalPhysicalAllowanceFramed.fixed
  dsimp only
  simp only [draw_data]
  cases h : (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.1.1.1 with
  | none => simp only [BinaryPRGGlobalFallbackMeasured.prepare_data]
  | some row => rfl

def fixedDelta (n : ℕ) : ℕ := BinaryWordTerminalEmissionMeasured.delta n+arrayDelta n+16

theorem fixed_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    Growth (BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar).1.2
      (fixed frame parsed hParsed seed rich K outer scalar).1.2 (fixedDelta parsed.1.1) := by
  have hd := draw_growth frame parsed hParsed seed rich K outer scalar
  have hf := fallback_growth (resourceInput parsed.1.2.logical.request rich)
  unfold fixed BinaryTerminalPhysicalAllowanceFramed.fixed
  dsimp only
  simp only [draw_data]
  cases h : (BinaryTerminalPhysicalAllowanceDraw.run frame parsed hParsed seed rich K outer scalar).1.1.1.1 with
  | none =>
      have hg := wrap_two 32 2 _ _ _ _ _ _ hd hf
      exact growth_mono _ _ _ _ hg (by unfold fixedDelta drawDelta; omega)
  | some row =>
      have hg := wrap_one 24 2 _ _ _ hd
      exact growth_mono _ _ _ _ hg (by unfold fixedDelta drawDelta; omega)

theorem fixed_work (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (fixed frame parsed hParsed seed rich K outer scalar).2 ≤
      (BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar).2+
        BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K+
          68*(parsed.1.1+1)^2+16 := by
  have hd := draw_work frame parsed hParsed seed rich K outer scalar
  rw [BinaryTerminalPhysicalAllowanceDraw.run_carried_work] at hd
  rw [BinaryTerminalPhysicalAllowanceFramed.fixed_carried_work,
    BinaryTerminalPhysicalAllowanceDraw.run_carried_work]
  unfold fixed
  dsimp only
  split
  · change _+4 ≤ _
    omega
  · have hf := BinaryPRGGlobalFallbackMeasured.prepare_work_quadratic (resourceInput parsed.1.2.logical.request rich)
    change _+_+8 ≤ _
    omega

theorem fixed_usage_growth (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (fixed frame parsed hParsed seed rich K outer scalar).1.2 ≤
      usage (BinaryTerminalPhysicalAllowanceFramed.fixed frame parsed hParsed seed rich K outer scalar).1.2+
        2*fixedDelta parsed.1.1 :=
  usage_growth _ _ _ (fixed_growth frame parsed hParsed seed rich K outer scalar)

theorem fixed_fullBudget (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (seed : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (value (resourceInput parsed.1.2.logical.request rich).budget : ℝ)
      (fun j => (value ((fixed frame parsed hParsed seed rich K outer scalar).1.1.1.1.read j) : ℝ)) := by
  rw [fixed_data]
  exact BinaryTerminalPhysicalAllowanceFramed.fixed_fullBudget frame parsed hParsed seed rich K outer scalar

theorem fixedDelta_polynomial (n : ℕ) : fixedDelta n ≤ 4096*(n+4)^2 := by
  have ht := BinaryWordTerminalEmissionMeasured.delta_polynomial n
  have ha := arrayDelta_polynomial n
  have hp : (n+1)^2 ≤ (n+4)^2 := Nat.pow_le_pow_left (by omega) 2
  unfold fixedDelta
  nlinarith

theorem accepted_extra_work : ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (K : ℕ),
    BinaryWordTerminalEmissionMeasured.workEnvelope parsed.1.1 (inputHeight parsed.1.2.logical.request) K+
      68*(parsed.1.1+1)^2+16 ≤ C*(frame.length+K+3)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryWordTerminalEmissionMeasured.work_polynomial
  refine ⟨C*33^d+84,max d 2,?_⟩
  intro frame parsed hParsed K
  let X := frame.length+K+3
  have hX : 0 < X := by dsimp only [X]; omega
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width frame parsed hParsed
  have hi : inputHeight parsed.1.2.logical.request ≤ 32*(frame.length+1) := by
    unfold inputHeight
    omega
  have hSize : parsed.1.1+inputHeight parsed.1.2.logical.request+K+2 ≤ 33*X := by
    dsimp only [X]
    omega
  have hPower : C*(parsed.1.1+inputHeight parsed.1.2.logical.request+K+2)^d ≤
      (C*33^d)*X^(max d 2) := by
    calc
      _ ≤ C*(33*X)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSize d)
      _ = (C*33^d)*X^d := by rw [Nat.mul_pow]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (Nat.le_max_left _ _))
  have hSquare : (parsed.1.1+1)^2 ≤ X^(max d 2) :=
    (Nat.pow_le_pow_left (by dsimp only [X]; omega) 2).trans
      (Nat.pow_le_pow_right hX (Nat.le_max_right _ _))
  have hPositive : 1 ≤ (parsed.1.1+1)^2 := by
    have h : 0 < (parsed.1.1+1)^2 := by positivity
    omega
  have hEmit := hBound parsed.1.1 (inputHeight parsed.1.2.logical.request) K
  change _ ≤ (C*33^d+84)*X^(max d 2)
  nlinarith only [hEmit,hPower,hSquare,hPositive]

end Blotto.BinaryTerminalPhysicalEmissionFixed
