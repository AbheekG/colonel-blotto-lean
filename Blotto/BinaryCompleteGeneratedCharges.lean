import Blotto.BinaryClosedRawCharges
import Blotto.BinaryGeneratedSeedTraceBounds
import Blotto.BinaryTerminalPhysicalParsedGeneratedBounds

/-! The actual fresh-bit single/pair callers transport the extended sampler
ledger. Entropy generation retains its preceding measured source price; seed
emission still means seed-store emission. The pair consumes the first draw's
returned entropy state and adds both actually reached ledgers. -/
namespace Blotto.BinaryCompleteGeneratedCharges
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinarySamplerExecutionCharges
open BinaryTerminalPhysicalCompleteGeneratedMeasured
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem accepted_total {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
    let supplied := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich generated.1.1.1
    total (runWithCharges next rich frame state).2 = total supplied.2+
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+
      5*generated.1.2.length+5*supplied.1.1.2.length+22 := by
  rw [runWithCharges_eq_reference]
  unfold runWithChargesReference
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_left hTail,total_addWrapper,BinarySeedWrapperEmission.three_work]
    omega

theorem rejected_none_total {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    total (runWithCharges next rich frame state).2 =
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+14 := by
  rw [runWithCharges_eq_reference]
  unfold runWithChargesReference
  dsimp only
  split
  · simp only [total_addWrapper,total_zero,BinaryWrapperEmission.one_work,Nat.zero_add]
  · rename_i selected hSome
    cases hParsed.symm.trans hSome

theorem rejected_tail_total {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    total (runWithCharges next rich frame state).2 =
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+14 := by
  rw [runWithCharges_eq_reference]
  unfold runWithChargesReference
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_right hTail,total_addWrapper,total_zero,BinaryWrapperEmission.one_work,Nat.zero_add]

theorem accepted_fields {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    let generated := BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state
    let supplied := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich generated.1.1.1
    let produced := runWithCharges next rich frame state
    produced.2.execution.primitive = supplied.2.execution.primitive ∧
      produced.2.execution.coinSource = supplied.2.execution.coinSource ∧
      produced.2.execution.write = supplied.2.execution.write ∧ produced.2.execution.native = supplied.2.execution.native ∧
      produced.2.seedEmission = supplied.2.seedEmission := by
  rw [runWithCharges_eq_reference]
  unfold runWithChargesReference
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_left hTail]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem parsed_ledger {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).2 =
      (runWithCharges next rich frame state).2 := by
  rw [BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges_eq_reference,runWithCharges_eq_reference]
  unfold BinaryTerminalPhysicalParsedGeneratedMeasured.runWithChargesReference runWithChargesReference
  dsimp only
  split
  · rename_i hNone
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hNone
    split
    · simp only [BinaryPRGPhysicalRawRequestMeasured.read_erases]
    · rename_i parsed hSome
      cases hOld.symm.trans hSome
  · rename_i parsed hSome
    have hOld := (congrArg Prod.fst (BinaryPRGPhysicalRawRequestMeasured.read_erases frame)).symm.trans hSome
    symm
    split
    · rename_i hNone
      cases hOld.symm.trans hNone
    · rename_i other hOther
      have he := Option.some.inj (hOld.symm.trans hOther)
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,BinaryPRGPhysicalRawRequestMeasured.read_erases]
      · simp only [ite_eq_right hTail,BinaryPRGPhysicalRawRequestMeasured.read_erases]

theorem uniform_total : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    total (runWithCharges next rich frame state).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := BinaryCompleteSeedCharges.accepted_uniform_charges
  obtain ⟨T,e,hTrace⟩ := BinaryCompleteSeedEventBounds.accepted_trace
  obtain ⟨P,f,hParser⟩ := BinaryPhysicalParserTraceSparsity.uniform_parser_length
  let D := max (max d e) (max f 1)
  refine ⟨C+5*T+5*P+5000022,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (show d ≤ D by dsimp [D]; omega))
  have he := Nat.mul_le_mul_left T (Nat.pow_le_pow_right hX (show e ≤ D by dsimp [D]; omega))
  have hf := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (show f ≤ D by dsimp [D]; omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp [D]; omega)
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  have hp := hParser frame
  cases hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      have h := rejected_none_total next rich frame state hRead
      nlinarith only [h,hp,hf,hOne]
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · have h := accepted_total next rich frame state parsed hRead hTail
        have hs := hSeed frame parsed hRead rich (BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state).1.1.1
        have ht := hTrace frame parsed hRead rich (BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state).1.1.1
        have hg := BinaryGeneratedSeedTraceBounds.physical_generate_length next frame parsed hRead state
        change (BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hRead rich
          (BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state).1.1.1).1.1.2.length ≤ _ at ht
        dsimp only at h
        nlinarith only [h,hs,ht,hg,hp,hd,he,hf,hLinear,hOne]
      · have h := rejected_tail_total next rich frame state parsed hRead hTail
        nlinarith only [h,hp,hf,hOne]

theorem uniform_trace : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    (run next rich frame state).1.2.length ≤ C*(frame.length+1)^d := by
  obtain ⟨T,e,hTrace⟩ := BinaryCompleteSeedEventBounds.accepted_trace
  obtain ⟨P,f,hParser⟩ := BinaryPhysicalParserTraceSparsity.uniform_parser_length
  let D := max e (max f 1)
  refine ⟨T+P+1000002,D,?_⟩
  intro S next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have he := Nat.mul_le_mul_left T (Nat.pow_le_pow_right hX (show e ≤ D by dsimp [D]; omega))
  have hf := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (show f ≤ D by dsimp [D]; omega))
  have hLinear : frame.length+1 ≤ (frame.length+1)^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp [D]; omega)
  have hOne := Nat.one_le_pow D (frame.length+1) (by omega)
  have hp := hParser frame
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · simp only [wrap,combine,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
      List.append_nil,List.length_append,List.length_cons,List.length_nil,BinaryResourceTraceLength.under_length]
    nlinarith only [hp,hf,hOne]
  · rename_i parsed hParsed
    split
    · have ht := hTrace frame parsed hParsed rich (BinaryPRGRulerSeedMeasured.generate next parsed.1.2.logical state).1.1.1
      have hg := BinaryGeneratedSeedTraceBounds.physical_generate_length next frame parsed hParsed state
      simp only [wrap,combine,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
        List.append_nil,List.length_append,List.length_cons,List.length_nil,BinaryResourceTraceLength.under_length]
      nlinarith only [ht,hg,hp,he,hf,hLinear,hOne]
    · simp only [wrap,combine,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
        List.append_nil,List.length_append,List.length_cons,List.length_nil,BinaryResourceTraceLength.under_length]
      nlinarith only [hp,hf,hOne]

theorem pair_total {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    total (pairWithCharges next frame state).2 = total (runWithCharges next true frame state).2+
      total (runWithCharges next false frame (run next true frame state).1.1.1.2).2+
      5*(run next true frame state).1.2.length+
      5*(run next false frame (run next true frame state).1.1.1.2).1.2.length+18 := by
  simp only [pairWithCharges_eq_reference,pairWithChargesReference,total_addWrapper,total_add,BinaryWrapperEmission.two_work,run]
  omega

theorem pair_fields {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    let rich := runWithCharges next true frame state
    let poor := runWithCharges next false frame rich.1.1.1.1.2
    let produced := pairWithCharges next frame state
    produced.2.execution.primitive = rich.2.execution.primitive+poor.2.execution.primitive ∧
      produced.2.execution.coinSource = rich.2.execution.coinSource+poor.2.execution.coinSource ∧
      produced.2.execution.write = rich.2.execution.write+poor.2.execution.write ∧
      produced.2.execution.native = rich.2.execution.native+poor.2.execution.native ∧
      produced.2.seedEmission = rich.2.seedEmission+poor.2.seedEmission := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem parsed_pair_ledger {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).2 =
      (pairWithCharges next frame state).2 := by
  simp only [BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges_eq_reference,pairWithCharges_eq_reference,
    BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithChargesReference,pairWithChargesReference,
    BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges_compat,
    runWithCharges_compat,BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases,parsed_ledger]

theorem pair_uniform_total : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    total (pairWithCharges next frame state).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hTotal⟩ := uniform_total
  obtain ⟨P,e,hTrace⟩ := uniform_trace
  refine ⟨2*C+10*P+18,max d e,?_⟩
  intro S next frame state
  have hr := hTotal next true frame state
  have hp := hTotal next false frame (run next true frame state).1.1.1.2
  have hrt := hTrace next true frame state
  have hpt := hTrace next false frame (run next true frame state).1.1.1.2
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) (frame.length+1) (by omega)
  rw [pair_total]
  nlinarith only [hr,hp,hrt,hpt,hd,he,hOne]

theorem parsed_uniform_total : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    total (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_total
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  rw [parsed_ledger]
  exact h next rich frame state

theorem parsed_pair_uniform_total : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    total (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := pair_uniform_total
  refine ⟨C,d,?_⟩
  intro S next frame state
  rw [parsed_pair_ledger]
  exact h next frame state

theorem parsed_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalParsedGeneratedBounds.uniform_joint
  obtain ⟨P,e,hLedger⟩ := parsed_uniform_total
  refine ⟨C+P,max d e,?_⟩
  intro S next rich frame state
  have ho := hOld next rich frame state
  have hl := hLedger next rich frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  change (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).1.2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).1.1.1.2+
    usage (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).1.1.2 ≤ _ at ho
  dsimp only
  nlinarith only [ho,hl,hd,he]

theorem parsed_pair_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+
      BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hOld⟩ := BinaryTerminalPhysicalParsedGeneratedBounds.pair_uniform_joint
  obtain ⟨P,e,hLedger⟩ := parsed_pair_uniform_total
  refine ⟨C+P,max d e,?_⟩
  intro S next frame state
  have ho := hOld next frame state
  have hl := hLedger next frame state
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  change (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).1.2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).1.1.1.2.1+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).1.1.1.2.2+
    usage (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).1.1.2 ≤ _ at ho
  dsimp only
  nlinarith only [ho,hl,hd,he]

theorem uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := runWithCharges next rich frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := parsed_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next rich frame state
  have hp := hBound next rich frame state
  change (BinaryTerminalPhysicalParsedGeneratedMeasured.run next rich frame state).2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.run next rich frame state).1.1.2+
    usage (BinaryTerminalPhysicalParsedGeneratedMeasured.run next rich frame state).1.2+
    total (BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state).2 ≤ _ at hp
  rw [BinaryTerminalPhysicalParsedGeneratedMeasured.run_charge,
    BinaryTerminalPhysicalParsedGeneratedMeasured.run_erases,parsed_ledger] at hp
  dsimp only
  change (run next rich frame state).2+BinaryBigEndian.littleValue (run next rich frame state).1.1.2+
    usage (run next rich frame state).1.2+total (runWithCharges next rich frame state).2 ≤ _
  omega

theorem pair_uniform_joint : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := pairWithCharges next frame state
    produced.1.2+BinaryBigEndian.littleValue produced.1.1.1.2.1+
      BinaryBigEndian.littleValue produced.1.1.1.2.2+usage produced.1.1.2+total produced.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := parsed_pair_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  have hp := hBound next frame state
  change (BinaryTerminalPhysicalParsedGeneratedMeasured.pair next frame state).2+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.pair next frame state).1.1.2.1+
    BinaryBigEndian.littleValue (BinaryTerminalPhysicalParsedGeneratedMeasured.pair next frame state).1.1.2.2+
    usage (BinaryTerminalPhysicalParsedGeneratedMeasured.pair next frame state).1.2+
    total (BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state).2 ≤ _ at hp
  rw [BinaryTerminalPhysicalParsedGeneratedMeasured.pair_charge,
    BinaryTerminalPhysicalParsedGeneratedMeasured.pair_erases,parsed_pair_ledger] at hp
  dsimp only
  change (pair next frame state).2+BinaryBigEndian.littleValue (pair next frame state).1.1.2.1+
    BinaryBigEndian.littleValue (pair next frame state).1.1.2.2+usage (pair next frame state).1.2+
    total (pairWithCharges next frame state).2 ≤ _
  omega

theorem counter_width (source allowance retained : ℕ) (charges : Charges) (L C d : ℕ)
    (hBound : source+allowance+retained+total charges ≤ C*(L+1)^d) :
    ∀ counter ∈ [source,charges.execution.primitive,charges.execution.coinSource,charges.execution.write,
      charges.execution.native,charges.execution.wrappers,charges.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (L+1) := by
  have hf := fields_le_total charges
  have hm := binaryWordWidth_mul C ((L+1)^d)
  have hp := Farey.binaryWordWidth_power (L+1) d
  have hWidth := binaryWordWidth_mono hBound
  intro counter hCounter
  have hc : counter ≤ source+allowance+retained+total charges := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hCounter
    rcases hCounter with h | h | h | h | h | h | h <;> subst counter <;> omega
  have hw := binaryWordWidth_mono hc
  omega

theorem parsed_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.runWithCharges next rich frame state
    ∀ counter ∈ [produced.1.2,produced.2.execution.primitive,produced.2.execution.coinSource,
      produced.2.execution.write,produced.2.execution.native,produced.2.execution.wrappers,produced.2.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsed_uniform_joint
  exact ⟨C,d,fun next rich frame state => counter_width _ _ _ _ _ C d (hBound next rich frame state)⟩

theorem parsed_pair_scalar_width : ∃ C d : ℕ,∀ {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S),
    let produced := BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithCharges next frame state
    ∀ counter ∈ [produced.1.2,produced.2.execution.primitive,produced.2.execution.coinSource,
      produced.2.execution.write,produced.2.execution.native,produced.2.execution.wrappers,produced.2.seedEmission],
      binaryWordWidth counter ≤ binaryWordWidth C+1+d*binaryWordWidth (frame.length+1) := by
  obtain ⟨C,d,hBound⟩ := parsed_pair_uniform_joint
  refine ⟨C,d,?_⟩
  intro S next frame state
  exact counter_width _ (_+_) _ _ _ C d (by simpa only [Nat.add_assoc] using hBound next frame state)

end Blotto.BinaryCompleteGeneratedCharges
