import Blotto.BinaryPhysicalPayloadPlan
import Blotto.BinaryCacheFinishRequest

/-! The actual planned-payload physical parser feeds supplied/generated PRG
execution. Old legacy/measured raw records and every preceding price are
preserved on forgetting the new parser charge. Reject before entropy. -/
namespace Blotto.BinaryParserPayloadRequest
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Prices := BinaryCacheFinishRequest.Prices × ℕ

def raw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let produced := BinaryPhysicalPayloadPlan.read frame
  let decoded := produced.1
  let price := produced.1.2+produced.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),(0,price)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPhysicalPayloadPlan.read_original frame)).symm.trans hParsed
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,(child.2.1,(child.2.2,price)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),(0,price)))

def parsedRaw (rich : Bool) (frame bits : List Bool) :
    ((((Option (List Bool) × List Bool) × Trace) × ℕ) × BinarySamplerExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let produced := BinaryPhysicalPayloadPlan.read frame
  let decoded := produced.1
  let price := produced.1.2+produced.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 16 2 decoded.1.2
        ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
      (result,((0,0),(0,price)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPhysicalPayloadPlan.read_original frame)).symm.trans hParsed
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich bits
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinaryWrapperEmission.two 32 2 decoded.1.2 output.1.2
          (((output.1.1,emitted.1),decoded.2+output.2+8),BinarySamplerExecutionCharges.addWrapper returned.2 emitted.2)
        (result,(child.2.1,(child.2.2,price)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
          ((((none,[]),emitted.1),decoded.2+4),BinarySamplerExecutionCharges.addWrapper BinarySamplerExecutionCharges.zero emitted.2)
        (result,((0,0),(0,price)))

def generated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let produced := BinaryPhysicalPayloadPlan.read frame
  let decoded := produced.1
  let price := produced.1.2+produced.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),(0,price)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPhysicalPayloadPlan.read_original frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,(child.2.1,(child.2.2,price)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),(0,price)))

def parsedGenerated {S : Type*} (next : S → Bool × S) (rich : Bool)
    (frame : List Bool) (state : S) :
    (((((Option (List Bool) × S) × List Bool) × Trace) × ℕ) × BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let produced := BinaryPhysicalPayloadPlan.read frame
  let decoded := produced.1
  let price := produced.1.2+produced.2
  match hParsed : decoded.1.1 with
  | none =>
      let result :=
        let emitted := BinaryWrapperEmission.one 24 2 decoded.1.2
        (((((none,state),[]),emitted.1),decoded.2+4),
          BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
      (result,((0,0),(0,price)))
  | some parsed =>
      if parsed.2 = [] then
        have hOriginal : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed :=
          (congrArg Prod.fst (BinaryPhysicalPayloadPlan.read_original frame)).symm.trans hParsed
        let generation := BinaryFreshGenerationPlan.generateWithEmission next parsed.1.2.logical state
        let generated := generation.1
        let child := BinaryCacheFinishRequest.seed frame parsed hOriginal rich generated.1.1.1
        let returned := child.1
        let result :=
          let output := returned.1
          let emitted := BinarySeedWrapperEmission.three 48 2 decoded.1.2 generated.1.2 output.1.2
          (((((output.1.1.1,generated.1.1.2),output.1.1.2),emitted.1),decoded.2+output.2+generated.2+8),
            BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.ofSampler returned.2 generation.2) emitted.2)
        (result,(child.2.1,(child.2.2,price)))
      else
        let result :=
          let emitted := BinaryWrapperEmission.one 32 2 decoded.1.2
          (((((none,state),[]),emitted.1),decoded.2+4),
            BinaryGenerationExecutionCharges.addWrapper BinaryGenerationExecutionCharges.zero emitted.2)
        (result,((0,0),(0,price)))

theorem raw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (raw rich frame bits) = BinaryCacheFinishRequest.raw rich frame bits := by
  have hRecord := BinaryPhysicalPayloadPlan.read_original frame
  have hData := congrArg Prod.fst hRecord
  have hTrace := congrArg Prod.snd hRecord
  unfold raw BinaryCacheFinishRequest.raw BinaryCacheContinuationCore.raw
    BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,BinaryCacheFinishRequest.seed_record]
      · simp only [ite_eq_right hTail,hTrace]

theorem parsedRaw_preceding (rich : Bool) (frame bits : List Bool) :
    BinaryCacheContinuationProjection.keepComplete (parsedRaw rich frame bits) = BinaryCacheFinishRequest.parsedRaw rich frame bits := by
  have hRecord := BinaryPhysicalPayloadPlan.read_compat frame
  have hData := congrArg (fun out => out.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.2) hRecord
  have hSource := congrArg Prod.snd hRecord
  unfold parsedRaw BinaryCacheFinishRequest.parsedRaw BinaryCacheContinuationCore.parsedRaw
    BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,BinaryCacheFinishRequest.seed_record]
      · simp only [ite_eq_right hTail,hTrace,hSource]

theorem generated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (generated next rich frame state) = BinaryCacheFinishRequest.generated next rich frame state := by
  have hRecord := BinaryPhysicalPayloadPlan.read_original frame
  have hData := congrArg Prod.fst hRecord
  have hTrace := congrArg Prod.snd hRecord
  unfold generated BinaryCacheFinishRequest.generated BinaryCacheContinuationCore.generated
    BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,BinaryCacheFinishRequest.seed_record]
      · simp only [ite_eq_right hTail,hTrace]

theorem parsedGenerated_preceding {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedGenerated next rich frame state) = BinaryCacheFinishRequest.parsedGenerated next rich frame state := by
  have hRecord := BinaryPhysicalPayloadPlan.read_compat frame
  have hData := congrArg (fun out => out.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.2) hRecord
  have hSource := congrArg Prod.snd hRecord
  unfold parsedGenerated BinaryCacheFinishRequest.parsedGenerated BinaryCacheContinuationCore.parsedGenerated
    BinaryCacheContinuationProjection.keepComplete
  dsimp only
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource]
    · rename_i other hSome
      cases hNone.symm.trans (hData.trans hSome)
  · rename_i parsed hSome
    symm
    split
    · rename_i hNone
      cases hSome.symm.trans (hData.trans hNone)
    · rename_i other hOther
      have he := Option.some.inj (hSome.symm.trans (hData.trans hOther))
      subst other
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail,hTrace,hSource,BinaryCacheFinishRequest.seed_record]
      · simp only [ite_eq_right hTail,hTrace,hSource]

def pair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let first := generated next true frame state
  let rich := first.1
  let second := generated next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2))

def parsedPair {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    ((((((Option (List Bool) × Option (List Bool)) × S) × (List Bool × List Bool)) × Trace) × ℕ) ×
      BinaryGenerationExecutionCharges.Charges) × ((ℕ × ℕ) × (Prices × ℕ)) :=
  let first := parsedGenerated next true frame state
  let rich := first.1
  let second := parsedGenerated next false frame rich.1.1.1.1.2
  let poor := second.1
  let result :=
    let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
    let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
    ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
      BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
  (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2))

theorem pair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (pair next frame state) = BinaryCacheFinishRequest.pair next frame state := by
  change BinaryCacheContinuationProjection.keepComplete (pair next frame state) =
    (
      let first := BinaryCacheFinishRequest.generated next true frame state
      let rich := first.1
      let second := BinaryCacheFinishRequest.generated next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [pair,← generated_preceding,BinaryCacheContinuationProjection.keepComplete]
  rfl

theorem parsedPair_preceding {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    BinaryCacheContinuationProjection.keepComplete (parsedPair next frame state) = BinaryCacheFinishRequest.parsedPair next frame state := by
  change BinaryCacheContinuationProjection.keepComplete (parsedPair next frame state) =
    (
      let first := BinaryCacheFinishRequest.parsedGenerated next true frame state
      let rich := first.1
      let second := BinaryCacheFinishRequest.parsedGenerated next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [parsedPair,← parsedGenerated_preceding,BinaryCacheContinuationProjection.keepComplete]
  rfl

theorem raw_compat (rich : Bool) (frame bits : List Bool) :
    (raw rich frame bits).1 = BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (raw_preceding rich frame bits)).trans (BinaryCacheFinishRequest.raw_compat rich frame bits)

theorem parsedRaw_compat (rich : Bool) (frame bits : List Bool) :
    (parsedRaw rich frame bits).1 = BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame bits :=
  (congrArg Prod.fst (parsedRaw_preceding rich frame bits)).trans (BinaryCacheFinishRequest.parsedRaw_compat rich frame bits)

theorem generated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (generated next rich frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (generated_preceding next rich frame state)).trans (BinaryCacheFinishRequest.generated_compat next rich frame state)

theorem parsedGenerated_compat {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    (parsedGenerated next rich frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.runWithGeneration next rich frame state :=
  (congrArg Prod.fst (parsedGenerated_preceding next rich frame state)).trans (BinaryCacheFinishRequest.parsedGenerated_compat next rich frame state)

theorem pair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (pair next frame state).1 = BinaryTerminalPhysicalCompleteGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (pair_preceding next frame state)).trans (BinaryCacheFinishRequest.pair_compat next frame state)

theorem parsedPair_compat {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    (parsedPair next frame state).1 = BinaryTerminalPhysicalParsedGeneratedMeasured.pairWithGeneration next frame state :=
  (congrArg Prod.fst (parsedPair_preceding next frame state)).trans (BinaryCacheFinishRequest.parsedPair_compat next frame state)

end Blotto.BinaryParserPayloadRequest
