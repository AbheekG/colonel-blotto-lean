import Blotto.BinaryRawParserContinuation

/-! Forget only the newest parser counter while retaining an arbitrary prior
counter. This reusable projection preserves complete single and sequential-pair
execution records, including all earlier prices and actual state order. -/
namespace Blotto.BinaryRawParserProjection
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryRawParserContinuation
set_option autoImplicit false
set_option maxHeartbeats 4000000

def keepReader {α F E : Type*} (record : α × (F × E)) : α × F := (record.1,record.2.1)

def Refines {F E : Type*} (backend : Backend (F × E)) (prior : Backend F) : Prop :=
  ∀ frame,keepReader (backend.run frame) = prior.run frame

def keepComplete {α F E : Type*} (out : α × ((ℕ × ℕ) × (Prices × (F × E)))) :
    α × ((ℕ × ℕ) × (Prices × F)) :=
  (out.1,(out.2.1,(out.2.2.1,out.2.2.2.1)))

variable {F E : Type*} [Zero F] [Add F] [Zero E] [Add E]

theorem raw_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior) (rich : Bool) (frame bits : List Bool) :
    keepComplete (raw backend rich frame bits) = raw prior rich frame bits := by
  have hReader := hRun frame
  have hRecord := congrArg Prod.fst hReader
  have hExtra := congrArg Prod.snd hReader
  dsimp only [keepReader] at hRecord hExtra
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  simp only [BinaryRawParserContinuation.raw_record,keepComplete]
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical,hExtra]
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
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical,hExtra]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical,hExtra]


theorem parsedRaw_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior) (rich : Bool) (frame bits : List Bool) :
    keepComplete (parsedRaw backend rich frame bits) = parsedRaw prior rich frame bits := by
  have hReader := hRun frame
  have hRecord := congrArg Prod.fst hReader
  have hExtra := congrArg Prod.snd hReader
  dsimp only [keepReader] at hRecord hExtra
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  simp only [BinaryRawParserContinuation.parsedRaw_record,keepComplete]
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical,hExtra]
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
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical,hExtra]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical,hExtra]


theorem generated_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    keepComplete (generated backend next rich frame state) = generated prior next rich frame state := by
  have hReader := hRun frame
  have hRecord := congrArg Prod.fst hReader
  have hExtra := congrArg Prod.snd hReader
  dsimp only [keepReader] at hRecord hExtra
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  simp only [BinaryRawParserContinuation.generated_record,keepComplete]
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical,hExtra]
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
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical,hExtra]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical,hExtra]


theorem parsedGenerated_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior) {S : Type*} (next : S → Bool × S) (rich : Bool) (frame : List Bool) (state : S) :
    keepComplete (parsedGenerated backend next rich frame state) = parsedGenerated prior next rich frame state := by
  have hReader := hRun frame
  have hRecord := congrArg Prod.fst hReader
  have hExtra := congrArg Prod.snd hReader
  dsimp only [keepReader] at hRecord hExtra
  have hData := congrArg (fun out => out.1.1.1) hRecord
  have hTrace := congrArg (fun out => out.1.1.2) hRecord
  have hSource := congrArg (fun out => out.1.2) hRecord
  have hCanonical := congrArg Prod.snd hRecord
  simp only [BinaryRawParserContinuation.parsedGenerated_record,keepComplete]
  split
  · rename_i hNone
    split
    · simp only [hTrace,hSource,hCanonical,hExtra]
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
      · simp only [ite_eq_left hTail,hTrace,hSource,hCanonical,hExtra]
      · simp only [ite_eq_right hTail,hTrace,hSource,hCanonical,hExtra]


theorem pair_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    keepComplete (pair backend next frame state) = pair prior next frame state := by
  change keepComplete (pair backend next frame state) =
    (
      let first := generated prior next true frame state
      let rich := first.1
      let second := generated prior next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [BinaryRawParserContinuation.pair_record,← generated_keep backend prior hRun,keepComplete]
  rfl


theorem parsedPair_keep (backend : Backend (F × E)) (prior : Backend F) (hRun : Refines backend prior)
    {S : Type*} (next : S → Bool × S) (frame : List Bool) (state : S) :
    keepComplete (parsedPair backend next frame state) = parsedPair prior next frame state := by
  change keepComplete (parsedPair backend next frame state) =
    (
      let first := parsedGenerated prior next true frame state
      let rich := first.1
      let second := parsedGenerated prior next false frame rich.1.1.1.1.2
      let poor := second.1
      let result :=
        let data := ((rich.1.1.1.1.1,poor.1.1.1.1.1),poor.1.1.1.1.2)
        let emitted := BinaryWrapperEmission.two 64 2 rich.1.1.2 poor.1.1.2
        ((((data,(rich.1.1.1.2,poor.1.1.1.2)),emitted.1),rich.1.2+poor.1.2+8),
          BinaryGenerationExecutionCharges.addWrapper (BinaryGenerationExecutionCharges.add rich.2 poor.2) emitted.2)
      (result,((first.2.1.1+second.2.1.1,first.2.1.2+second.2.1.2),first.2.2+second.2.2)))
  simp only [BinaryRawParserContinuation.parsedPair_record,← parsedGenerated_keep backend prior hRun,keepComplete]
  rfl


end Blotto.BinaryRawParserProjection
