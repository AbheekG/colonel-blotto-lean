import Blotto.BinaryCompleteSeedEventBounds
import Blotto.BinaryTerminalPhysicalParsedRawMeasured

/-! Actual raw wrappers forward the complete seed ledger. Parser trace emission
is charged exactly; its remaining input-uniform event join is stated separately
from the closed accepted seed ledger. -/
namespace Blotto.BinaryCompleteRawCharges
open BinarySeedPreparationSpace BinarySamplerExecutionCharges
open BinaryTerminalPhysicalAllowanceCache (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem accepted_total (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    total (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 =
      total (BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich seed).2+
        5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+
        5*(BinaryTerminalPhysicalCompleteSeedMeasured.run frame parsed hParsed rich seed).1.2.length+18 := by
  unfold BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_left hTail,total_addWrapper,BinaryWrapperEmission.two_work,
      BinaryTerminalPhysicalCompleteSeedMeasured.run]
    omega

theorem rejected_none_total (rich : Bool) (frame seed : List Bool)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = none) :
    total (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 =
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+14 := by
  unfold BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
  dsimp only
  split
  · simp only [total_addWrapper,total_zero,BinaryWrapperEmission.one_work,Nat.zero_add]
  · rename_i selected hSome
    cases hParsed.symm.trans hSome

theorem rejected_tail_total (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 ≠ []) :
    total (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 =
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+14 := by
  unfold BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_right hTail,total_addWrapper,total_zero,BinaryWrapperEmission.one_work,Nat.zero_add]

theorem accepted_fields (rich : Bool) (frame seed : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (hTail : parsed.2 = []) :
    let incoming := BinaryTerminalPhysicalCompleteSeedMeasured.runWithCharges frame parsed hParsed rich seed
    let produced := BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed
    produced.2.execution.primitive = incoming.2.execution.primitive ∧
      produced.2.execution.coinSource = incoming.2.execution.coinSource ∧
      produced.2.execution.write = incoming.2.execution.write ∧ produced.2.execution.native = incoming.2.execution.native ∧
      produced.2.seedEmission = incoming.2.seedEmission := by
  unfold BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
  dsimp only
  split
  · rename_i hNone
    cases hParsed.symm.trans hNone
  · rename_i selected hSome
    have he := Option.some.inj (hParsed.symm.trans hSome)
    subst selected
    simp only [ite_eq_left hTail]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem parsed_ledger (rich : Bool) (frame seed : List Bool) :
    (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).2 =
      (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 := by
  unfold BinaryTerminalPhysicalParsedRawMeasured.runWithCharges BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges
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

theorem uniform_parser_footprint : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    total (BinaryTerminalPhysicalCompleteRawMeasured.runWithCharges rich frame seed).2 ≤
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+C*(frame.length+1)^d := by
  obtain ⟨C,d,hSeed⟩ := BinaryCompleteSeedCharges.accepted_uniform_charges
  obtain ⟨P,e,hTrace⟩ := BinaryCompleteSeedEventBounds.accepted_trace
  refine ⟨C+5*P+18,max d e,?_⟩
  intro rich frame seed
  have hX : 0 < frame.length+1 := by omega
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d e))
  have he := Nat.mul_le_mul_left P (Nat.pow_le_pow_right hX (Nat.le_max_right d e))
  have hOne := Nat.one_le_pow (max d e) (frame.length+1) (by omega)
  cases hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none =>
      have h := rejected_none_total rich frame seed hRead
      nlinarith only [h,hOne]
  | some parsed =>
      by_cases hTail : parsed.2 = []
      · have h := accepted_total rich frame seed parsed hRead hTail
        have hs := hSeed frame parsed hRead rich seed
        have ht := hTrace frame parsed hRead rich seed
        nlinarith only [h,hs,ht,hd,he,hOne]
      · have h := rejected_tail_total rich frame seed parsed hRead hTail
        nlinarith only [h,hOne]

theorem parsed_uniform_parser_footprint : ∃ C d : ℕ,∀ (rich : Bool) (frame seed : List Bool),
    total (BinaryTerminalPhysicalParsedRawMeasured.runWithCharges rich frame seed).2 ≤
      5*(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2.length+C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_parser_footprint
  refine ⟨C,d,?_⟩
  intro rich frame seed
  rw [parsed_ledger]
  exact h rich frame seed

end Blotto.BinaryCompleteRawCharges
