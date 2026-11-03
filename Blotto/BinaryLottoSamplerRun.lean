import Blotto.BinaryLottoResourceInput
import Blotto.BinaryTerminalPartialRun
import Blotto.WordMachineSerialRun

/-! Native general-field PRG execution retains one resource result and hands
the same reader and absolute position to the actual terminal coupling. Neither
phase absorbs exhaustion. Runtime inputs are stored words and erased promises;
the exact original rational source is used only in refinement proofs. -/

namespace Blotto.BinaryLottoSamplerRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryLottoResourceInput

theorem resource_position {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) : (BinaryLottoResourceInput.run input hC N bits).2 ≤ N := by
  obtain ⟨source,hr⟩ := hAd
  rw [run_phase_position input source hC hr N bits]
  exact source.phase.run_bits_le N source.start bits

def run {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : Option (FixedArrayTable n SignedWord) × ℕ :=
  let result := BinaryLottoResourceInput.run input hC N bits
  match hs : result.1 with
  | none => (none,result.2)
  | some state =>
      BinaryTerminalPartialRun.runIndexed (groupingInput input state) (groupingInput_canonical input hC state)
        (reachedGrouping_admissible input hC hAd N bits state hs) K N outer scalar bits result.2
        (resource_position input hC hAd N bits)

theorem source_serial_run {n : ℕ} (source : RationalLottoResourceSystem n) (K N : ℕ)
    (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (source.machine K outer scalar).run N (source.samplingStart K outer scalar) bits =
      WordStateMachine.handoff N (source.phase.run N source.start bits)
        (fun state pos hp => ((source.terminalData state).program K outer scalar).machine.runCursorIndexed N bits
          (.state ((source.terminalData state).program K outer scalar).start) pos hp) := by
  rw [WordStateMachine.run_eq_numeric]
  unfold WordStateMachine.runNumeric RationalLottoResourceSystem.machine RationalLottoResourceSystem.samplingStart
  have he := WordStateMachine.serial_source_run source.phase
    (fun state => ((source.terminalData state).program K outer scalar).machine)
    (fun state => ((source.terminalData state).program K outer scalar).start) 80
    (fun state => ((source.terminalData state).program K outer scalar).rank_le) N bits (.state source.start) 0 (Nat.zero_le N)
  dsimp only [WordCursor.mapState] at he
  rw [he]
  rw [WordStateMachine.run_eq_numeric]
  rfl

theorem indexed_position_congr {S α : Type*} (machine : WordStateMachine S α) (N : ℕ)
    (bits : Fin N → Bool) (cursor : WordCursor S) (pos pos' : ℕ) (hp : pos ≤ N) (hp' : pos' ≤ N)
    (he : pos = pos') : machine.runCursorIndexed N bits cursor pos hp = machine.runCursorIndexed N bits cursor pos' hp' := by
  have hs : (⟨pos,hp⟩ : {v : ℕ // v ≤ N}) = ⟨pos',hp'⟩ := Subtype.ext he
  exact congrArg (fun p : {v : ℕ // v ≤ N} => machine.runCursorIndexed N bits cursor p.val p.property) hs

theorem run_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ((run input hC hAd K N outer scalar bits).1.map BinaryTerminalPartialRun.sourceRow,
      (run input hC hAd K N outer scalar bits).2) =
      (source.machine K outer scalar).run N (source.samplingStart K outer scalar) bits := by
  rw [source_serial_run]
  unfold run
  dsimp only
  split
  · rename_i hn
    have hs := (run_phase_failure_iff input source hC hr N bits).mp hn
    simp only [WordStateMachine.handoff,hs,Option.map_none]
    exact Prod.ext rfl (run_phase_position input source hC hr N bits)
  · rename_i state hs
    have hPhase := run_phase_success input source hC hr N bits state hs
    have hPos := run_phase_position input source hC hr N bits
    have hBound := source.phase.run_bits_le N source.start bits
    simp only [WordStateMachine.handoff,hPhase,hBound,dite_true]
    rw [←reachedTerminal_eq_phase_data input source hC hr N bits state hs]
    have ht := BinaryTerminalPartialRun.runIndexed_refines (groupingInput input state)
      (reachedTerminal input source hC hr N bits state hs) (groupingInput_canonical input hC state)
      (reachedGrouping_refines input source hC hr N bits state hs)
      (reachedGrouping_admissible input hC hAd N bits state hs) K N outer scalar bits
      (BinaryLottoResourceInput.run input hC N bits).2 (resource_position input hC hAd N bits)
    apply ht.trans
    exact indexed_position_congr _ _ _ _ _ _ _ _ hPos

theorem run_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool)
    (row : FixedArrayTable n SignedWord) (hs : (run input hC hAd K N outer scalar bits).1 = some row) :
    ∀ j, CanonicalWord (row.read j) := by
  unfold run at hs
  dsimp only at hs
  split at hs
  · cases hs
  · exact BinaryTerminalPartialRun.runIndexed_canonical _ _ _ _ _ _ _ _ _ _ row hs

theorem run_position {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).2 ≤ N := by
  obtain ⟨source,hr⟩ := hAd
  have he := congrArg Prod.snd (run_refines input source hC hr (show Admissible input from ⟨source,hr⟩) K N outer scalar bits)
  exact he.trans_le ((source.machine K outer scalar).run_bits_le N (source.samplingStart K outer scalar) bits)

end Blotto.BinaryLottoSamplerRun
