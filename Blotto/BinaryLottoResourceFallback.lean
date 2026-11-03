import Blotto.BinaryLottoResourceInput
import Blotto.BinaryGeneralResourceFallback

/-! The deterministic native lower resource path prepares a valid terminal
Lotto grouping input, exactly refining the retained invariant-restricted phase
lower leaf. This phase fallback is separate from the manuscript's global
exhaustion allocation (B,0,...,0), which is preserved by the final output. -/

namespace Blotto.BinaryLottoResourceFallback
open BinaryRationalNormalization BinaryRationalEncoding BinaryResourcePair BinaryLottoResourceInput

def state {n : ℕ} (input : Input n) (hC : input.Canonical) : Certified input.length:=
  BinaryGeneralResourceFallback.choose hC.2.1 (initial input hC)

def grouping {n : ℕ} (input : Input n) (hC : input.Canonical) : BinaryTerminalGrouping.Input n:=
  groupingInput input (state input hC)

theorem state_terminal {n : ℕ} (input : Input n) (hC : input.Canonical) : (state input hC).state.active.length≤1:=
  BinaryGeneralResourceFallback.choose_terminal hC.2.1 (initial input hC)

theorem state_invariant {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    RationalResourceInvariant (fun j=>value (input.length.read j)) (2*(source.B : ℝ)) (state input hC).reference:=
  BinaryGeneralResourceFallback.choose_invariant hC.2.1 (initial input hC) _
    (initial_invariant input source hC hr)

noncomputable def terminal {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) : RationalTerminalLotto n:=
  terminalOf input source hr (state input hC) (state_invariant input source hC hr) (state_terminal input hC)

theorem grouping_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    (grouping input hC).Refines (terminal input source hC hr):=
  groupingInput_refines input source hr (state input hC) _ _

theorem grouping_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) : (grouping input hC).Canonical:=
  groupingInput_canonical input hC _

theorem resource_choose_transport {n : ℕ} {L L' : Fin n→ℚ} (he : L=L') (s : RationalActiveResources L) :
    transportState he ((rationalResourceMachine L).chooseLeaf (.ready s))=
      (rationalResourceMachine L').chooseLeaf (.ready (transportState he s)):=by cases he; rfl

theorem state_eq_phase_leaf {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    sourceState input source hr (state input hC)=(source.phase.chooseLeaf source.start).1:=by
  rw [sourceState_transport]
  have he:=BinaryGeneralResourceFallback.choose_refines hC.2.1 (initial input hC)
  change (state input hC).reference=_ at he
  rw [he,resource_choose_transport,initial_transport input source hC hr]
  exact ((rationalResourceMachine source.length).restricted_chooseLeaf source.CursorInvariant source.TerminalState source.phaseProof source.start).symm

theorem terminal_eq_phase_data {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) :
    terminal input source hC hr=source.terminalData (source.phase.chooseLeaf source.start):=by
  unfold terminal terminalOf RationalLottoResourceSystem.terminalData
  congr 1
  exact state_eq_phase_leaf input source hC hr


theorem grouping_admissible {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) :
    ∃ terminal : RationalTerminalLotto n,(grouping input hC).Refines terminal:=by
  obtain ⟨source,hr⟩:=hAd
  exact ⟨terminal input source hC hr,grouping_refines input source hC hr⟩

end Blotto.BinaryLottoResourceFallback
