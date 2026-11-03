import Blotto.BinaryPRGResourceHandoff
import Blotto.BinaryGreedyPackingWork

/-! A successful actual resource run supplies terminal canonicality and fixed
lattice word bounds. Original capacity and budget promises derive the Boolean
next-fit packing price on its actual uniform-item list. No terminal factory,
reached-state width bound or grouping-cost oracle is supplied. Classification,
routes, descriptors/sampling/emission and physical storage remain separate. -/

namespace Blotto.BinaryPRGTerminalWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork
open BinaryPRGResourceHandoff BinaryGeneralResourceLattice

def terminalInput {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) : BinaryTerminalGrouping.Input n :=
  BinaryLottoResourceInput.groupingInput (resourceInput request rich) state

theorem terminal_canonical {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) :
    (terminalInput request rich state).Canonical :=
  BinaryLottoResourceInput.groupingInput_canonical _ (resource_canonical request rich) state

theorem terminal_admissible {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    BinaryTerminalPromises.Admissible (terminalInput request rich state) :=
  BinaryLottoResourceInput.reachedGrouping_admissible _ (resource_canonical request rich)
    (resource_admissible request rich) N bits state (resource_success request rich N bits state h)

theorem budget_lattice {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    OnRationalLattice request.source.normalizedInput.latticeDenominator
      (value (resourceInput request rich).budget) := by
  rw [(resource_refines request rich).1]
  cases rich
  · change request.source.normalizedInput.b.den ∣ request.source.normalizedInput.latticeDenominator
    exact dvd_mul_right _ _
  · simp [sourceSystem, RationalPRGInput.richNativeSystem, OnRationalLattice]

theorem budget_box {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    0 ≤ value (resourceInput request rich).budget ∧ value (resourceInput request rich).budget ≤ 1 := by
  rw [(resource_refines request rich).1]
  exact ⟨(sourceSystem request rich).B_pos.le, source_unit request rich⟩

theorem length_good {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    ∀ j, BinaryGreedyPackingWork.GoodTotal request.source.normalizedInput.latticeDenominator
      (resourceInput request rich).budget ((resourceInput request rich).length.read j) := by
  have hr := resource_refines request rich
  intro j
  refine ⟨(resource_canonical request rich).2.1 j, (resource_lattice_boxes request rich).1 j, ?_, ?_⟩
  · rw [hr.2.1 j]; exact ((sourceSystem request rich).length_pos j).le
  · rw [hr.2.1 j, hr.1]; exact (sourceSystem request rich).length_le j

theorem reached_invariant {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) :
    StateInvariant (resourceInput request rich).length request.source.normalizedInput.latticeDenominator state := by
  obtain ⟨hL, hR, _, hBox⟩ := resource_lattice_boxes request rich
  have hi := initial_invariant (resourceInput request rich).length (resourceInput request rich).resource
    (resource_canonical request rich).2.1 (resource_canonical request rich).2.2
    request.source.normalizedInput.latticeDenominator hR hBox
  have hs := resource_success request rich N bits state h
  exact run_completed_invariant (resource_canonical request rich).2.1
    request.source.normalizedInput.latticeDenominator hL _ hi N bits state hs

theorem terminal_length_width {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) (j : Fin n) :
    width ((terminalInput request rich state).length.read j) ≤
      1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator :=
  BinaryGreedyPackingWork.goodTotal_width _ request.source.normalizedInput.latticeDenominator_pos
    _ _ (budget_box request rich).2 (length_good request rich j)

theorem terminal_resource_width {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) (j : Fin n) :
    width ((terminalInput request rich state).resource.read j) ≤
      1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator :=
  state_wordWidth state _ request.source.normalizedInput.latticeDenominator_pos
    (fun j => ((resource_lattice_boxes request rich).2.2.1 j).2) (reached_invariant request rich N bits state h) j

def packingWork {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) :
    List (List (Fin n) × SignedWord) × ℕ :=
  BinaryGreedyPackingWork.pack (terminalInput request rich state).length.read
    (terminalInput request rich state).budget (BinaryTerminalGrouping.uniformItems (terminalInput request rich state))

theorem packing_state {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) :
    (packingWork request rich state).1 = BinaryTerminalGrouping.packed (terminalInput request rich state) :=
  BinaryGreedyPackingWork.pack_state _ _ _

theorem packing_boolean_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length) :
    (packingWork request rich state).2 ≤
      160000 * (n - 1) * (request.source.originalInputWordWidth + 2) ^ 3 := by
  have hp := BinaryGreedyPackingWork.pack_boolean_bound (terminalInput request rich state).length.read
    (terminalInput request rich state).budget request.source.normalizedInput.latticeDenominator
    request.source.normalizedInput.latticeDenominator_pos (terminal_canonical request rich state).1
    (budget_lattice request rich) (budget_box request rich) (length_good request rich)
    (BinaryTerminalGrouping.uniformItems (terminalInput request rich state))
  have hn : (BinaryTerminalGrouping.uniformItems (terminalInput request rich state)).length - 1 ≤ n - 1 := by
    have hl := List.length_filter_le (BinaryTerminalGrouping.uniform (terminalInput request rich state)) (List.finRange n)
    simp only [List.length_finRange] at hl
    exact Nat.sub_le_sub_right hl 1
  have hd := request.source.normalized_lattice_wordWidth_original
  have hw : 2 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator ≤
      2 * (request.source.originalInputWordWidth + 2) := by omega
  have hBound := hp.trans (Nat.mul_le_mul hn
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hw 3)))
  exact hBound.trans_eq (by ring)

end Blotto.BinaryPRGTerminalWork
