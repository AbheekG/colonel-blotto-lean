import Blotto.BinaryCachedTerminalWork
import Blotto.RationalExpressionWordWidth

/-! Actual reached resource data and cached group totals derive all small-group
input heights from the original request. The probability height comes from the
actual pivot division; no group/geometry/operand-height certificate is supplied
by the caller. Uniform and mixed continuations keep their original scopes. -/

namespace Blotto.BinaryCachedGroupInputHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryCachedTerminalPreparation BinaryPRGResourceWork BinaryPRGTerminalWork

noncomputable def inputHeight {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  4 * (request.source.originalInputWordWidth + 2)

theorem inputHeight_two {n : ℕ} (request : BinaryPRGRequest.Request n) : 2 ≤ inputHeight request := by
  unfold inputHeight
  omega

theorem unit_lattice_height {D : ℕ} (hD : 0 < D) (q : ℚ) (hL : OnRationalLattice D q)
    (hBox : 0 ≤ q ∧ q ≤ 1) : RationalHeight q (1 + 2 * binaryWordWidth D) :=
  (rationalHeight_of_wordWidth q).mono (rationalWordWidth_lattice_bound hD hL hBox)

theorem lattice_height_original {n : ℕ} (request : BinaryPRGRequest.Request n) :
    2 * (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) ≤ inputHeight request := by
  have hd := request.source.normalized_lattice_wordWidth_original
  unfold inputHeight
  omega

theorem budget_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) :
    RationalHeight (value (resourceInput request rich).budget) (inputHeight request) := by
  have h := unit_lattice_height request.source.normalizedInput.latticeDenominator_pos _
    (budget_lattice request rich) (budget_box request rich)
  exact h.mono (by have hd := lattice_height_original request; omega)

theorem length_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (j : Fin n) :
    RationalHeight (value ((resourceInput request rich).length.read j))
      (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) :=
  unit_lattice_height request.source.normalizedInput.latticeDenominator_pos _
    ((resource_lattice_boxes request rich).1 j) ((resource_lattice_boxes request rich).2.2.1 j)

theorem reached_resource_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) (j : Fin n) :
    RationalHeight (value (state.state.resource.read j))
      (1 + 2 * binaryWordWidth request.source.normalizedInput.latticeDenominator) := by
  have hs := reached_invariant request rich N bits state h
  have hLat := hs.1 j
  simp only [BinaryResourcePair.Certified.reference, RationalResourceArray.allocation_ofAllocation,
    BinaryResourceState.allocation] at hLat
  change OnRationalLattice request.source.normalizedInput.latticeDenominator (value (state.state.resource.read j)) at hLat
  have hBox := hs.2 j
  simp only [BinaryResourcePair.Certified.reference, RationalResourceArray.realAllocation,
    RationalResourceArray.allocation_ofAllocation, BinaryResourceState.allocation] at hBox
  have hBoxQ : 0 ≤ value (state.state.resource.read j) ∧
      value (state.state.resource.read j) ≤ value ((resourceInput request rich).length.read j) := by exact_mod_cast hBox
  exact unit_lattice_height request.source.normalizedInput.latticeDenominator_pos _ hLat
    ⟨hBoxQ.1, hBoxQ.2.trans (((resource_lattice_boxes request rich).2.2.1 j).2)⟩

theorem cached_total_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (g : Fin (prepare (terminalInput request rich state)).count) :
    RationalHeight (value ((prepare (terminalInput request rich state)).totals.read g)) (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  have hBox := BinaryCachedTerminalWork.Prepared.total_box cached hC hAd g
  have hLat := BinaryCachedTerminalWork.Prepared.total_lattice cached hC _
    (fun j => (resource_lattice_boxes request rich).1 j) g
  have hHeight := unit_lattice_height request.source.normalizedInput.latticeDenominator_pos _ hLat
    ⟨hBox.1.le, hBox.2.trans (budget_box request rich).2⟩
  change RationalHeight (value (cached.totals.read g)) _
  rw [cached.totals_eq, FixedArrayTable.read_ofFn]
  exact hHeight.mono (by have hd := lattice_height_original request; omega)

theorem cached_pivot_heights {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    RationalHeight (value (prepare (terminalInput request rich state)).ell) (inputHeight request) ∧
      RationalHeight (value (prepare (terminalInput request rich state)).probability) (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hL := length_height request rich selected
  have hR := reached_resource_height request rich N bits state h selected
  have hEll : cached.ell = (terminalInput request rich state).length.read selected := by
    rw [cached.ell_eq, hPivot]
    rfl
  have hProb : cached.probability = apply .div ((terminalInput request rich state).resource.read selected)
      ((terminalInput request rich state).length.read selected) := by
    rw [cached.probability_eq, hPivot]
    rfl
  change RationalHeight (value cached.ell) _ ∧ RationalHeight (value cached.probability) _
  constructor
  · rw [hEll]
    exact hL.mono (by have hd := lattice_height_original request; omega)
  · rw [hProb, apply_value .div _ _ (hC.2.2 selected).1 (hC.2.1 selected).1]
    exact (hR.div hL).mono (by have hw := lattice_height_original request; omega)

end Blotto.BinaryCachedGroupInputHeight
