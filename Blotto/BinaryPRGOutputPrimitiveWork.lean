import Blotto.BinaryPRGCachedPrimitiveRun
import Blotto.RationalPRGOutputHeight
import Blotto.BinaryStoredRowFrameWork
import Blotto.BinaryFactoryHeight

/-! Native original-budget scaling and coordinate framing are priced from
original request words and precision on every bit path, including global
exhaustion. Final stored payload/serialized lengths are derived, not supplied.
Header production, metadata and physical execution/space remain separate. -/

namespace Blotto.BinaryPRGOutputPrimitiveWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryFactoryHeight
open BinaryPRGResourceWork BinaryPRGTerminalWork
open scoped BigOperators

noncomputable def normalizedHeight {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) : ℕ :=
  expressionHeightBudget (max (3 + request.source.originalInputWordWidth) (K + 2)) 75

noncomputable def outputHeight {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) : ℕ :=
  expressionHeightBudget (max (3 + request.source.originalInputWordWidth) (K + 2)) 76

theorem normalizedSample_canonical {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    ∀ j, CanonicalWord ((BinaryPRGCachedPrimitiveRun.sample request rich K bits).1.read j) := by
  rw [BinaryPRGCachedPrimitiveRun.sample_state,BinaryPRGResourceHandoff.sample_state]
  exact BinaryLottoSampler.sample_canonical _ _ _ K bits

theorem normalizedSample_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (value ((BinaryPRGCachedPrimitiveRun.sample request rich K bits).1.read j)) (normalizedHeight request K) := by
  rw [BinaryPRGCachedPrimitiveRun.sample_state,BinaryPRGResourceHandoff.sample_state]
  have hr := BinaryLottoSampler.sample_refines (resourceInput request rich) (sourceSystem request rich)
    (resource_canonical request rich) (resource_refines request rich) (resource_admissible request rich) K bits
  have he := congrFun hr j
  change value ((BinaryLottoSampler.sample (resourceInput request rich) (resource_canonical request rich)
    (resource_admissible request rich) K bits).read j) = _ at he
  rw [he]
  have hLattice : (sourceSystem request rich).OnLattice request.source.normalizedInput.latticeDenominator :=
    ⟨source_length_lattice request rich,source_initial_lattice request rich⟩
  have hs : 2 ≤ 3 + request.source.originalInputWordWidth := by omega
  have hBudget : RationalHeight (sourceSystem request rich).B (3 + request.source.originalInputWordWidth) := by
    cases rich
    · exact request.source.normalized_budget_height
    · exact (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  exact hLattice.paperSample request.source.normalizedInput.latticeDenominator_pos (source_unit request rich) _ hs hBudget
    (request.source.normalized_lattice_wordWidth_original.trans (by omega)) K bits j

def rescaleWithWork {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) : FixedArrayTable n SignedWord × ℕ :=
  let cells := FixedArrayTable.ofFn (fun j => applyWithWork .mul budget (row.read j))
  (FixedArrayTable.ofFn (fun j => (cells.read j).1),∑ j, (cells.read j).2)

theorem rescaleWithWork_state {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (rescaleWithWork budget row).1 = BinaryPRGOriginalSampler.rescale budget row := by
  unfold rescaleWithWork BinaryPRGOriginalSampler.rescale
  simp only [FixedArrayTable.read_ofFn,applyWithWork_state]

theorem rescaleWithWork_bound {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord)
    (hB : CanonicalWord budget) (hC : ∀ j, CanonicalWord (row.read j)) (s : ℕ)
    (hH : RationalHeight (value budget) s) (hRow : ∀ j, RationalHeight (value (row.read j)) s) :
    (rescaleWithWork budget row).2 ≤ n * opcodeBound s := by
  have hp := fun j => opcode_bound .mul budget (row.read j) hB (hC j) s hH (hRow j)
  unfold rescaleWithWork
  simp only [FixedArrayTable.read_ofFn]
  calc
    _ ≤ ∑ _j : Fin n, opcodeBound s := Finset.sum_le_sum (fun j _ => hp j)
    _ = n * opcodeBound s := by simp

theorem scale_height {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) :
    RationalHeight (value request.prepared.original.a) (normalizedHeight request K) := by
  exact request.source.scale_height.mono ((le_max_left _ _).trans (expressionHeightBudget_ge_input _ 75))

theorem requestScaling_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (rescaleWithWork request.prepared.original.a (BinaryPRGCachedPrimitiveRun.sample request rich K bits).1).2 ≤
      n * opcodeBound (normalizedHeight request K) :=
  rescaleWithWork_bound _ _ request.valid.2.1.1 (normalizedSample_canonical request rich K bits) _
    (scale_height request K) (normalizedSample_height request rich K bits)

theorem originalSample_canonical {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    ∀ j, CanonicalWord ((BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1.read j) := by
  rw [BinaryPRGCachedPrimitiveRun.originalSample_state]
  cases rich
  · exact BinaryPRGOriginalSampler.poorSample_canonical _ _ _ bits
  · exact BinaryPRGOriginalSampler.richSample_canonical _ _ _ bits

theorem originalSample_height {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) (j : Fin n) :
    RationalHeight (value ((BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1.read j)) (outputHeight request request.precision) := by
  rw [BinaryPRGCachedPrimitiveRun.originalSample_state]
  cases rich
  · have he := congrFun (BinaryPRGOriginalSampler.poorSample_refines request.prepared request.valid request.precision bits) j
    change value ((BinaryPRGOriginalSampler.poorSample request.prepared request.valid request.precision bits).read j) = request.source.poorSample request.precision bits j at he
    change RationalHeight (value ((BinaryPRGOriginalSampler.poorSample request.prepared request.valid request.precision bits).read j)) _
    rw [he]
    exact (request.source.sample_heights request.precision bits j).2
  · have he := congrFun (BinaryPRGOriginalSampler.richSample_refines request.prepared request.valid request.precision bits) j
    change value ((BinaryPRGOriginalSampler.richSample request.prepared request.valid request.precision bits).read j) = request.source.richSample request.precision bits j at he
    change RationalHeight (value ((BinaryPRGOriginalSampler.richSample request.prepared request.valid request.precision bits).read j)) _
    rw [he]
    exact (request.source.sample_heights request.precision bits j).1

noncomputable def outputWidth {n : ℕ} (request : BinaryPRGRequest.Request n) : ℕ :=
  1 + 2 * outputHeight request request.precision

theorem originalSample_width {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) (j : Fin n) :
    width ((BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1.read j) ≤ outputWidth request :=
  (originalSample_canonical request rich bits j).2.trans (rationalWordWidth_of_height (originalSample_height request rich bits j))

theorem storedSpines_bound (inputs : List SignedWord) (W : ℕ) (h : ∀ word ∈ inputs, width word ≤ W) :
    BinaryStoredRowFrameWork.storedSpines inputs ≤ 2 * inputs.length * W := by
  induction inputs with
  | nil => simp [BinaryStoredRowFrameWork.storedSpines]
  | cons word inputs ih =>
      have hw := h word (by simp)
      have hn : word.numerator.length ≤ W := by unfold width at hw; omega
      have hd : word.denominator.length ≤ W := by unfold width at hw; omega
      have ht := ih (fun item hi => h item (by simp [hi]))
      simp only [BinaryStoredRowFrameWork.storedSpines,List.length_cons]
      nlinarith

theorem row_length_bound {n : ℕ} (row : FixedArrayTable n SignedWord) (W : ℕ) (h : ∀ j, width (row.read j) ≤ W) :
    (BinaryStoredRowFrame.row row).length ≤ 2 * binaryWordWidth n + 1 + n * (4 * W + 3) := by
  have hs := storedSpines_bound (List.ofFn row.read) W (by intro word hw; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw; exact h j)
  simp only [List.length_ofFn] at hs
  rw [BinaryStoredRowFrameWork.row_length]
  nlinarith

theorem rowCoordinateVisits_bound {n : ℕ} (row : FixedArrayTable n SignedWord) (W : ℕ) (h : ∀ j, width (row.read j) ≤ W) :
    BinaryStoredRowFrameWork.rowCoordinateVisits row ≤ 4 * (2 * binaryWordWidth n + 1 + n * (4 * W + 3)) + 2 * n := by
  have hv := BinaryStoredRowFrameWork.rowCoordinateVisits_bound row
  have hl := row_length_bound row W h
  omega

theorem requestFrame_length_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    (BinaryStoredRowFrame.row (BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1).length ≤
      2 * binaryWordWidth n + 1 + n * (4 * outputWidth request + 3) :=
  row_length_bound _ _ (originalSample_width request rich bits)

theorem requestFrame_coordinateVisits_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n request.precision) → Bool) :
    BinaryStoredRowFrameWork.rowCoordinateVisits (BinaryPRGCachedPrimitiveRun.originalSample request rich bits).1 ≤
      4 * (2 * binaryWordWidth n + 1 + n * (4 * outputWidth request + 3)) + 2 * n :=
  rowCoordinateVisits_bound _ _ (originalSample_width request rich bits)

end Blotto.BinaryPRGOutputPrimitiveWork
