import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapFixedLifetime

/-! Original request fields and supplied precision bound every actual returned
normalized word, including global exhaustion, without a reached-row oracle. -/
namespace Blotto.BinaryPRGHeapFixedProperties
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork
open BinaryPRGOutputPrimitiveWork
set_option maxHeartbeats 2000000

theorem row_height {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (j : Fin n) :
    RationalHeight (value ((BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar).1.1.read j))
      (normalizedHeight request K) := by
  rw [BinaryPRGHeapFixedLifetime.runWithTrace_state,BinaryPRGCachedPrimitiveRun.fixedSample_state,
    BinaryPRGResourceHandoff.fixedSample_state]
  have hr := BinaryLottoSampler.fixedSample_refines (resourceInput request rich) (sourceSystem request rich)
    (resource_canonical request rich) (resource_refines request rich) (resource_admissible request rich)
    K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)
  have he := congrFun hr j
  change value ((BinaryLottoSampler.fixedSample (resourceInput request rich) (resource_canonical request rich)
    (resource_admissible request rich) K store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)).read j) = _ at he
  rw [he]
  have hLattice : (sourceSystem request rich).OnLattice request.source.normalizedInput.latticeDenominator :=
    ⟨source_length_lattice request rich,source_initial_lattice request rich⟩
  have hs : 2 ≤ 3+request.source.originalInputWordWidth := by omega
  have hBudget : RationalHeight (sourceSystem request rich).B (3+request.source.originalInputWordWidth) := by
    cases rich
    · exact request.source.normalized_budget_height
    · exact (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  exact hLattice.paperFixedSample request.source.normalizedInput.latticeDenominator_pos (source_unit request rich) _ hs hBudget
    (request.source.normalized_lattice_wordWidth_original.trans (by omega)) K store.cap.value outer scalar
    (BinaryWordIndexCoinController.reader store) j

noncomputable def wordWidth {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) : ℕ :=
  1+2*normalizedHeight request K

theorem row_width {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (j : Fin n) :
    width ((BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar).1.1.read j) ≤ wordWidth request K :=
  (BinaryPRGHeapFixedLifetime.runWithTrace_canonical store request rich K outer scalar j).2.trans
    (rationalWordWidth_of_height (row_height store request rich K outer scalar j))

theorem scale_width {n : ℕ} (request : BinaryPRGRequest.Request n) (K : ℕ) :
    width request.prepared.original.a ≤ wordWidth request K :=
  request.valid.2.1.1.2.trans (rationalWordWidth_of_height (scale_height request K))

end Blotto.BinaryPRGHeapFixedProperties
