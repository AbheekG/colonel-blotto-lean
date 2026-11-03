import Blotto.BinaryPRGHeapCertifiedPrefixLifetime
import Blotto.BinaryCachedThreeDescriptorWork
import Blotto.BinaryCachedRouteHeight

/-! Source promises and field heights for the cache actually returned by the
physical prefix. All reference preparation occurs in erased proofs. -/
namespace Blotto.BinaryPRGHeapCertifiedPrefixProperties
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryPRGHeapCertifiedPrefixLifetime BinaryTerminalCacheCertificate BinaryCachedThreeDescriptorWork
open BinaryCachedGroupInputHeight
set_option maxHeartbeats 2000000

theorem reached {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : CachedResult request rich) (h : (runWithTrace store request rich).1.1 = some result) :
    (resourceWork request rich store.cap.value (BinaryWordIndexCoinController.reader store)).1.1 = some result.1 ∧
      result.2 = zeroWork (BinaryCachedTerminalPreparation.prepare (terminalInput request rich result.1)) := by
  rw [runWithTrace_reference] at h
  unfold reference at h
  dsimp only at h
  obtain ⟨state,hState,hResult⟩ := Option.map_eq_some_iff.mp h
  cases hResult
  have hOld := congrArg Prod.fst (BinaryPRGWordControllerResource.requestRun_state store request rich)
  exact ⟨hOld.symm.trans hState,rfl⟩

theorem cursor_bound {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool) :
    (runWithTrace store request rich).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_reference]
  change (BinaryPRGWordControllerResource.requestRun store request rich).2.value ≤ store.cap.value
  exact (BinaryPRGWordControllerResource.run_position store (resourceInput request rich).length
    (resource_canonical request rich).2.1 (BinaryResourcePair.initial _ _
      (resource_canonical request rich).2.1 (resource_canonical request rich).2.2)
    (BinaryWordIndexCoinController.zeroIndex store)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2

theorem admissible {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : CachedResult request rich) (h : (runWithTrace store request rich).1.1 = some result) :
    BinaryTerminalPromises.Admissible (terminalInput request rich result.1) :=
  terminal_admissible request rich store.cap.value (BinaryWordIndexCoinController.reader store) result.1 (reached store request rich result h).1

theorem uniform_height {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : CachedResult request rich) (h : (runWithTrace store request rich).1.1 = some result) :
    UniformHeights result.2.uniform (inputHeight request) := by
  rw [(reached store request rich result h).2]
  exact cached_uniform_heights request rich store.cap.value (BinaryWordIndexCoinController.reader store) result.1 (reached store request rich result h).1

theorem mixed_height {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : CachedResult request rich) (h : (runWithTrace store request rich).1.1 = some result)
    (selected : Fin n) (hPivot : result.2.pivot = some selected) :
    MixedHeights result.2.mixed (inputHeight request) := by
  have hr := reached store request rich result h
  rw [hr.2] at hPivot ⊢
  exact cached_mixed_heights request rich store.cap.value (BinaryWordIndexCoinController.reader store) result.1 hr.1 selected hPivot

theorem route_height {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (result : CachedResult request rich) (h : (runWithTrace store request rich).1.1 = some result) (j : Fin n) :
    RationalHeight (value (result.2.routes.read j).2) (expressionHeightBudget (inputHeight request) 1) := by
  have hr := reached store request rich result h
  rw [hr.2]
  exact BinaryCachedRouteHeight.reached_route_height request rich store.cap.value (BinaryWordIndexCoinController.reader store) result.1 hr.1 j

end Blotto.BinaryPRGHeapCertifiedPrefixProperties
