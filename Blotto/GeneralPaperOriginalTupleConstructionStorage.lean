import Blotto.GeneralPaperSourceEndpointReturnReachedRates

/-! Literal original/recovered tuple-row flatMap construction. Current
segments, append copies, output terms, finite iterator, reference/anchor
guards and native wrapper prices are counted. Reference callbacks are
conservatively retained in full; no tuple enumeration or metadata pass runs. -/
namespace Blotto.GeneralPaperOriginalTupleConstructionStorage
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStaticRayRows
open GeneralPaperStaticRowResidualStorage GeneralPaperStaticRowConstructionStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

theorem terms_length {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) :
    (GeneralPaperBlockerRowPrice.tupleRun W labels).1.length≤m := by
  rw [GeneralPaperBlockerRowPrice.tuple_data]
  exact rawRow_sum_length (fun _ => 0) labels 0

theorem terms_unit {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) :
    ∀ t∈(GeneralPaperBlockerRowPrice.tupleRun W labels).1,t.2.natAbs≤1 := by
  intro t ht
  change t∈(GeneralPaperPricedListStream.flatMap W
    (fun j => (refTerms (tupleReference j (labels j)),16*W)) (List.finRange m)).1 at ht
  rw [GeneralPaperPricedListStream.flatMap_data] at ht
  obtain ⟨j,_,ht⟩ := List.mem_flatMap.mp ht
  exact reference_unit _ t ht

def controlCap (W m K : ℕ) : ℕ := m+K+1+3*(64*(m+1)*W)+16*(m+1)*W

def window {m K : ℕ} (W copied : ℕ) (labels : Fin m → Fin K) : ℕ :=
  let terms := GeneralPaperPricedListStream.flatMap W (fun j => (refTerms (tupleReference j (labels j)),16*W)) (List.finRange m)
  let result := GeneralPaperBlockerRowPrice.tupleRun W labels
  GeneralPaperPricedPayloadStreamStorage.flatWindow W copied (termFoot W)
    (fun j => (refTerms (tupleReference j (labels j)),16*W)) (fun _ => 0) none (List.finRange m)+
    budgetFrames W labels+GeneralPaperFinRangeStorage.window W m copied+
    fields W [m,K,terms.2,result.2,16*W,16*(m+1)*W]+192*W

def profile (W m K : ℕ) : ℕ :=
  GeneralPaperPricedPayloadStreamStorage.flatProfile W (termProfile W m K) 1 (16*W) m 0+
    budgetFrameProfile W m K+GeneralPaperFinRangeStorage.profile W m+
      6*(natBits (controlCap W m K)+W)+224*W

theorem bounded {m K : ℕ} (W copied : ℕ) (labels : Fin m → Fin K) : window W copied labels≤profile W m K := by
  let terms := GeneralPaperPricedListStream.flatMap W (fun j => (refTerms (tupleReference j (labels j)),16*W)) (List.finRange m)
  let result := GeneralPaperBlockerRowPrice.tupleRun W labels
  have hFlat := GeneralPaperPricedPayloadStreamStorage.flat_bounded W (termProfile W m K) 1 (16*W) m 0 copied
    (termFoot W) (fun j => (refTerms (tupleReference j (labels j)),16*W)) (fun _ => 0) none (List.finRange m)
    (by simp only [List.length_finRange,le_refl]) (fun j _ => reference_length _)
    (fun _ _ => le_rfl) (fun j _ t ht => term_bound W t (reference_unit _ t ht))
    (fun _ _ => le_rfl) (by intro a ha; cases ha)
  have hFrames := budget_frames W labels
  have hIterator := GeneralPaperFinRangeStorage.bounded W m copied
  have hWork := GeneralPaperBlockerRowPrice.tuple_work W labels
  change result.2≤64*(m+1)*W at hWork
  have hShape : result.2=terms.2+16*(m+1)*W := rfl
  have hPay : 16*W≤16*(m+1)*W := by nlinarith only [Nat.zero_le (m*W)]
  have hf := fields_bound W (natBits (controlCap W m K)) [m,K,terms.2,result.2,16*W,16*(m+1)*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold controlCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (controlCap W m K)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [terms,result] at hf
  omega

end Blotto.GeneralPaperOriginalTupleConstructionStorage
