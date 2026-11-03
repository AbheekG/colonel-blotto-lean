import Blotto.GeneralPaperReferenceHeaderSlotArea

/-! The actual outer measured plan contains exactly the address-control
header, its natural payload and the final selected record. Field extraction
reads these three actual returned regions; it computes no footprint oracle. -/
namespace Blotto.GeneralPaperEqualOuterFieldLayout
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Fields (A : ℕ) where
  control : Region A
  value : Region A
  record : Region A

def extract (S A : ℕ) (regions : List (Region A)) : Option (Fields A) × ℕ :=
  match regions with
  | [control,value,record] =>
    (some ⟨control,value,record⟩,
      GeneralPaperEncodedScalarStorage.natBits control.start + GeneralPaperEncodedScalarStorage.natBits control.length +
      GeneralPaperEncodedScalarStorage.natBits value.start + GeneralPaperEncodedScalarStorage.natBits value.length +
      GeneralPaperEncodedScalarStorage.natBits record.start + GeneralPaperEncodedScalarStorage.natBits record.length +
      6 * A + 256 * (S + A + 1))
  | _ => (none,256 * (S + A + 1))

theorem plan_data (model : RationalCostModel) (S A : ℕ) :
    (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes = [A * 33,GeneralPaperEncodedScalarStorage.natBits A,A * 64] := by
  simp only [GeneralPaperEqualMeasuredSelectedPlan.header,join_data,GeneralPaperMeasuredListBlockPlan.data,
    List.length_cons,List.length_nil,natural_data,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,references_data,Nat.mul_zero,Nat.zero_add,List.singleton_append,List.append_nil]
  norm_num

def canonical (A start : ℕ) : Fields A :=
  ⟨⟨start,A * 33,FixedBinaryWord.ofNat A start⟩,
    ⟨start + A * 33,GeneralPaperEncodedScalarStorage.natBits A,FixedBinaryWord.ofNat A (start + A * 33)⟩,
    ⟨start + A * 33 + GeneralPaperEncodedScalarStorage.natBits A,A * 64,
      FixedBinaryWord.ofNat A (start + A * 33 + GeneralPaperEncodedScalarStorage.natBits A)⟩⟩

theorem regions (model : RationalCostModel) (S A start : ℕ) :
    (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1 =
      [(canonical A start).control,(canonical A start).value,(canonical A start).record] := by
  dsimp only [GeneralPaperMeasuredBlockLayout.run]
  rw [plan_data]
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,canonical]

theorem extracted (model : RationalCostModel) (S A start : ℕ) :
    (extract S A (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1).1 = some (canonical A start) := by
  rw [regions]
  rfl

def headers {A : ℕ} (fields : Fields A) (branch tag : FixedBinaryWord A) : List (Header A) :=
  [⟨fields.control,32,[fields.value.reference]⟩,
    ⟨fields.record,0,[branch,fields.control.reference,tag]⟩]

theorem selected_owners (model : RationalCostModel) (S A start : ℕ) (branch tag : FixedBinaryWord A) :
    ((headers (canonical A start) branch tag).map Header.region).Sublist
      (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1 := by
  rw [regions]
  change [(canonical A start).control,(canonical A start).record].Sublist
    [(canonical A start).control,(canonical A start).value,(canonical A start).record]
  exact (List.Sublist.cons (canonical A start).value (List.Sublist.refl [(canonical A start).record])).cons_cons _

theorem valid (A start : ℕ) (branch tag : FixedBinaryWord A) :
    ∀ header ∈ headers (canonical A start) branch tag,Valid header := by
  intro header hh
  simp only [headers,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl | rfl
  · change A * (32 + [((canonical A start).value.reference)].length) ≤ A * 33
    simp only [List.length_cons,List.length_nil]; omega
  · change A * (0 + [branch,(canonical A start).control.reference,tag].length) ≤ A * 64
    simp only [List.length_cons,List.length_nil]
    omega

theorem value_size (A start : ℕ) : (canonical A start).value.length = GeneralPaperEncodedScalarStorage.natBits A := rfl

end Blotto.GeneralPaperEqualOuterFieldLayout
