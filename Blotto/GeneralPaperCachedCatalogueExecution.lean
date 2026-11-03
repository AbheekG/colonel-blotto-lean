import Blotto.GeneralPaperCatalogueSlotsPrice

/-! One partition, one optional-entry fill and one padded catalogue fill.
Code-limit/slot-count arithmetic and the retained native work fields are
included; no decoder, partition or epoch is replayed for calibration.
-/
namespace Blotto.GeneralPaperCachedCatalogueExecution
open GeneralPaperCodeAlphabet
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def reference (n : ℕ) (a : Alphabet) (response : Bool) (part : GeneralPaperPreparedPartition.Prepared) :
    GeneralPaperCachedCatalogue.Prepared (n+1) :=
  let raw := GeneralPaperCellCatalogue.build a response part.intervals
  let padded := GeneralPaperCatalogueSlots.build (cap:=n+1) a raw.1
  ⟨padded.1,raw.2,padded.2⟩

def finish (n : ℕ) (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (part : GeneralPaperPreparedPartition.Prepared) :
    GeneralPaperCachedCatalogue.Prepared (n+1) × ℕ :=
  let raw := GeneralPaperCellCatalogueExecution.run bits index model W a response part.intervals
  let padded := GeneralPaperCatalogueSlotsExecution.run (cap:=n+1) bits index model W a raw.1.1
  (⟨padded.1.1,raw.1.2,padded.1.2⟩,raw.2+padded.2+128*W)

def header (price : ℕ → ℕ) (n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 8 a.C+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) n 1

def run {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) : GeneralPaperCachedCatalogue.Prepared (n+1) × ℕ :=
  let part := GeneralPaperCataloguePartitionPrice.run bits index (primitive bits model) W (8*a.C) summary
  let ready := finish n bits index model W a response part.1
  (ready.1,part.2+ready.2+header (primitive bits model) n a+128*W)

theorem finish_data (n : ℕ) (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (part : GeneralPaperPreparedPartition.Prepared) :
    (finish n bits index model W a response part).1=reference n a response part := by
  unfold finish reference
  dsimp only
  rw [GeneralPaperCatalogueSlotsExecution.data,GeneralPaperCellCatalogueData.data]

theorem data {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    (run bits index model W a response summary).1=GeneralPaperCachedCatalogue.prepare a response summary := by
  change (finish n bits index model W a response
    (GeneralPaperCataloguePartitionPrice.run bits index (primitive bits model) W (8*a.C) summary).1).1=_
  rw [finish_data]
  exact congrArg (reference n a response) (GeneralPaperCataloguePartitionPrice.data bits index (primitive bits model) W (8*a.C) summary)

theorem same_data {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) :
    (run true (fun w => w) model W a response summary).1=(run false (fun _ => 1) model 1 a response summary).1 := by
  rw [data,data]

theorem zero_slot {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    (run bits index model W a response summary).1.entries.read 0=GeneralPaperCatalogueSlots.zero a := by
  rw [data]
  exact GeneralPaperCachedCatalogue.read_zero a response summary

theorem decoded {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    (GeneralPaperCodeDecode.decode a response ((run bits index model W a response summary).1.entries.read i).cost).choice=
      some ((run bits index model W a response summary).1.entries.read i).predecessor := by
  rw [data]
  exact GeneralPaperCachedCatalogue.decoded a response summary i

theorem code_bound {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((run bits index model W a response summary).1.entries.read i).cost<8*a.C := by
  rw [data]
  exact GeneralPaperCachedCatalogue.code_bound a response summary i

theorem denominator {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((run bits index model W a response summary).1.entries.read i).predecessor.threshold.den≤a.C := by
  rw [data]
  exact GeneralPaperCachedCatalogue.denominator a response summary i

theorem candidate_closed {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((run bits index model W a false summary).1.entries.read i).predecessor.opened=false := by
  rw [data]
  exact GeneralPaperCachedCatalogue.candidate_closed a summary i

theorem preserves_objective (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (k : ℕ) (summary : GeneralPaperUnsignedCellConstancy.Summary k)
    (preparedPrefix : GeneralPaperUnsignedCellConstancy.Prefix k) (hMono : Monotone summary.read)
    (hCodes : ∀ r,summary.read r<2*(8*a.C)) (code : ℕ) (choice : Choice)
    (hDecode : (GeneralPaperCodeDecode.decode a response code).choice=some choice) :
    ∃ i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2),
      ((run bits index model W a response summary).1.entries.read i).predecessor.tag≤choice.tag ∧
      GeneralPaperSignedTailProperties.signedValue k (8*a.C) summary preparedPrefix
        ((run bits index model W a response summary).1.entries.read i).cost=
        GeneralPaperSignedTailProperties.signedValue k (8*a.C) summary preparedPrefix code := by
  rw [data]
  exact GeneralPaperCachedCatalogue.preserves_objective a response k summary preparedPrefix hMono hCodes code choice hDecode

end Blotto.GeneralPaperCachedCatalogueExecution
