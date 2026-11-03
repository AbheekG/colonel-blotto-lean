import Blotto.GeneralPaperTailCataloguePartition

/-! Actual nonenumerated code catalogues prepared once from the signed
summary positions. The common slot count is summary-size+2: zero, one slot
per actual cell, and zero padding. Lookup and padding profiles are retained
separately; full partition/sorting/source bit and space prices remain joins.
-/
namespace Blotto.GeneralPaperCachedCatalogue
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeMinimumScan
open GeneralPaperEpochCellInstructions
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure Prepared (cap : ℕ) where
  entries : FixedArrayTable (cap+1) Entry
  lookupWork : ℕ
  paddingWork : ℕ

def prepare {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) : Prepared (n+1) :=
  let partition := GeneralPaperTailCataloguePartition.prepare (8*a.C) summary
  let raw := GeneralPaperCellCatalogue.build a response partition.intervals
  let padded := GeneralPaperCatalogueSlots.build (cap:=n+1) a raw.1
  ⟨padded.1,raw.2,padded.2⟩

theorem read_zero {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    (prepare a response summary).entries.read 0=GeneralPaperCatalogueSlots.zero a :=
  GeneralPaperCatalogueSlots.read_zero a _

theorem decoded {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    (decode a response ((prepare a response summary).entries.read i).cost).choice=
      some ((prepare a response summary).entries.read i).predecessor := by
  apply GeneralPaperCatalogueSlots.decoded
  intro r entry hSome
  exact (GeneralPaperCellCatalogue.sound a response _ r entry hSome).2

theorem valid {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    Valid a response ((prepare a response summary).entries.read i).cost :=
  GeneralPaperCodeDecodeSound.decode_valid a response _ _ (decoded a response summary i)

theorem code_bound {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((prepare a response summary).entries.read i).cost<8*a.C :=
  valid_in_alphabet a response _ (valid a response summary i)

theorem denominator {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((prepare a response summary).entries.read i).predecessor.threshold.den≤a.C :=
  (GeneralPaperCodeDecodeSound.decode_sound a response _ _ (decoded a response summary i)).2

theorem candidate_closed {n : ℕ} (a : Alphabet) (summary : FixedArrayTable n ℕ) (i : Fin (n+2)) :
    ((prepare a false summary).entries.read i).predecessor.opened=false :=
  GeneralPaperCodeDecodeSound.candidate_closed a _ _ (decoded a false summary i)

theorem zero_tag {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    ((prepare a response summary).entries.read 0).predecessor.tag=0 := by
  rw [read_zero]
  exact GeneralPaperCatalogueSlots.zero_tag a

theorem covers_valid {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ)
    (code : ℕ) (choice : Choice) (hDecode : (decode a response code).choice=some choice) :
    ∃ i : Fin (n+2), ∃ r : Fin (GeneralPaperTailCataloguePartition.prepare (8*a.C) summary).count,
      Contains (GeneralPaperTailCataloguePartition.prepare (8*a.C) summary).intervals r code ∧
      Contains (GeneralPaperTailCataloguePartition.prepare (8*a.C) summary).intervals r ((prepare a response summary).entries.read i).cost ∧
      ((prepare a response summary).entries.read i).predecessor.tag≤choice.tag := by
  have hCode := valid_in_alphabet a response code (GeneralPaperCodeDecodeSound.decode_valid a response code choice hDecode)
  obtain ⟨r,hCell⟩ := GeneralPaperTailCataloguePartition.covers (8*a.C) summary code hCode
  obtain ⟨entry,hRaw,hEntry,hTag⟩ := GeneralPaperCellCatalogue.covers_valid a response
    (GeneralPaperTailCataloguePartition.prepare (8*a.C) summary).intervals r code choice hCell hDecode
  have hCount := GeneralPaperTailCataloguePartition.count_bound (8*a.C) summary
  let i : Fin (n+2) := ⟨r.val+1,by have := r.isLt; omega⟩
  have hRead : (prepare a response summary).entries.read i=entry :=
    GeneralPaperCatalogueSlots.read_cell a _ hCount r entry hRaw
  exact ⟨i,r,hCell,by rw [hRead]; exact hEntry,by rw [hRead]; exact hTag⟩

theorem preserves_objective (a : Alphabet) (response : Bool) (k : ℕ) (summary : Summary k) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ r, summary.read r<2*(8*a.C))
    (code : ℕ) (choice : Choice) (hDecode : (decode a response code).choice=some choice) :
    ∃ i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2),
      ((prepare a response summary).entries.read i).predecessor.tag≤choice.tag ∧
      GeneralPaperSignedTailProperties.signedValue k (8*a.C) summary preparedPrefix ((prepare a response summary).entries.read i).cost=
        GeneralPaperSignedTailProperties.signedValue k (8*a.C) summary preparedPrefix code := by
  obtain ⟨i,r,hCode,hEntry,hTag⟩ := covers_valid a response summary code choice hDecode
  exact ⟨i,hTag,GeneralPaperTailCataloguePartition.signed_value_constant k (8*a.C) summary preparedPrefix
    hMono hCodes r _ code hEntry hCode⟩

theorem lookup_work {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    (prepare a response summary).lookupWork≤(n+1)*(934*a.lambda+2772)+18 := by
  have he := GeneralPaperCellCatalogue.build_work a response (GeneralPaperTailCataloguePartition.prepare (8*a.C) summary).intervals
  have hn := GeneralPaperTailCataloguePartition.count_bound (8*a.C) summary
  exact he.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 18)

theorem padding_work {n : ℕ} (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    (prepare a response summary).paddingWork=62*(n+2)+18 :=
  GeneralPaperCatalogueSlots.build_work a _

end Blotto.GeneralPaperCachedCatalogue
