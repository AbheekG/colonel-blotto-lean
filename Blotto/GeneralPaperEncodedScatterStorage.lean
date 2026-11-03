import Blotto.GeneralPaperSelectorResidentStorage

/-! Intermediate scatter tables and one present/absent candidate include
exact resources, typed predecessor payloads, slots and descriptors. Safe
heights are erased invariants; no table or candidate census executes. -/
namespace Blotto.GeneralPaperEncodedScatterStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
open GeneralPaperOrderedTableHeight GeneralPaperEncodedFixedVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def tableFootprint {Witness : Type*} {J : ℕ} (W : ℕ) (encode : Witness → ℕ) (table : Table Tag Witness J) : ℕ :=
  GeneralPaperRetainedDPStorage.tableTagBits table+GeneralPaperEncodedDPStorage.tableMetadata W encode table

def tableProfile (W J P s : ℕ) : ℕ := J*(1+2*s+2)+64*W+J*(9*W+P+1)

theorem table_bound {Witness : Type*} {J : ℕ} (W P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (table : Table Tag Witness J) (ht : Safe s table) :
    tableFootprint W encode table≤tableProfile W J P s := by
  have hh : Safe (expressionHeightBudget s 0) table := by simpa only [expressionHeightBudget_zero] using ht
  have htag := GeneralPaperRetainedDPStorage.table_tag_bits s 0 table hh
  rw [GeneralPaperTagHeight.word_zero] at htag
  have hmeta := GeneralPaperEncodedDPStorage.table_metadata_bound W P encode he table
  exact (Nat.add_le_add htag hmeta).trans_eq (by unfold tableProfile; ring)

def entryFootprint {Witness : Type*} {J : ℕ} (W : ℕ) (encode : Witness → ℕ) : Option (Entry Tag Witness J) → ℕ
  | none => 32*W
  | some e => rationalWordWidth e.selection.cost.threshold+1+encode e.selection.predecessor+rankBits e.label+64*W

def entryProfile (W J P s : ℕ) : ℕ := 1+2*s+P+rankWord J+96*W+2

theorem entry_bound {Witness : Type*} {J : ℕ} (W P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (entry : Option (Entry Tag Witness J)) (hs : OptionalSafe s entry) :
    entryFootprint W encode entry≤entryProfile W J P s := by
  cases entry with
  | none => simp only [entryFootprint,entryProfile]; omega
  | some e =>
    have hr := rationalWordWidth_of_height (hs e rfl)
    have hp := he e.selection.predecessor
    have hi := rank_bound e.label
    simp only [entryFootprint,entryProfile]
    omega

def applyWindow {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ) (encode : Witness → ℕ)
    (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J)) : ℕ :=
  tableFootprint W encode table+entryFootprint W encode entry+
    tableFootprint W encode (GeneralPaperOrderedScatterExecution.applyEntry price W A table entry).1+128*W

def applyProfile (W J P s : ℕ) : ℕ := 2*tableProfile W J P s+entryProfile W J P s+128*W

theorem apply_bound {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) (table : Table Tag Witness J) (entry : Option (Entry Tag Witness J))
    (ht : Safe s table) (hs : OptionalSafe s entry) :
    applyWindow price W A encode table entry≤applyProfile W J P s := by
  have h0 := table_bound W P s encode he table ht
  have h1 := entry_bound W P s encode he entry hs
  have h2 := table_bound W P s encode he _ (GeneralPaperOrderedScatterPrice.apply_safe price W A s table entry ht hs)
  unfold applyWindow applyProfile
  omega

theorem empty_bound {Witness : Type*} (W J P s : ℕ) (encode : Witness → ℕ)
    (he : ∀ witness,encode witness≤P) :
    tableFootprint W encode (empty Witness J)≤tableProfile W J P s :=
  table_bound W P s encode he _ (empty_safe Witness J s)

end Blotto.GeneralPaperEncodedScatterStorage
