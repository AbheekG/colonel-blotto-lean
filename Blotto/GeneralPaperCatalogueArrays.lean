import Blotto.GeneralPaperCachedCatalogue

/-! Materialize common-width native code/threshold/open arrays from the
actual per-field catalogues. Projection equalities are erased metadata;
predecessor entries and all three numerical arrays are retained once.
No supplied validity, denominator, zero-entry or closure oracle is used.
-/
namespace Blotto.GeneralPaperCatalogueArrays
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeMinimumScan
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Arrays (m K : ℕ) where
  entries : FixedArrayTable m (FixedArrayTable K Entry)
  codes : FixedArrayTable m (FixedArrayTable K ℕ)
  thresholds : FixedArrayTable m (FixedArrayTable K Farey.Fraction)
  opened : FixedArrayTable m (FixedArrayTable K Bool)
  codes_spec : codes=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).cost))
  thresholds_spec : thresholds=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).predecessor.threshold))
  opened_spec : opened=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).predecessor.opened))

def project {m K : ℕ} (entries : FixedArrayTable m (FixedArrayTable K Entry)) : Arrays m K :=
  ⟨entries,FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).cost)),
    FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).predecessor.threshold)),
    FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun i => ((entries.read j).read i).predecessor.opened)),rfl,rfl,rfl⟩

def prepare {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) :
    Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2) :=
  let catalogues := FixedArrayTable.ofFn (fun j => GeneralPaperCachedCatalogue.prepare a response (summaries.read j))
  project (FixedArrayTable.ofFn (fun j => (catalogues.read j).entries))

def tags {m K : ℕ} (data : Arrays m K) : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag) :=
  GeneralPaperNativeRowBudget.tags data.thresholds data.opened

theorem codes_read {m K : ℕ} (data : Arrays m K) (j : Fin m) (i : Fin K) :
    (data.codes.read j).read i=((data.entries.read j).read i).cost := by
  rw [data.codes_spec]
  simp only [FixedArrayTable.read_ofFn]

theorem thresholds_read {m K : ℕ} (data : Arrays m K) (j : Fin m) (i : Fin K) :
    (data.thresholds.read j).read i=((data.entries.read j).read i).predecessor.threshold := by
  rw [data.thresholds_spec]
  simp only [FixedArrayTable.read_ofFn]

theorem opened_read {m K : ℕ} (data : Arrays m K) (j : Fin m) (i : Fin K) :
    (data.opened.read j).read i=((data.entries.read j).read i).predecessor.opened := by
  rw [data.opened_spec]
  simp only [FixedArrayTable.read_ofFn]

theorem tags_read {m K : ℕ} (data : Arrays m K) (j : Fin m) (i : Fin K) :
    ((tags data).read j).read i=((data.entries.read j).read i).predecessor.tag := by
  simp only [tags,GeneralPaperNativeRowBudget.tags,FixedArrayTable.read_ofFn,thresholds_read,opened_read,Choice.tag]

theorem entries_read {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) (j : Fin m) :
    (prepare a response k summaries).entries.read j=(GeneralPaperCachedCatalogue.prepare a response (summaries.read j)).entries := by
  simp only [prepare,project,FixedArrayTable.read_ofFn]

theorem entry_zero {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) (j : Fin m) :
    (((prepare a response k summaries).entries.read j).read 0)=GeneralPaperCatalogueSlots.zero a := by
  rw [entries_read,GeneralPaperCachedCatalogue.read_zero]

theorem decoded_entry {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    (decode a response (((prepare a response k summaries).codes.read j).read i)).choice=
      some (((prepare a response k summaries).entries.read j).read i).predecessor := by
  rw [codes_read,entries_read]
  exact GeneralPaperCachedCatalogue.decoded a response (summaries.read j) i

theorem code_bound {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    ((prepare a response k summaries).codes.read j).read i<8*a.C := by
  rw [codes_read,entries_read]
  exact GeneralPaperCachedCatalogue.code_bound a response (summaries.read j) i

theorem denominator {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    (((prepare a response k summaries).thresholds.read j).read i).den≤a.C := by
  rw [thresholds_read,entries_read]
  exact GeneralPaperCachedCatalogue.denominator a response (summaries.read j) i

theorem candidate_closed {m : ℕ} (a : Alphabet) (k : ℕ) (summaries : FixedArrayTable m (Summary k))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    ((prepare a false k summaries).opened.read j).read i=false := by
  rw [opened_read,entries_read]
  exact GeneralPaperCachedCatalogue.candidate_closed a (summaries.read j) i

theorem zero_code {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) (j : Fin m) :
    ((prepare a response k summaries).codes.read j).read 0=0 := by
  rw [codes_read,entry_zero]
  rfl

theorem zero_tag {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ) (summaries : FixedArrayTable m (Summary k)) (j : Fin m) :
    ((tags (prepare a response k summaries)).read j).read 0=0 := by
  rw [tags_read,entry_zero]
  exact GeneralPaperCatalogueSlots.zero_tag a

end Blotto.GeneralPaperCatalogueArrays
