import Blotto.GeneralPaperBlockerRowPrice

/-! Original-row prefix and retained-row append materialize references
once per entry in the paper indexed-array model. No dense row payload is
copied when appending the array of original-row references.
-/
namespace Blotto.GeneralPaperBasisArrayPrice
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow
open GeneralPaperBasisOriginalDirection GeneralPaperBasisPrefixSum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

def prefixRun {j d : ℕ} (index : ℕ → ℕ) (W : ℕ) (row : Dense d) (hj : j≤d) : Vector j × ℕ :=
  PaperIndexedArrayConstruction.run index W (fun i => (row.coefficients.read (embed hj i),4*W))

theorem prefix_data {j d : ℕ} (index : ℕ → ℕ) (W : ℕ) (row : Dense d) (hj : j≤d) :
    (prefixRun index W row hj).1=rowPrefix row hj := PaperIndexedArrayConstruction.run_data _ _ _

theorem prefix_work {j d : ℕ} (row : Dense d) (hj : j≤d) :
    (prefixRun (fun _ => 1) 1 row hj).2≤64*(j+1) := by
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fun i : Fin j => (row.coefficients.read (embed hj i),4*1))
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 j j
  change (prefixRun (fun _ => 1) 1 row hj).2=_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  omega

def appendRun {j d : ℕ} (index : ℕ → ℕ) (W : ℕ) (rows : Rows j d) (new : Dense d) : Rows (j+1) d × ℕ :=
  PaperIndexedArrayConstruction.run index W (fun i => (if h : i.val<j then rows.read ⟨i.val,h⟩ else new,8*W))

theorem append_data {j d : ℕ} (index : ℕ → ℕ) (W : ℕ) (rows : Rows j d) (new : Dense d) :
    (appendRun index W rows new).1=GeneralPaperBasisAppendRows.append rows new := PaperIndexedArrayConstruction.run_data _ _ _

theorem append_work {j d : ℕ} (rows : Rows j d) (new : Dense d) :
    (appendRun (fun _ => 1) 1 rows new).2≤64*(j+2) := by
  have hh := PaperIndexedArrayConstruction.run_work (fun _ => 1) 1 (fun i : Fin (j+1) =>
    (if h : i.val<j then rows.read ⟨i.val,h⟩ else new,8*1))
  have ho := GeneralPaperUnitArrayOverhead.overhead 1 (j+1) (j+1)
  change (appendRun (fun _ => 1) 1 rows new).2=_ at hh
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hh
  omega

def initialRun (index : ℕ → ℕ) (W d : ℕ) : GeneralPaperBasisState.State 0 d × ℕ :=
  let rows : Rows 0 d × ℕ := PaperIndexedArrayConstruction.run index W (fun i => (Fin.elim0 i,0))
  let adj : IntMatrix 0 × ℕ := PaperIndexedArrayConstruction.run index W (fun i => (Fin.elim0 i,0))
  (⟨rows.1,1,adj.1⟩,rows.2+adj.2+8*W)

theorem initial_data (index : ℕ → ℕ) (W d : ℕ) :
    (initialRun index W d).1=GeneralPaperBasisState.initial d := by
  simp only [initialRun,PaperIndexedArrayConstruction.run_data,GeneralPaperBasisState.initial,GeneralPaperBasisStoredCorrect.initial]

theorem initial_work (d : ℕ) : (initialRun (fun _ => 1) 1 d).2≤64 := by
  change PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 0 0+
    PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 0 0+8*1≤64
  norm_num [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.initialWork]

end Blotto.GeneralPaperBasisArrayPrice
