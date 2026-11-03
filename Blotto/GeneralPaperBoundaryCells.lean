import Blotto.GeneralPaperRankedEpochError

/-! Native cells from adjacent ordered boundaries. Coverage, disjointness
and threshold constancy are proved, including repeated boundary values.
The following preparation module supplies the actual ordered boundaries.
-/
namespace Blotto.GeneralPaperBoundaryCells
open scoped Classical
open GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

def cells {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) : Cells n :=
  FixedArrayTable.ofFn (fun r => (boundary.read r.castSucc,boundary.read r.succ))

theorem read_cells {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) (r : Fin n) :
    (cells boundary).read r=(boundary.read r.castSucc,boundary.read r.succ) := FixedArrayTable.read_ofFn _ _

theorem disjoint {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) (hMono : Monotone boundary.read) :
    GeneralPaperEpochCellInstructions.Disjoint (cells boundary) := by
  intro r s i hr hs
  simp only [Contains,read_cells] at hr hs
  apply Fin.ext
  by_contra hNe
  rcases Nat.lt_or_gt_of_ne hNe with hRS|hSR
  · have he := hMono (show r.succ≤s.castSucc from by change r.val+1≤s.val; omega)
    omega
  · have he := hMono (show s.succ≤r.castSucc from by change s.val+1≤r.val; omega)
    omega

theorem covers {n : ℕ} (U : ℕ) (boundary : FixedArrayTable (n+1) ℕ)
    (hFirst : boundary.read 0=0) (hLast : boundary.read (Fin.last n)=U) : Covers U (cells boundary) := by
  intro i hi
  let S := Finset.univ.filter (fun j : Fin (n+1) => i<boundary.read j)
  have hS : S.Nonempty := ⟨Fin.last n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hLast]; exact hi⟩⟩
  let j := S.min' hS
  have hj : i<boundary.read j := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hJ : 0<j.val := by
    by_contra hn
    have hz : j=0 := by apply Fin.ext; change j.val=0; omega
    rw [hz,hFirst] at hj
    omega
  let r : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
  have hNext : r.succ=j := by
    apply Fin.ext
    change j.val-1+1=j.val
    omega
  refine ⟨r,?_⟩
  simp only [Contains,read_cells]
  constructor
  · by_contra hn
    have hm : r.castSucc∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    have hMin : j≤r.castSucc := S.min'_le _ hm
    have hVal : j.val≤r.val := hMin
    dsimp only [r] at hVal
    omega
  · rw [hNext]
    exact hj

theorem nonempty {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) (hStrict : StrictMono boundary.read) (r : Fin n) :
    ((cells boundary).read r).1<((cells boundary).read r).2 := by
  rw [read_cells]
  exact hStrict (show r.castSucc<r.succ from by change r.val<r.val+1; omega)

theorem breakpoint_sides {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) (hMono : Monotone boundary.read)
    (r : Fin n) (b : Fin (n+1)) :
    boundary.read b≤((cells boundary).read r).1 ∨ ((cells boundary).read r).2≤boundary.read b := by
  rw [read_cells]
  by_cases hB : b.val≤r.val
  · exact Or.inl (hMono (show b≤r.castSucc from hB))
  · exact Or.inr (hMono (show r.succ≤b from by change r.val+1≤b.val; omega))

theorem threshold_constant {n : ℕ} (boundary : FixedArrayTable (n+1) ℕ) (hMono : Monotone boundary.read)
    (r : Fin n) (b : Fin (n+1)) (i j : ℕ) (hI : Contains (cells boundary) r i) (hJ : Contains (cells boundary) r j) :
    boundary.read b≤ i ↔ boundary.read b≤j := by
  have hb := breakpoint_sides boundary hMono r b
  unfold Contains at hI hJ
  rcases hb with hb|hb <;> omega

end Blotto.GeneralPaperBoundaryCells
