import Blotto.GeneralPaperRankArrayExecution

/-! The whole native rank array and its work annotation are returned exactly.
Every query is called once; both arrays include duplicate occurrence ranks.
Prefix equality identifies the existing fill, not an additional traversal.
-/
namespace Blotto.GeneralPaperRankArrayData
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperRankArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem fill_data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) (hDepth : depth=35+k) (count : ℕ) (hCount : count≤m) :
    (fill bits index primitive W k depth values cuts count hCount).1=
      PaperIndexedArrayConstruction.fill (fun _ => 1) 1 (fun q : Fin m =>
        let found := GeneralPaperSelectedRank.lookup k values (cuts.read q)
        (found.position,found.work+8)) count hCount := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [fill,PaperIndexedArrayConstruction.fill]
    dsimp only
    rw [ih]
    simp only [GeneralPaperSelectedRankPrice.data bits primitive W k depth values _ hDepth]
    dsimp only [PaperIndexedArrayConstruction.stepWork]
    congr 1

theorem data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k depth : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) (hDepth : depth=35+k) :
    (run bits index primitive W k depth values cuts).1=GeneralPaperRankCache.build k values cuts := by
  unfold run GeneralPaperRankCache.build PaperIndexedArrayConstruction.run
  dsimp only
  have h := fill_data bits index primitive W k depth values cuts hDepth m (Nat.le_refl _)
  simp only [Prod.mk.injEq,FixedArrayTable.mk.injEq]
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

theorem prepare_data {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k : ℕ) (values : Summary k) (cuts : FixedArrayTable m ℕ) :
    (prepare bits index primitive W k values cuts).1=GeneralPaperRankCache.build k values cuts :=
  data bits index primitive W k (35+k) values cuts rfl

theorem cached_spec {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k : ℕ) (values : Summary k)
    (cuts : FixedArrayTable m ℕ) (hMono : Monotone values.read) (q : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    values.read r<cuts.read q ↔ r.val<((prepare bits index primitive W k values cuts).1.1.read q).val := by
  rw [prepare_data]
  exact GeneralPaperRankCache.cached_spec k values hMono cuts q r

end Blotto.GeneralPaperRankArrayData
