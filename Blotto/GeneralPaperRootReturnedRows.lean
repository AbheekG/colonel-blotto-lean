import Blotto.GeneralPaperRowTrimPrice

/-! Returned native root tuples have the actual padded leaf count. This
discharges decoded-list conversion prices without a length traversal or a
caller-supplied shape oracle, even when other root inputs are arbitrary. -/
namespace Blotto.GeneralPaperRootReturnedRows
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem length {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag)
    (result : Fin grid.size × List (Fin K))
    (hResult : (GeneralPaperOrderedRootExecution.run bits index price W grid tree budget).1=some result) :
    result.2.length=2^h := by
  rw [GeneralPaperOrderedRootExecution.data] at hResult
  dsimp only [GeneralPaperOrderedProfitRoot.solve] at hResult
  cases hs : GeneralPaperOrderedProfitRoot.select (GeneralPaperOrderedProfitDP.run grid tree).table budget with
  | none => simp only [hs] at hResult; cases hResult
  | some label =>
    cases hd : decode (GeneralPaperOrderedProfitDP.run grid tree) label with
    | none => simp only [hs,hd,Option.map_none] at hResult; cases hResult
    | some labels =>
      have he : (label,labels)=result := by simpa only [hs,hd,Option.map_some,Option.some.injEq] using hResult
      rw [←he]
      exact GeneralPaperTypedDecodeLength.length _ label labels hd

theorem trim_work {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W m : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag)
    (result : Fin grid.size × List (Fin K))
    (hResult : (GeneralPaperOrderedRootExecution.run bits index price W grid tree budget).1=some result) :
    (GeneralPaperRowTrimExecution.run (fun x => x) (GeneralPaperRowTrimPrice.word W m (2^h)) m result.2).2≤
      GeneralPaperRowTrimPrice.profile W m (2^h) :=
  GeneralPaperRowTrimPrice.work W m (2^h) result.2 (by rw [length bits index price W grid tree budget result hResult])

theorem trim_arithmetic_work {K q w B h : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W m : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h) (budget : Tag)
    (result : Fin grid.size × List (Fin K))
    (hResult : (GeneralPaperOrderedRootExecution.run bits index price W grid tree budget).1=some result) :
    (GeneralPaperRowTrimExecution.run (fun _ => 1) 1 m result.2).2≤64*2^h+108*m+173 :=
  GeneralPaperRowTrimPrice.arithmetic_work m (2^h) result.2 (by rw [length bits index price W grid tree budget result hResult])

end Blotto.GeneralPaperRootReturnedRows
