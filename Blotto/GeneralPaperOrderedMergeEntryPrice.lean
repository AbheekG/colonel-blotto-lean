import Blotto.GeneralPaperOrderedLeafEntryPrice

/-! One present child pair performs one cached grid query, one raw profit
addition and one exact tag addition. Missing pairs return immediately. Typed
child indices are borrowed; no candidate-pair array is materialized. -/
namespace Blotto.GeneralPaperOrderedMergeEntryPrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 800000

def run {Left Right : Type*} {q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (i j : Fin grid.size) : Option (Entry Tag (Fin grid.size × Fin grid.size) grid.size) × ℕ :=
  let A := if bits then arrayWord W grid.size else W
  match left.read i,right.read j with
  | some a,some b =>
    let rounded := GeneralPaperProfitGridRoundExecution.merge bits price W grid (grid.numerators.read i+grid.numerators.read j)
    let resource := GeneralPaperTagPrimitivePrice.add price W a.cost b.cost
    (some ⟨rounded.1.label,⟨resource.1,(i,j)⟩⟩,rounded.2+resource.2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (grid.numerators.read i) (grid.numerators.read j)+256*W+128*A)
  | _,_ => (none,64*W+128*A)

theorem data {Left Right : Type*} {q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (i j : Fin grid.size) : (run bits price W grid left right i j).1=mergeEntry grid left right i j := by
  cases hl : left.read i <;> cases hr : right.read j <;>
    simp only [run,mergeEntry,hl,hr,GeneralPaperProfitGridRoundExecution.merge_data,GeneralPaperTagPrimitivePrice.add_data]

theorem safe {Left Right : Type*} {q w B : ℕ} (bits : Bool) (price : ℕ → ℕ) (W s h : ℕ)
    (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (left : Table Tag Left grid.size) (right : Table Tag Right grid.size)
    (i j : Fin grid.size) (hl : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) left)
    (hr : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) right) :
    GeneralPaperOrderedTableHeight.OptionalSafe (expressionHeightBudget s (h+1)) (run bits price W grid left right i j).1 := by
  rw [data]
  cases hli : left.read i with
  | none => intro e he; simp only [mergeEntry,hli] at he; contradiction
  | some a =>
    cases hrj : right.read j with
    | none => intro e he; simp only [mergeEntry,hli,hrj] at he; contradiction
    | some b =>
      intro e he
      simp only [mergeEntry,hli,hrj,Option.some.injEq] at he
      rw [←he]
      exact GeneralPaperTagHeight.add_height s h a.cost b.cost (hl i a hli) (hr j b hrj)

theorem profit_add_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (i j : Fin prepared.grid.size) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (prepared.grid.numerators.read i) (prepared.grid.numerators.read j)≤
      2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  subst prepared
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let F := GeneralPaperProfitGridPoints.denominator p.width p.exponent
  let grid := GeneralPaperProfitGridPrepare.prepare p.qProf p.width p.exponent
  let V := GeneralPaperProfitGridQueryOperands.cap p.qProf F
  have hi := GeneralPaperProfitGridPrepare.numerator_bound p.qProf p.width p.exponent i
  have hj := GeneralPaperProfitGridPrepare.numerator_bound p.qProf p.width p.exponent j
  have hv := (GeneralPaperProfitGridQueryOperands.cap_large p.qProf F).2.2.2
  have hn := GeneralPaperRankOperands.basic grid.size grid.depth V
  change grid.numerators.read i≤2*F at hi
  change grid.numerators.read j≤2*F at hj
  change 4*F+1≤V at hv
  have h := GeneralPaperProfitGridRoundPrice.binary_work price hMono grid.depth V grid.depthCap (fun a b => a+b)
    (grid.numerators.read i) (grid.numerators.read j) (by omega) (by omega) (by omega)
  have hw := hMono (GeneralPaperProfitGridQueryOperands.source_word m lambda k Qv)
  exact h.trans (Nat.mul_le_mul_left 2 hw)

def profile (price : ℕ → ℕ) (W m lambda k Qv J s h : ℕ) : ℕ :=
  GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+
    2*price (GeneralPaperTagHeight.word s (h+1))+2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+
    320*W+128*arrayWord W J

theorem bit_work {Left Right : Type*} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv s h : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (left : Table Tag Left prepared.grid.size) (right : Table Tag Right prepared.grid.size) (i j : Fin prepared.grid.size)
    (hl : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) left)
    (hr : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) right) :
    (run true price W prepared.grid left right i j).2≤profile price W m lambda k Qv prepared.grid.size s h := by
  cases hli : left.read i with
  | none =>
    simp only [run,hli,ite_true]
    unfold profile
    omega
  | some a =>
    cases hrj : right.read j with
    | none =>
      simp only [run,hli,hrj,ite_true]
      unfold profile
      omega
    | some b =>
      have hg := GeneralPaperCachedProfitGridPrice.merge_work price hMono W m lambda k Qv prepared.parameters
        (congrArg GeneralPaperProfitParameters.Prepared.parameters hp) prepared.grid (by cases hp; rfl) i j
      have ht := GeneralPaperTagHeight.add_work price hMono W s h a.cost b.cost (hl i a hli) (hr j b hrj)
      have hn := profit_add_work price hMono m lambda k Qv prepared hp i j
      simp only [run,hli,hrj,ite_true]
      unfold profile
      omega

theorem arithmetic_work {Left Right : Type*} {q w B : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (left : Table Tag Left grid.size) (right : Table Tag Right grid.size) (i j : Fin grid.size) :
    (run false (fun _ => 1) 1 grid left right i j).2≤512*(grid.depth+1)^2+658 := by
  cases hl : left.read i with
  | none =>
    simp only [run,hl,Bool.false_eq_true,ite_false]
    omega
  | some a =>
    cases hr : right.read j with
    | none =>
      simp only [run,hl,hr,Bool.false_eq_true,ite_false]
      omega
    | some b =>
      have h := GeneralPaperProfitGridRoundExecution.merge_arithmetic_work grid (grid.numerators.read i+grid.numerators.read j)
      simp only [run,hl,hr,Bool.false_eq_true,ite_false,GeneralPaperTagPrimitivePrice.add_arithmetic,
        GeneralPaperNaturalPrimitivePrice.binary]
      omega

end Blotto.GeneralPaperOrderedMergeEntryPrice
