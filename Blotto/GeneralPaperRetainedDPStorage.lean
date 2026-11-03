import Blotto.GeneralPaperRetainedForestNodes

/-! Sizes of all retained DP tables, including both children at every node.
Actual rational tag payloads are summed at their own subtree heights. These
observers neither scan tables nor alter execution or backtracking. -/
namespace Blotto.GeneralPaperRetainedDPStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def tables {K J : ℕ} : {h : ℕ} → Computation Tag K J h → ℕ
  | _,.leaf _ => 1
  | _,.node left right _ => tables left+tables right+1

def slots {K J : ℕ} : {h : ℕ} → Computation Tag K J h → ℕ
  | _,.leaf states => states.data.size
  | _,.node left right states => slots left+slots right+states.data.size

theorem tables_exact {K J h : ℕ} (computed : Computation Tag K J h) : tables computed+1=2^(h+1) := by
  induction computed with
  | leaf _ => rfl
  | @node h left right states ihl ihr =>
    dsimp only [tables]
    rw [pow_succ (2:ℕ) (h+1)]
    omega

theorem slots_exact {K J h : ℕ} (computed : Computation Tag K J h) : slots computed=J*tables computed := by
  induction computed with
  | leaf states => simp only [slots,tables,states.size,Nat.mul_one]
  | node left right states ihl ihr => simp only [slots,tables,states.size,ihl,ihr]; ring

theorem slots_bound {K J h : ℕ} (computed : Computation Tag K J h) : slots computed≤2*J*2^h := by
  have ht := tables_exact computed
  rw [pow_succ (2:ℕ) h] at ht
  have hs := Nat.mul_le_mul_left J (show tables computed≤2^h*2 by omega)
  rw [slots_exact]
  nlinarith only [hs]

def tableTagBits {Witness : Type*} {J : ℕ} (states : Table Tag Witness J) : ℕ :=
  ∑ j, (match states.read j with
    | none => 0
    | some selected => rationalWordWidth selected.cost.threshold+2)

theorem table_tag_bits {Witness : Type*} {J : ℕ} (s h : ℕ) (states : Table Tag Witness J)
    (hs : GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) states) :
    tableTagBits states≤J*(GeneralPaperTagHeight.word s h+2) := by
  have hb : ∀ j,(match states.read j with
      | none => 0
      | some selected => rationalWordWidth selected.cost.threshold+2)≤GeneralPaperTagHeight.word s h+2 := by
    intro j
    cases he : states.read j with
    | none => exact Nat.zero_le _
    | some selected => exact Nat.add_le_add_right (rationalWordWidth_of_height (hs j selected he)) 2
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hb j)
  simpa only [tableTagBits,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hsum

def tagBits {K J : ℕ} : {h : ℕ} → Computation Tag K J h → ℕ
  | _,.leaf states => tableTagBits states
  | _,.node left right states => tagBits left+tagBits right+tableTagBits states

def tagProfile (J s : ℕ) : ℕ → ℕ
  | 0 => J*(GeneralPaperTagHeight.word s 0+2)
  | h+1 => 2*tagProfile J s h+J*(GeneralPaperTagHeight.word s (h+1)+2)

theorem native_tag_bits {K q w B h : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (tree : Tree Tag K h) (s : ℕ) (hLeaves : GeneralPaperOrderedDPHeight.Leaves s tree) :
    tagBits (GeneralPaperOrderedProfitDP.run grid tree)≤tagProfile grid.size s h := by
  induction tree with
  | leaf field => exact table_tag_bits s 0 _ (GeneralPaperOrderedDPHeight.states grid (.leaf field) s hLeaves)
  | @node h left right ihl ihr =>
    have hl := ihl hLeaves.1
    have hr := ihr hLeaves.2
    have ht := table_tag_bits s (h+1) _ (GeneralPaperOrderedDPHeight.states grid (.node left right) s hLeaves)
    change tableTagBits (mergeTable grid (GeneralPaperOrderedProfitDP.run grid left).table
      (GeneralPaperOrderedProfitDP.run grid right).table)≤grid.size*(GeneralPaperTagHeight.word s (h+1)+2) at ht
    change tagBits (GeneralPaperOrderedProfitDP.run grid left)+tagBits (GeneralPaperOrderedProfitDP.run grid right)+_≤2*tagProfile grid.size s h+_
    omega

theorem root_word_bound (s h : ℕ) : GeneralPaperTagHeight.word s h+2≤2^h*(2*s+4) := by
  have hw := GeneralPaperBalancedTagWords.word_affine s h
  have hp := Nat.two_pow_pos h
  nlinarith only [hw,hp]

theorem tag_profile_bound (J s h : ℕ) : tagProfile J s h≤J*(h+1)*2^h*(2*s+4) := by
  induction h with
  | zero =>
    have h := Nat.mul_le_mul_left J (root_word_bound s 0)
    simpa only [tagProfile,pow_zero,Nat.mul_one,Nat.one_mul,Nat.zero_add] using h
  | succ h ih =>
    have hw := Nat.mul_le_mul_left J (root_word_bound s (h+1))
    rw [pow_succ (2:ℕ) h] at hw ⊢
    dsimp only [tagProfile]
    nlinarith only [ih,hw]

theorem ready_tag_bits {m k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    tagBits (GeneralPaperOrderedProfitDP.run prepared.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached))≤
        prepared.grid.size*(prepared.parameters.height+1)*2^prepared.parameters.height*(2*(ready.alphabet.lambda+1)+4) :=
  (native_tag_bits prepared.grid _ _ (GeneralPaperOrderedDPHeight.native_tree prepared T ready weights prefixes)).trans
    (tag_profile_bound _ _ _)

theorem priced_ready_tag_bits {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    tagBits (GeneralPaperOrderedDPExecution.run bits index price W prepared.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached)).1≤
        prepared.grid.size*(prepared.parameters.height+1)*2^prepared.parameters.height*(2*(ready.alphabet.lambda+1)+4) := by
  rw [GeneralPaperOrderedDPExecution.data]
  exact ready_tag_bits prepared T ready weights prefixes

end Blotto.GeneralPaperRetainedDPStorage
