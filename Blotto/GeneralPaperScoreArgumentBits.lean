import Blotto.GeneralPaperScorePrefixBits

/-! Literal score-argument evaluation at actual operand widths. The label
successor is formed as a constructed integer before its rational conversion.
The three rational operations and their input/output copies are priced.
-/
namespace Blotto.GeneralPaperScoreArgumentBits
open GeneralPaperBoundedQuotient
set_option autoImplicit false
set_option maxHeartbeats 1500000

def index {K : ℕ} (l : Fin K) : ℚ := ((l.val+1:ℕ):ℚ)

def value {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : ℚ :=
  (S:ℚ)*v.weight j*(index l/(K:ℚ))

theorem value_eq_argument {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) :
    value v S j l=GeneralPaperScoreMatrixWork.argument v S j l := by
  simp only [value,index,GeneralPaperScoreMatrixWork.argument,Nat.cast_add,Nat.cast_one]

def height (V w K : ℕ) : ℕ := V+w+2*binaryWordWidth K+3

theorem operands_height {m K : ℕ} (v : RationalFieldSelector m) (S w V : ℕ) (hCap : S<2^w)
    (j : Fin m) (hValue : RationalHeight (v.weight j) V) (l : Fin K) :
    RationalHeight (S:ℚ) (height V w K) ∧ RationalHeight (v.weight j) (height V w K) ∧
    RationalHeight (index l) (height V w K) ∧ RationalHeight (K:ℚ) (height V w K) ∧
    RationalHeight ((S:ℚ)*v.weight j) (height V w K) ∧
    RationalHeight (index l/(K:ℚ)) (height V w K) ∧ RationalHeight (value v S j l) (height V w K) := by
  have hs := nat_height S w hCap
  have hk := nat_height K (binaryWordWidth K) (lt_pow_binaryWordWidth K)
  have hi : RationalHeight (index l) (binaryWordWidth K+1) :=
    nat_height (l.val+1) (binaryWordWidth K)
      ((Nat.succ_le_of_lt l.isLt).trans_lt (lt_pow_binaryWordWidth K))
  have hm := hs.mul hValue
  have hd := hi.div hk
  have ho := hm.mul hd
  refine ⟨hs.mono ?_,hValue.mono ?_,hi.mono ?_,hk.mono ?_,hm.mono ?_,hd.mono ?_,ho.mono ?_⟩ <;>
    unfold height <;> omega

def argumentRun {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : RationalFieldSelector m)
    (S : ℕ) (j : Fin m) (l : Fin K) : ℚ × ℕ :=
  let converted := index l
  let weighted := (S:ℚ)*v.weight j
  let fraction := converted/(K:ℚ)
  let output := weighted*fraction
  (output,64*W+rationalWordWidth (S:ℚ)+rationalWordWidth (v.weight j)+
    rationalWordWidth converted+rationalWordWidth (K:ℚ)+primitivePrice model (S:ℚ) (v.weight j)+
      primitivePrice model converted (K:ℚ)+primitivePrice model weighted fraction+rationalWordWidth output)

theorem argument_data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : RationalFieldSelector m)
    (S : ℕ) (j : Fin m) (l : Fin K) :
    (argumentRun model W v S j l).1=GeneralPaperScoreMatrixWork.argument v S j l := value_eq_argument v S j l

def argumentProfile (model : RationalCostModel) (W V w K : ℕ) : ℕ :=
  64*W+8*model.rat (1+2*height V w K)

theorem argument_work {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : RationalFieldSelector m)
    (S w V : ℕ) (hCap : S<2^w) (j : Fin m) (hValue : RationalHeight (v.weight j) V) (l : Fin K) :
    (argumentRun model W v S j l).2≤argumentProfile model W V w K := by
  obtain ⟨hs,hv,hi,hk,hm,hd,ho⟩ := operands_height v S w V hCap j hValue l
  have ws := rationalWordWidth_of_height hs
  have wv := rationalWordWidth_of_height hv
  have wi := rationalWordWidth_of_height hi
  have wk := rationalWordWidth_of_height hk
  have wm := rationalWordWidth_of_height hm
  have wd := rationalWordWidth_of_height hd
  have wo := (rationalWordWidth_of_height ho).trans (model.word_le _)
  have ps := ws.trans (model.word_le _)
  have pv := wv.trans (model.word_le _)
  have pi := wi.trans (model.word_le _)
  have pk := wk.trans (model.word_le _)
  have p1 := primitivePrice_le model (S:ℚ) (v.weight j) _ ws wv
  have p2 := primitivePrice_le model (index l) (K:ℚ) _ wi wk
  have p3 := primitivePrice_le model ((S:ℚ)*v.weight j) (index l/(K:ℚ)) _ wm wd
  change 64*W+rationalWordWidth (S:ℚ)+rationalWordWidth (v.weight j)+rationalWordWidth (index l)+
    rationalWordWidth (K:ℚ)+primitivePrice model (S:ℚ) (v.weight j)+primitivePrice model (index l) (K:ℚ)+
      primitivePrice model ((S:ℚ)*v.weight j) (index l/(K:ℚ))+rationalWordWidth (value v S j l)≤_
  unfold argumentProfile
  omega

end Blotto.GeneralPaperScoreArgumentBits
