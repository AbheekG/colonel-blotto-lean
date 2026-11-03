import Blotto.GeneralPaperBitQuotientStorage
import Blotto.GeneralPaperScoreArgumentBits

/-! Literal score-argument storage: all seven rational operands/results,
the three primitive scratch reservations, constructed integer indices and
the actual native argument-work counter. These are erased observers of
the existing call, not additional evaluation or payload traversals. -/
namespace Blotto.GeneralPaperScoreArgumentStorage
open GeneralPaperScoreArgumentBits GeneralPaperBoundedQuotient GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

def window {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : RationalFieldSelector m)
    (S : ℕ) (j : Fin m) (l : Fin K) : ℕ :=
  listFootprint W rationalWordWidth [(S:ℚ),v.weight j,index l,(K:ℚ),(S:ℚ)*v.weight j,
    index l/(K:ℚ),value v S j l]+
    primitivePrice model (S:ℚ) (v.weight j)+primitivePrice model (index l) (K:ℚ)+
    primitivePrice model ((S:ℚ)*v.weight j) (index l/(K:ℚ))+
    fields W [S,K,j.val,l.val,l.val+1,(argumentRun model W v S j l).2]+256*W

def profile (model : RationalCostModel) (W m K S V depth : ℕ) : ℕ :=
  let H := 1+2*height V depth K
  7*(H+2*W)+32*W+3*model.rat H+
    6*(natBits (m+K+S+1+argumentProfile model W V depth K)+W)+32*W+256*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W : ℕ) (v : RationalFieldSelector m)
    (S depth V : ℕ) (hCap : S<2^depth) (j : Fin m) (hv : RationalHeight (v.weight j) V) (l : Fin K) :
    window model W v S j l≤profile model W m K S V depth := by
  obtain ⟨hs,hv',hi,hk,hm,hd,ho⟩ := operands_height v S depth V hCap j hv l
  have ws := rationalWordWidth_of_height hs
  have wv := rationalWordWidth_of_height hv'
  have wi := rationalWordWidth_of_height hi
  have wk := rationalWordWidth_of_height hk
  have wm := rationalWordWidth_of_height hm
  have wd := rationalWordWidth_of_height hd
  have wo := rationalWordWidth_of_height ho
  have hp := list_bound W (1+2*height V depth K) rationalWordWidth
    [(S:ℚ),v.weight j,index l,(K:ℚ),(S:ℚ)*v.weight j,index l/(K:ℚ),value v S j l] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ws
      · exact wv
      · exact wi
      · exact wk
      · exact wm
      · exact wd
      · exact wo)
  change listFootprint W rationalWordWidth _≤7*(1+2*height V depth K+2*W)+32*W at hp
  have p1 := primitivePrice_le model (S:ℚ) (v.weight j) _ ws wv
  have p2 := primitivePrice_le model (index l) (K:ℚ) _ wi wk
  have p3 := primitivePrice_le model ((S:ℚ)*v.weight j) (index l/(K:ℚ)) _ wm wd
  have hw := argument_work model W v S depth V hCap j hv l
  have hf := fields_bound W (natBits (m+K+S+1+argumentProfile model W V depth K))
    [S,K,j.val,l.val,l.val+1,(argumentRun model W v S j l).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals have hj := j.isLt; have hl := l.isLt; omega)
  change fields W _≤6*(natBits (m+K+S+1+argumentProfile model W V depth K)+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

@[fun_prop]
theorem scaling (model : RationalCostModel) (m K S V depth : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W m K S V depth) := by
  unfold profile argumentProfile
  dsimp only
  fun_prop

end Blotto.GeneralPaperScoreArgumentStorage
