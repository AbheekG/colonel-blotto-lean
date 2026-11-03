import Blotto.GeneralPaperScoreArgumentBits

/-! Full bit-priced materialized score matrix. Each entry evaluates its
argument and bounded floor once, then stores the score/resource pair. Both
indexed array loops and the ordered field-reference list are charged.
-/
namespace Blotto.GeneralPaperScoreMatrixBits
open GeneralPaperDictionary GeneralPaperExactScoreDP GeneralPaperStrictScore
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def scoreRun {m K : ℕ} (model : RationalCostModel) (W w : ℕ) (v : RationalFieldSelector m)
    (S : ℕ) (j : Fin m) (l : Fin K) : ℕ × ℕ :=
  let argument := GeneralPaperScoreArgumentBits.argumentRun model W v S j l
  let quotient := GeneralPaperBoundedQuotient.runWithBits model W argument.1 1 w
  (quotient.1.quotient,argument.2+quotient.2+16*W)

theorem score_data {m K : ℕ} (model : RationalCostModel) (W w : ℕ) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m) (l : Fin K) :
    (scoreRun model W w v S j l).1=score v S j l := by
  simp only [scoreRun,GeneralPaperBoundedQuotient.run_data,GeneralPaperScoreArgumentBits.argument_data]
  exact GeneralPaperScoreMatrixWork.score_data w v S hK hCap j l

def scoreProfile (model : RationalCostModel) (W V w K : ℕ) : ℕ :=
  GeneralPaperScoreArgumentBits.argumentProfile model W V w K+
    GeneralPaperBoundedQuotient.bitProfile model W (GeneralPaperScoreArgumentBits.height V w K) 1 w+16*W

theorem score_work {m K : ℕ} (model : RationalCostModel) (W w : ℕ) (v : RationalFieldSelector m)
    (S V : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m) (hValue : RationalHeight (v.weight j) V) (l : Fin K) :
    (scoreRun model W w v S j l).2≤scoreProfile model W V w K := by
  have ha := GeneralPaperScoreArgumentBits.argument_work model W v S w V hCap j hValue l
  have hx := (GeneralPaperScoreArgumentBits.operands_height v S w V hCap j hValue l).2.2.2.2.2.2
  rw [GeneralPaperScoreArgumentBits.value_eq_argument] at hx
  have hb := GeneralPaperScoreMatrixWork.argument_bounds v S hK j l
  have hcap : GeneralPaperScoreMatrixWork.argument v S j l<(1:ℚ)*(2:ℚ)^w := by
    have hS : (S:ℚ)<(2:ℚ)^w := by exact_mod_cast hCap
    simpa only [one_mul] using hb.2.trans_lt hS
  have hOne : RationalHeight 1 1 := by norm_num [RationalHeight]
  have hq := GeneralPaperBoundedQuotient.run_bit_work model W
    (GeneralPaperScoreMatrixWork.argument v S j l) 1 (by norm_num) w
      (GeneralPaperScoreArgumentBits.height V w K) 1 hb.1 hcap hx hOne
  have hqActual :
      (GeneralPaperBoundedQuotient.runWithBits model W
        (GeneralPaperScoreArgumentBits.argumentRun model W v S j l).1 1 w).2≤
          GeneralPaperBoundedQuotient.bitProfile model W (GeneralPaperScoreArgumentBits.height V w K) 1 w := by
    rw [GeneralPaperScoreArgumentBits.argument_data]
    exact hq
  unfold scoreRun scoreProfile
  dsimp only
  omega

def entryRun {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : (ℕ × ℚ) × ℕ :=
  let result := scoreRun model W w v S j l
  ((result.1,d.anchor j l),result.2+rationalWordWidth (d.anchor j l)+8*W)

theorem entry_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m) (l : Fin K) :
    (entryRun model W w d v S j l).1=(score v S j l,d.anchor j l) := by
  simp only [entryRun,score_data model W w v S hK hCap]

def entryProfile (model : RationalCostModel) (W V A w K : ℕ) : ℕ :=
  scoreProfile model W V w K+model.rat (1+2*A)+8*W

theorem entry_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S V A : ℕ) (hK : 0<K) (hCap : S<2^w)
    (j : Fin m) (hValue : RationalHeight (v.weight j) V) (l : Fin K) (hAnchor : RationalHeight (d.anchor j l) A) :
    (entryRun model W w d v S j l).2≤entryProfile model W V A w K := by
  have hs := score_work model W w v S V hK hCap j hValue l
  have ha := (rationalWordWidth_of_height hAnchor).trans (model.word_le _)
  unfold entryRun entryProfile
  dsimp only
  omega

theorem array_overhead (n W : ℕ) (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) :
    (n+1)*(6*W+10*binaryWordWidth (n+1)+28)≤44*(n+1)*W := by
  have hp : 6*W+10*binaryWordWidth (n+1)+28≤44*W := by omega
  exact (Nat.mul_le_mul_left (n+1) hp).trans_eq (by ring)

def fieldRun {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) : Field K × ℕ :=
  PaperIndexedArrayConstruction.run (fun b => b) W (entryRun model W w d v S j)

theorem field_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m) :
    (fieldRun model W w d v S j).1=FixedArrayTable.ofFn (fun l => (score v S j l,d.anchor j l)) := by
  unfold fieldRun
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [entry_data model W w d v S hK hCap]

def fieldProfile (model : RationalCostModel) (W V A w K : ℕ) : ℕ :=
  K*entryProfile model W V A w K+44*(K+1)*W

theorem field_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S V A : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m)
    (hValue : RationalHeight (v.weight j) V) (hAnchors : ∀ l,RationalHeight (d.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) :
    (fieldRun model W w d v S j).2≤fieldProfile model W V A w K := by
  have hSum := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) =>
    entry_work model W w d v S V A hK hCap j hValue l (hAnchors l))
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun b => b) 1 (fun _ => by omega) W
    (entryRun model W w d v S j)
  change (fieldRun model W w d v S j).2≤(∑ l,(entryRun model W w d v S j l).2)+
    (K+1)*(6*W+10*binaryWordWidth (K+1)+28) at hArray
  unfold fieldProfile
  exact hArray.trans (Nat.add_le_add hSum (array_overhead K W hW hLabel))

def matrixRun {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) : FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run (fun b => b) W (fieldRun model W w d v S)

theorem matrix_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (matrixRun model W w d v S).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => (score v S j l,d.anchor j l))) := by
  unfold matrixRun
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [field_data model W w d v S hK hCap]

def matrixProfile (model : RationalCostModel) (W V A w m K : ℕ) : ℕ :=
  m*fieldProfile model W V A w K+44*(m+1)*W

theorem matrix_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S V A : ℕ) (hK : 0<K) (hCap : S<2^w)
    (hValues : ∀ j,RationalHeight (v.weight j) V) (hAnchors : ∀ j l,RationalHeight (d.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (matrixRun model W w d v S).2≤matrixProfile model W V A w m K := by
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    field_work model W w d v S V A hK hCap j (hValues j) (hAnchors j) hW hLabel)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have hArray := PaperIndexedArrayConstruction.run_work_bound (fun b => b) 1 (fun _ => by omega) W
    (fieldRun model W w d v S)
  change (matrixRun model W w d v S).2≤(∑ j,(fieldRun model W w d v S j).2)+
    (m+1)*(6*W+10*binaryWordWidth (m+1)+28) at hArray
  unfold matrixProfile
  exact hArray.trans (Nat.add_le_add hSum (array_overhead m W hW hField))

def fieldsRun {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) : List (Field K) × ℕ :=
  let matrix := matrixRun model W w d v S
  (matrix.1.data.toList,matrix.2+8*m*W+4*W)

theorem fields_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (fieldsRun model W w d v S).1=fields (score v S) d.anchor := by
  simp only [fieldsRun,matrix_data model W w d v S hK hCap,FixedArrayTable.ofFn,Array.toList_ofFn,fields]

def fieldsProfile (model : RationalCostModel) (W V A w m K : ℕ) : ℕ :=
  matrixProfile model W V A w m K+8*m*W+4*W

theorem fields_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (v : RationalFieldSelector m) (S V A : ℕ) (hK : 0<K) (hCap : S<2^w)
    (hValues : ∀ j,RationalHeight (v.weight j) V) (hAnchors : ∀ j l,RationalHeight (d.anchor j l) A)
    (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (fieldsRun model W w d v S).2≤fieldsProfile model W V A w m K := by
  have h := matrix_work model W w d v S V A hK hCap hValues hAnchors hW hLabel hField
  unfold fieldsRun fieldsProfile
  dsimp only
  omega

end Blotto.GeneralPaperScoreMatrixBits
