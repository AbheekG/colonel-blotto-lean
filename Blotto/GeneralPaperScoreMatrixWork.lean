import Blotto.GeneralPaperThresholdScanWork

/-! Materialized literal floor-score matrix from arithmetic/comparisons.
The bounded quotient evaluates each score once. The source profile pays the
arithmetic, anchor read, pair fields and indexed array construction. This is
a real-RAM profile; bit/height and simultaneous-space joins remain separate.
-/
namespace Blotto.GeneralPaperScoreMatrixWork
open GeneralPaperDictionary GeneralPaperStrictScore GeneralPaperExactScoreDP
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def argument {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : ℚ :=
  (S:ℚ)*v.weight j*((l.val+1:ℚ)/(K:ℚ))

theorem argument_bounds {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K)
    (j : Fin m) (l : Fin K) : 0≤argument v S j l ∧ argument v S j l≤(S:ℚ) := by
  have hk : (0:ℚ)<K := by exact_mod_cast hK
  have hv : v.weight j≤1 := by
    rw [← v.sum_one]
    exact Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (v.positive k).le) (Finset.mem_univ j)
  have hl : (l.val+1:ℚ)≤K := by exact_mod_cast Nat.succ_le_of_lt l.isLt
  have hf := (div_le_one hk).mpr hl
  have hvPos := v.positive j
  have hp : (0:ℚ)≤(S:ℚ)*v.weight j := by positivity
  have hs := mul_le_mul_of_nonneg_left hv (show (0:ℚ)≤S by positivity)
  have he := mul_le_mul_of_nonneg_left hf hp
  unfold argument
  constructor
  · positivity
  · simp only [mul_one] at hs he
    exact he.trans hs

def scoreRun {m K : ℕ} (w : ℕ) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) : ℕ × ℕ :=
  let result := GeneralPaperBoundedQuotient.run (argument v S j l) 1 w
  (result.quotient,result.work+12)

theorem score_data {m K : ℕ} (w : ℕ) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K)
    (hCap : S<2^w) (j : Fin m) (l : Fin K) : (scoreRun w v S j l).1=score v S j l := by
  have ha := argument_bounds v S hK j l
  have hcap : (S:ℚ)<(2:ℚ)^w := by exact_mod_cast hCap
  exact GeneralPaperBoundedQuotient.run_floor _ w ha.1 (ha.2.trans_lt hcap)

theorem score_work {m K : ℕ} (w : ℕ) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) (l : Fin K) :
    (scoreRun w v S j l).2=12*w+14 := by
  simp only [scoreRun,GeneralPaperBoundedQuotient.run_work]

def fieldRun {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) :
    Field K × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fun l =>
    let result := scoreRun w v S j l
    ((result.1,d.anchor j l),result.2+4))

theorem field_data {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (hCap : S<2^w) (j : Fin m) :
    (fieldRun w d v S j).1=FixedArrayTable.ofFn (fun l => (score v S j l,d.anchor j l)) := by
  unfold fieldRun
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [score_data w v S hK hCap]

theorem field_work {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) (j : Fin m) :
    (fieldRun w d v S j).2≤64*(K+1)*(w+1) := by
  unfold fieldRun
  apply (PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1
    (fun l => (((scoreRun w v S j l).1,d.anchor j l),(scoreRun w v S j l).2+4))).trans
  simp only [score_work,Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id]
  nlinarith

def matrixRun {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    FixedArrayTable m (Field K) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 0) 1 (fieldRun w d v S)

theorem matrix_data {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (matrixRun w d v S).1=FixedArrayTable.ofFn (fun j => FixedArrayTable.ofFn (fun l => (score v S j l,d.anchor j l))) := by
  unfold matrixRun
  rw [PaperIndexedArrayConstruction.run_data]
  simp only [field_data w d v S hK hCap]

theorem matrix_work {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    (matrixRun w d v S).2≤128*(m+1)*(K+1)*(w+1) := by
  have he := field_work w d v S
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_id] at hSum
  have h := PaperIndexedArrayConstruction.run_work_bound (fun _ => 0) 0 (fun _ => by simp) 1 (fieldRun w d v S)
  change (matrixRun w d v S).2≤(∑ j,(fieldRun w d v S j).2)+(m+1)*(6+10*0*binaryWordWidth (m+1)+28) at h
  norm_num only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero,Nat.reduceAdd] at h
  let Q := (K+1)*(w+1)
  have hQ : 1≤Q := by
    have hp : 0<(K+1)*(w+1) := Nat.mul_pos (by omega) (by omega)
    exact hp
  have hm := Nat.mul_le_mul_left m hQ
  have hs : (∑ j,(fieldRun w d v S j).2)≤64*m*Q := by
    simpa only [Q,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hSum
  calc
    _ ≤ 128*(m+1)*Q := by nlinarith only [h,hs,hm,hQ]
    _ = _ := by dsimp only [Q]; ring

def fieldsRun {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) : List (Field K) × ℕ :=
  let matrix := matrixRun w d v S
  (matrix.1.data.toList,matrix.2+8*m+4)

theorem fields_data {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m)
    (S : ℕ) (hK : 0<K) (hCap : S<2^w) : (fieldsRun w d v S).1=fields (score v S) d.anchor := by
  simp only [fieldsRun,matrix_data w d v S hK hCap,FixedArrayTable.ofFn,Array.toList_ofFn,fields]

theorem fields_work {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ) :
    (fieldsRun w d v S).2≤256*(m+1)*(K+1)*(w+1) := by
  have h := matrix_work w d v S
  change (matrixRun w d v S).2+8*m+4≤_
  let Q := (K+1)*(w+1)
  have hQ : 1≤Q := by
    have hp : 0<(K+1)*(w+1) := Nat.mul_pos (by omega) (by omega)
    exact hp
  have hm := Nat.mul_le_mul_left (m+1) hQ
  have hs : (matrixRun w d v S).2≤128*(m+1)*Q := by
    simpa only [Q,Nat.mul_assoc] using h
  calc
    _ ≤ 256*(m+1)*Q := by nlinarith only [hs,hm]
    _ = _ := by dsimp only [Q]; ring

end Blotto.GeneralPaperScoreMatrixWork
