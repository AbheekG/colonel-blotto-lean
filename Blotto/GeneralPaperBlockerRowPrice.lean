import Blotto.GeneralPaperBasisEndpointPrice

/-! Construct one ORIGINAL blocker row from its descriptor. Tuple rows
visit the m recovered/original labels once; no high tuple is enumerated.
The literal static and high row terms, signs and RHS fields are preserved.
-/
namespace Blotto.GeneralPaperBlockerRowPrice
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperRayBlockerRows
open GeneralPaperStaticRayRows
set_option autoImplicit false
set_option maxHeartbeats 5000000

def tupleRun {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) : List (Variable m K × ℤ) × ℕ :=
  let terms := GeneralPaperPricedListStream.flatMap W
    (fun j => (refTerms (tupleReference j (labels j)),16*W)) (List.finRange m)
  (terms.1,terms.2+16*(m+1)*W)

theorem tuple_data {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) :
    (tupleRun W labels).1=(rawRow (fun _ => 0) (.inr (labels,0))).terms := by
  simp only [tupleRun,GeneralPaperPricedListStream.flatMap_data,rawRow,List.ofFn_eq_map]
  have hh (xs : List (Fin m)) : xs.flatMap (fun j => refTerms (tupleReference j (labels j)))=
      (xs.map (fun j => refTerms (tupleReference j (labels j)))).flatten := by
    induction xs with
    | nil => rfl
    | cons j rest ih => simp only [List.flatMap_cons,List.map_cons,List.flatten_cons,ih]
  exact hh _

theorem tuple_work {m K : ℕ} (W : ℕ) (labels : Fin m → Fin K) :
    (tupleRun W labels).2≤64*(m+1)*W := by
  have hh := GeneralPaperPricedListStream.flatMap_work W 1 (16*W)
    (fun j => (refTerms (tupleReference j (labels j)),16*W)) (List.finRange m)
    (fun j _ => refTerms_length _) (fun _ _ => le_rfl)
  simp only [List.length_finRange] at hh
  change _+16*(m+1)*W≤_
  nlinarith only [hh,Nat.zero_le (m*W)]

def run {T m K : ℕ} (W : ℕ) (labels : Fin T → Fin m → Fin K) : Descriptor T m K → Row (Variable m K) × ℕ
  | .inl (.inl (v,b)) => (if b then ⟨[(v,1)],1,0⟩ else ⟨[(v,-1)],0,0⟩,32*W)
  | .inl (.inr (.inl (j,l))) =>
    (⟨refTerms (reference j (orderLeft l))++(refTerms (reference j (orderRight l))).map (fun t => (t.1,-t.2)),0,0⟩,64*W)
  | .inl (.inr (.inr i)) =>
    let terms := tupleRun W (labels i)
    (⟨terms.1,1,0⟩,terms.2+16*W)
  | .inr tuple =>
    let terms := tupleRun W tuple.read
    let signed := GeneralPaperPricedListMap.run W (fun t => ((t.1,-t.2),8*W)) terms.1
    (⟨signed.1,0,-1⟩,terms.2+signed.2+16*W)

theorem data {T m K : ℕ} (W : ℕ) (labels : Fin T → Fin m → Fin K) (blocker : Descriptor T m K) :
    (run W labels blocker).1=GeneralPaperRayBlockerRows.row labels blocker := by
  rcases blocker with static|tuple
  · rcases static with ⟨v,b⟩|⟨j,l⟩|i
    · cases b <;> rfl
    · rfl
    · simp only [run,tuple_data,GeneralPaperRayBlockerRows.row,GeneralPaperStaticRayRows.row,constraints,embed]
  · simp only [run,GeneralPaperPricedListMap.data,tuple_data,GeneralPaperRayBlockerRows.row,LinearRow.neg]

theorem length {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K) (blocker : Descriptor T m K) :
    (GeneralPaperRayBlockerRows.row labels blocker).terms.length≤m+1 := by
  rcases blocker with static|tuple
  · exact (GeneralPaperStaticRowPrice.row_length labels static).trans (GeneralPaperStaticRowPrice.support_bound hm static)
  · simp only [GeneralPaperRayBlockerRows.row,LinearRow.neg,List.length_map]
    exact (rawRow_sum_length (fun _ => 0) tuple.read 0).trans (Nat.le_succ _)

theorem work {T m K : ℕ} (W : ℕ) (labels : Fin T → Fin m → Fin K) (blocker : Descriptor T m K) :
    (run W labels blocker).2≤256*(m+1)*W := by
  rcases blocker with static|tuple
  · rcases static with ⟨v,b⟩|⟨j,l⟩|i
    · change 32*W≤_; nlinarith only [Nat.zero_le (m*W)]
    · change 64*W≤_; nlinarith only [Nat.zero_le (m*W)]
    · have hh := tuple_work W (labels i)
      change (tupleRun W (labels i)).2+16*W≤_
      nlinarith only [hh,Nat.zero_le (m*W)]
  · have ht := tuple_work W tuple.read
    have hl : (tupleRun W tuple.read).1.length≤m := by rw [tuple_data]; exact rawRow_sum_length (fun _ => 0) tuple.read 0
    have hm' := GeneralPaperPricedListMap.work W (8*W) (fun t : Variable m K × ℤ => ((t.1,-t.2),8*W))
      (tupleRun W tuple.read).1 (fun _ _ => le_rfl)
    have hp := Nat.mul_le_mul_left (8*W+8*W) hl
    change (tupleRun W tuple.read).2+_+16*W≤_
    nlinarith only [ht,hm',hp,Nat.zero_le (m*W)]

end Blotto.GeneralPaperBlockerRowPrice
