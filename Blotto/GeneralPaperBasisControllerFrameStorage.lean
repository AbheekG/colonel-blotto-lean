import Blotto.GeneralPaperBasisControllerInitialStorage

/-! Actual basis-controller recursion metadata. Pending ancestors hold
only indices and shared argument references; their child has not returned
a basis yet. One active return frame retains all literal failure/success
partial-work fields. Active old/new basis owners stay in previous checked
stage windows rather than being summed across all recursion depths. -/
namespace Blotto.GeneralPaperBasisControllerFrameStorage
open RationalOrderCell GeneralPaperBasisState GeneralPaperBasisStoredProducts
open GeneralPaperEncodedScalarStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def pendingWindow (W d : ℕ) : ℕ := ∑ i : Fin d,(fields W [i.val+1,d,i.val]+64*W)
def pendingProfile (W d : ℕ) : ℕ := d*(3*(natBits (d+1)+W)+96*W)
def metadataCap (W d F : ℕ) : ℕ := d+F+24*W+1
def controls {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) : (j : ℕ) → j≤m*(K-1) → List ℕ
  | 0,_ =>
    let empty := GeneralPaperBasisArrayPrice.initialRun (fun w => w) W (m*(K-1))
    [0,empty.2,empty.2+8*W,8*W]
  | j+1,hj =>
    let earlier := GeneralPaperBasisControllerBits.stages model W labels matrix S h N betaN initialGrid j (by omega)
    match earlier.1 with
    | none => [j+1,earlier.2,earlier.2+8*W,8*W,0]
    | some state =>
      let updated := GeneralPaperBasisStepBits.run model W labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)
      [j+1,earlier.2,updated.2,earlier.2+updated.2+24*W,24*W,earlier.2+updated.2,
        GeneralPaperFinalStaticLoopStorage.bit updated.1.isSome]
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (j : ℕ) (hj : j≤m*(K-1)) : ℕ :=
  GeneralPaperBasisControllerInitialStorage.window W (m*(K-1))+pendingWindow W (m*(K-1))+
    fields W (controls model W labels matrix S h N betaN initialGrid j hj)+192*W
def profile (W d F : ℕ) : ℕ :=
  GeneralPaperBasisControllerInitialStorage.profile W d+pendingProfile W d+
    7*(natBits (metadataCap W d F)+W)+224*W

theorem pending_bound (W d : ℕ) : pendingWindow W d≤pendingProfile W d := by
  have hEach (i : Fin d) : fields W [i.val+1,d,i.val]+64*W≤3*(natBits (d+1)+W)+96*W := by
    have hf := fields_bound W (natBits (d+1)) [i.val+1,d,i.val] (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl <;> omega)
    change fields W [i.val+1,d,i.val]≤3*(natBits (d+1)+W)+32*W at hf
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hEach i)
  simpa only [pendingWindow,pendingProfile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs

theorem controls_length {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (j : ℕ) (hj : j≤m*(K-1)) :
    (controls model W labels matrix S h N betaN initialGrid j hj).length≤7 := by
  cases j with
  | zero => norm_num only [controls,List.length_cons,List.length_nil]
  | succ j =>
    unfold controls
    dsimp only
    split <;> norm_num only [List.length_cons,List.length_nil]

theorem controls_bounded {T m K : ℕ} (model : RationalCostModel) (W F : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1)))
    (hAll : ∀ j (hj : j≤m*(K-1)),(GeneralPaperBasisControllerBits.stages model W labels matrix S h N betaN initialGrid j hj).2≤F)
    (j : ℕ) (hj : j≤m*(K-1)) :
    fields W (controls model W labels matrix S h N betaN initialGrid j hj)≤7*(natBits (metadataCap W (m*(K-1)) F)+W)+32*W := by
  have hf := fields_bound W (natBits (metadataCap W (m*(K-1)) F))
    (controls model W labels matrix S h N betaN initialGrid j hj) (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      have hCurrent := hAll j hj
      cases j with
      | zero =>
        change (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W (m*(K-1))).2+8*W≤F at hCurrent
        simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold metadataCap
        rcases hz with rfl|rfl|rfl|rfl <;> omega
      | succ j =>
        let earlier := GeneralPaperBasisControllerBits.stages model W labels matrix S h N betaN initialGrid j (by omega)
        change (match earlier.1 with
          | none => (none,earlier.2+8*W)
          | some state => let updated := GeneralPaperBasisStepBits.run model W labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)
            (updated.1,earlier.2+updated.2+24*W)).2≤F at hCurrent
        change z∈(match earlier.1 with
          | none => [j+1,earlier.2,earlier.2+8*W,8*W,0]
          | some state => let updated := GeneralPaperBasisStepBits.run model W labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)
            [j+1,earlier.2,updated.2,earlier.2+updated.2+24*W,24*W,earlier.2+updated.2,
              GeneralPaperFinalStaticLoopStorage.bit updated.1.isSome]) at hz
        cases he : earlier.1 with
        | none =>
          rw [he] at hz hCurrent
          dsimp only at hCurrent
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          unfold metadataCap
          rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega
        | some state =>
          rw [he] at hz hCurrent
          dsimp only at hz hCurrent
          have hb := GeneralPaperFinalStaticLoopStorage.bit_bound
            (GeneralPaperBasisStepBits.run model W labels matrix S h N betaN initialGrid state (Nat.lt_of_succ_le hj)).1.isSome
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          unfold metadataCap
          rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  exact hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (controls_length model W labels matrix S h N betaN initialGrid j hj)) _)

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W F : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (hW : 1≤W)
    (hAll : ∀ j (hj : j≤m*(K-1)),(GeneralPaperBasisControllerBits.stages model W labels matrix S h N betaN initialGrid j hj).2≤F)
    (j : ℕ) (hj : j≤m*(K-1)) : window model W labels matrix S h N betaN initialGrid j hj≤profile W (m*(K-1)) F := by
  have hInitial := GeneralPaperBasisControllerInitialStorage.bounded W (m*(K-1)) hW
  have hPending := pending_bound W (m*(K-1))
  have hFields := controls_bounded model W F labels matrix S h N betaN initialGrid hAll j hj
  unfold window profile
  omega

end Blotto.GeneralPaperBasisControllerFrameStorage
