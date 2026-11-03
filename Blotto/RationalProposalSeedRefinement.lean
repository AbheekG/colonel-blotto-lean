import Blotto.RationalProposalBlockSampler

/-! Exact address-list versus consecutive-block refinement, including all
out-of-range reader positions. This is a layout equality for every seed. -/

namespace Blotto
namespace RationalWeightedGuideTree

theorem readSeedBlock_head (width : ℕ) (rest : List ℕ)
    (bits : Fin (width :: rest).sum → Bool) :
    readSeedBlock (width :: rest) bits 0 =
      finiteBitReader (fun i : Fin width => bits ⟨i.val, by simp only [List.sum_cons]; omega⟩) := by
  funext pos
  by_cases hp : pos < width
  · rw [readSeedBlock_eq _ _ 0 pos (by simp) hp]
    unfold finiteBitReader
    rw [dite_eq_left hp]
    congr 1
    apply Fin.ext
    change blockOffset (width :: rest) 0 + pos = pos
    simp [blockOffset]
  · simp only [readSeedBlock, List.length_cons, Nat.zero_lt_succ, dite_true,
      List.getElem_cons_zero, hp, dite_false, finiteBitReader]

theorem readSeedBlock_cons_tail (width : ℕ) (rest : List ℕ)
    (bits : Fin (width :: rest).sum → Bool) (node : ℕ) :
    readSeedBlock (width :: rest) bits (1 + node) =
      readSeedBlock rest
        (fun i => bits ⟨width + i.val, by simp only [List.sum_cons]; omega⟩) node := by
  funext pos
  by_cases hn : node < rest.length
  · have hn' : 1 + node < (width :: rest).length := by simp only [List.length_cons]; omega
    by_cases hp : pos < rest[node]
    · have hp' : pos < (width :: rest)[1 + node] := by simpa [Nat.add_comm] using hp
      rw [readSeedBlock_eq _ _ _ pos hn' hp', readSeedBlock_eq _ _ _ pos hn hp]
      congr 1
      apply Fin.ext
      simp only [blockOffset, Nat.add_comm 1 node, List.take_succ_cons, List.sum_cons]
      omega
    · have hp' : ¬pos < (width :: rest)[1 + node] := by simpa [Nat.add_comm] using hp
      simp only [readSeedBlock, hn', hn, dite_true, hp', hp, dite_false]
  · have hn' : ¬1 + node < (width :: rest).length := by simp only [List.length_cons]; omega
    simp only [readSeedBlock, hn', hn, dite_false]

theorem blockOffset_append_left (first second : List ℕ) (node : ℕ) (hn : node < first.length) :
    blockOffset (first ++ second) node = blockOffset first node := by
  unfold blockOffset
  rw [List.take_append]
  have he : node - first.length = 0 := by omega
  simp only [he, List.take_zero, List.append_nil]

theorem blockOffset_append_right (first second : List ℕ) (node : ℕ) :
    blockOffset (first ++ second) (first.length + node) = first.sum + blockOffset second node := by
  unfold blockOffset
  rw [List.take_append]
  have he : first.take (first.length + node) = first := List.take_of_length_le (by omega)
  rw [he]
  simp only [Nat.add_sub_cancel_left, List.sum_append]

theorem readSeedBlock_append_left (first second : List ℕ)
    (bits : Fin (first ++ second).sum → Bool) (node : ℕ) (hn : node < first.length) :
    readSeedBlock (first ++ second) bits node =
      readSeedBlock first
        (fun i => bits ⟨i.val, by rw [List.sum_append]; omega⟩) node := by
  funext pos
  have hn' : node < (first ++ second).length := by rw [List.length_append]; omega
  by_cases hp : pos < first[node]
  · have hp' : pos < (first ++ second)[node] := by simpa only [List.getElem_append_left hn] using hp
    rw [readSeedBlock_eq _ _ _ pos hn' hp', readSeedBlock_eq _ _ _ pos hn hp]
    congr 1
    apply Fin.ext
    change blockOffset (first ++ second) node + pos = blockOffset first node + pos
    rw [blockOffset_append_left first second node hn]
  · have hp' : ¬pos < (first ++ second)[node] := by simpa only [List.getElem_append_left hn] using hp
    simp only [readSeedBlock, hn', hn, dite_true, hp', hp, dite_false]

theorem readSeedBlock_append_right (first second : List ℕ)
    (bits : Fin (first ++ second).sum → Bool) (node : ℕ) :
    readSeedBlock (first ++ second) bits (first.length + node) =
      readSeedBlock second
        (fun i => bits ⟨first.sum + i.val, by rw [List.sum_append]; omega⟩) node := by
  funext pos
  by_cases hn : node < second.length
  · have hn' : first.length + node < (first ++ second).length := by rw [List.length_append]; omega
    have hg : (first ++ second)[first.length + node] = second[node] := by
      simpa only [Nat.add_comm] using (List.getElem_append_right' first hn).symm
    by_cases hp : pos < second[node]
    · have hp' : pos < (first ++ second)[first.length + node] := by rw [hg]; exact hp
      rw [readSeedBlock_eq _ _ _ pos hn' hp', readSeedBlock_eq _ _ _ pos hn hp]
      congr 1
      apply Fin.ext
      change blockOffset (first ++ second) (first.length + node) + pos =
        first.sum + (blockOffset second node + pos)
      rw [blockOffset_append_right]
      omega
    · have hp' : ¬pos < (first ++ second)[first.length + node] := by rw [hg]; exact hp
      simp only [readSeedBlock, hn', hn, dite_true, hp', hp, dite_false]
  · have hn' : ¬first.length + node < (first ++ second).length := by rw [List.length_append]; omega
    simp only [readSeedBlock, hn', hn, dite_false]

theorem sampleRecord_congr_nodes (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (first second : ℕ → ℕ → Bool)
    (h : ∀ node, node < tree.nodes → first node = second node) :
    tree.sampleRecord B K first = tree.sampleRecord B K second := by
  induction tree generalizing B first second with
  | leaf family guide gamma =>
    change family.conditionalSample B K (first 0) = family.conditionalSample B K (second 0)
    rw [h 0 (by simp [nodes])]
  | fork guide gamma left right ihLeft ihRight =>
    have hroot := h 0 (by simp [nodes])
    have hright : ∀ node, node < right.nodes → first (1 + node) = second (1 + node) := by
      intro node hn
      exact h _ (by simp only [nodes]; omega)
    have hleft : ∀ node, node < left.nodes →
        first (1 + right.nodes + node) = second (1 + right.nodes + node) := by
      intro node hn
      exact h _ (by simp only [nodes]; omega)
    unfold sampleRecord
    rw [hroot]
    cases hi : left.guide.syntheticSample right.guide B K (second 0) with
    | none => rfl
    | some i =>
      dsimp only
      rw [ihRight _ _ _ hright]
      cases hr : right.sampleRecord (B - left.guide.resource i) K (fun node => second (1 + node)) with
      | none => rfl
      | some r =>
        dsimp only
        rw [ihLeft _ _ _ hleft]

theorem sampleRecord_seed_eq_blocks (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (bits : Fin (tree.seedWidths K).sum → Bool) :
    tree.sampleRecord B K (readSeedBlock (tree.seedWidths K) bits) =
      tree.sampleBlocks B K (fun j => bits (j.cast (tree.seedWidths_sum K).symm)) := by
  induction tree generalizing B with
  | @leaf n p family guide gamma =>
    let leafBits : Fin [3 * (n - 1 + K)].sum → Bool := bits
    have he := readSeedBlock_head (3 * (n - 1 + K)) [] leafBits
    change family.conditionalSample B K (readSeedBlock [3 * (n - 1 + K)] leafBits 0) = _
    rw [he]
    apply congrArg (fun reader => family.conditionalSample B K reader)
    apply congrArg finiteBitReader
    funext j
    congr 1
  | fork guide gamma left right ihLeft ihRight =>
    let root := 3 * (left.guideSize - 1 + K)
    let widths := right.seedWidths K ++ left.seedWidths K
    let allBits : Fin (root :: widths).sum → Bool := bits
    let restBits : Fin widths.sum → Bool :=
      fun j => allBits ⟨root + j.val, by simp only [List.sum_cons]; omega⟩
    let rightBits : Fin (right.seedWidths K).sum → Bool :=
      fun j => restBits ⟨j.val, by simp only [widths, List.sum_append]; omega⟩
    let leftBits : Fin (left.seedWidths K).sum → Bool :=
      fun j => restBits ⟨(right.seedWidths K).sum + j.val, by simp only [widths, List.sum_append]; omega⟩
    have hroot : readSeedBlock (root :: widths) allBits 0 =
        finiteBitReader (fun j : Fin root => allBits ⟨j.val, by simp only [List.sum_cons]; omega⟩) :=
      readSeedBlock_head root widths allBits
    have hrAll : ∀ budget : ℚ,
        right.sampleRecord budget K (fun node => readSeedBlock (root :: widths) allBits (1 + node)) =
          right.sampleBlocks budget K (fun j => rightBits (j.cast (right.seedWidths_sum K).symm)) := by
      intro budget
      calc
        _ = right.sampleRecord budget K (readSeedBlock (right.seedWidths K) rightBits) := by
          apply sampleRecord_congr_nodes
          intro node hn
          rw [readSeedBlock_cons_tail]
          exact readSeedBlock_append_left (right.seedWidths K) (left.seedWidths K) restBits node
            (by rw [seedWidths_length]; exact hn)
        _ = _ := ihRight budget rightBits
    have hlAll : ∀ budget : ℚ,
        left.sampleRecord budget K
            (fun node => readSeedBlock (root :: widths) allBits (1 + right.nodes + node)) =
          left.sampleBlocks budget K (fun j => leftBits (j.cast (left.seedWidths_sum K).symm)) := by
      intro budget
      calc
        _ = left.sampleRecord budget K (readSeedBlock (left.seedWidths K) leftBits) := by
          apply sampleRecord_congr_nodes
          intro node _
          rw [show 1 + right.nodes + node = 1 + ((right.seedWidths K).length + node) by rw [seedWidths_length]; omega]
          rw [readSeedBlock_cons_tail]
          exact readSeedBlock_append_right (right.seedWidths K) (left.seedWidths K) restBits node
        _ = _ := ihLeft budget leftBits
    let castBits : Fin (root + (right.totalBitBudget K + left.totalBitBudget K)) → Bool :=
      fun j => bits (j.cast (by
        simp only [root, seedWidths, List.sum_cons, List.sum_nil, List.sum_append, seedWidths_sum]
        omega))
    have hfirst : (fun j : Fin root => allBits ⟨j.val, by simp only [List.sum_cons]; omega⟩) =
        firstBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits := by
      funext j
      congr 1
    have hrightBits : (fun j => rightBits (j.cast (right.seedWidths_sum K).symm)) =
        firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
          (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits) := by
      funext j
      congr 1
    have hleftBits : (fun j => leftBits (j.cast (left.seedWidths_sum K).symm)) =
        secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
          (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits) := by
      funext j
      unfold leftBits restBits allBits secondBitBlock castBits
      apply congrArg bits
      apply Fin.ext
      change root + ((right.seedWidths K).sum + j.val) = root + (right.totalBitBudget K + j.val)
      rw [seedWidths_sum]
    unfold sampleRecord sampleBlocks
    change (match left.guide.syntheticSample right.guide B K (readSeedBlock (root :: widths) allBits 0) with
      | none => none
      | some i => match right.sampleRecord (B - left.guide.resource i) K
          (fun node => readSeedBlock (root :: widths) allBits (1 + node)) with
        | none => none
        | some r => match left.sampleRecord (B - right.resource r) K
            (fun node => readSeedBlock (root :: widths) allBits (1 + right.nodes + node)) with
          | none => none
          | some l => some (i, r, l)) = _
    rw [hroot]
    simp_rw [hrAll, hlAll]
    rw [hfirst, hrightBits, hleftBits]
    have hcast : (fun j : Fin (root + (right.totalBitBudget K + left.totalBitBudget K)) =>
        bits ((j.cast (by simp only [root, totalBitBudget]; omega)).cast
          ((fork guide gamma left right).seedWidths_sum K).symm)) = castBits := by
      funext j
      apply congrArg bits
      exact Fin.ext rfl
    change _ = (match left.guide.syntheticSample right.guide B K
      (finiteBitReader (firstBitBlock root (right.totalBitBudget K + left.totalBitBudget K)
        (fun j => bits ((j.cast (by simp only [root, totalBitBudget]; omega)).cast
          ((fork guide gamma left right).seedWidths_sum K).symm)))) with
      | none => none
      | some i => match right.sampleBlocks (B - left.guide.resource i) K
        (firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
          (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K)
            (fun j => bits ((j.cast (by simp only [root, totalBitBudget]; omega)).cast
              ((fork guide gamma left right).seedWidths_sum K).symm)))) with
        | none => none
        | some r => (left.sampleBlocks (B - right.resource r) K
          (secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
            (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K)
              (fun j => bits ((j.cast (by simp only [root, totalBitBudget]; omega)).cast
                ((fork guide gamma left right).seedWidths_sum K).symm))))).map (fun l => (i, r, l)))
    rw [hcast]
    cases hi : left.guide.syntheticSample right.guide B K
      (finiteBitReader (firstBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits)) with
    | none => rfl
    | some i =>
      dsimp only
      cases hr : right.sampleBlocks (B - left.guide.resource i) K
        (firstBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
          (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits)) with
      | none => rfl
      | some r =>
        dsimp only
        cases left.sampleBlocks (B - right.resource r) K
          (secondBitBlock (right.totalBitBudget K) (left.totalBitBudget K)
            (secondBitBlock root (right.totalBitBudget K + left.totalBitBudget K) castBits)) <;> rfl

theorem sampleFinite_eq_sampleBlocks (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (bits : Fin (tree.totalBitBudget K) → Bool) :
    tree.sampleFinite B K bits = tree.sampleBlocks B K bits := by
  unfold sampleFinite
  rw [sampleRecord_seed_eq_blocks]
  have he : (fun j : Fin (tree.totalBitBudget K) =>
      bits ((j.cast (tree.seedWidths_sum K).symm).cast (tree.seedWidths_sum K))) = bits := by
    funext j
    apply congrArg bits
    exact Fin.ext rfl
  rw [he]

end RationalWeightedGuideTree
end Blotto
