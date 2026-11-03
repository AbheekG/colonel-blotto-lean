import Blotto.RationalRoutingBitCost
import Blotto.RationalTerminalPacketMetadata

/-! The retained raw-list router prices each actual coefficient environment,
expression and label words, plus its nested loops, zero fill and patch traversal.
Payload copying of route arrays, physical addresses and ownership stay separate. -/

namespace Blotto.RationalTerminalPacking
open scoped BigOperators

def entryMetadataWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) (e : Fin n × GroupRoute i.groups.length) : ℕ :=
  match e.2.1 with
  | none => 0
  | some g =>
      let env := RationalLotteryAssemblyCode.environment (i.length e.1) (p.groups.read g).2
      rationalEnvironmentMetadataWork primitive env +
        RationalExpression.metadataAllowance c (RationalExpression.div (.input 0) (.input 1) : RationalExpression 2) env +
          4 * (binaryWordWidth (e.1.val + 1) + binaryWordWidth (g.val + 1)) +
            4 * primitive (binaryWordWidth (e.1.val + 1)) + 4 * primitive (binaryWordWidth (g.val + 1)) + 6

def entryMetadataBound (c n s : ℕ) : ℕ :=
  rationalEnvironmentMetadataBound c 2 (1 + 2 * s) + 4 * RationalExpression.metadataInstructionBound c 2 4 +
    (8 + 8 * c) * binaryWordWidth (n + 4) + 6

theorem entryMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hWidth : binaryWordWidth D ≤ s)
    (e : Fin n × GroupRoute i.groups.length) (he : e ∈ p.routeAssignments) :
    p.entryMetadataWork primitive c e ≤ entryMetadataBound c n s := by
  rcases (p.mem_routeAssignments e).mp he with ⟨g, _, hEq⟩
  have hOption : e.2.1 = some g := congrArg Prod.fst hEq
  have hEnv := RationalLotteryAssemblyCode.environmentMetadataWork_bound primitive c hPrimitive _ _ s
    ((h.length_height hD hB e.1).mono hWidth) ((h.total_height hD hB g).mono hWidth)
  have hExpr := RationalExpression.metadataAllowance_uniform_bound c
    (RationalExpression.div (.input 0) (.input 1) : RationalExpression 2)
    (RationalLotteryAssemblyCode.environment (i.length e.1) (i.partition.total g)) 2 4 le_rfl (by decide)
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hIndex := binaryWordWidth_mono (show e.1.val + 1 ≤ n + 4 by omega)
  have hGroup := binaryWordWidth_mono (show g.val + 1 ≤ n + 4 by omega)
  have hIndexPrice := (hPrimitive (binaryWordWidth (e.1.val + 1))).trans (Nat.mul_le_mul_left c hIndex)
  have hGroupPrice := (hPrimitive (binaryWordWidth (g.val + 1))).trans (Nat.mul_le_mul_left c hGroup)
  simp only [entryMetadataWork, hOption, p.total_correct]
  unfold entryMetadataBound
  nlinarith

def routingMetadataWork {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) : ℕ :=
  (p.routeAssignments.map (p.entryMetadataWork primitive c)).sum +
    indexedLoopMetadataBitWork primitive 0 n + indexedLoopMetadataBitWork primitive 0 p.routeAssignments.length +
      indexedLoopMetadataBitWork primitive 0 i.groups.length +
        ∑ g : Fin i.groups.length, indexedLoopMetadataBitWork primitive 0 (p.groups.read g).1.length

def routingMetadataBound (c n s : ℕ) : ℕ :=
  n * entryMetadataBound c n s + 5 * indexedLoopMetadataBound c n + indexedLoopMetadataBound c 3

theorem routingMetadataBound_mono_fields (c s : ℕ) : Monotone (fun n => routingMetadataBound c n s) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 4)
  have hEntry : entryMetadataBound c a s ≤ entryMetadataBound c b s := by
    unfold entryMetadataBound
    gcongr
  have hLoop := indexedLoopMetadataBound_mono c hab
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul hab hEntry) (Nat.mul_le_mul_left 5 hLoop)) _

theorem routingMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (D s : ℕ) (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (hWidth : binaryWordWidth D ≤ s) :
    p.routingMetadataWork primitive c ≤ routingMetadataBound c n s := by
  have hAssignments : (p.routeAssignments.map (p.entryMetadataWork primitive c)).sum ≤ n * entryMetadataBound c n s := by
    have hp := List.sum_le_sum (fun e he => p.entryMetadataWork_bound primitive c hPrimitive D s h hD hB hWidth e he)
    have he : (p.routeAssignments.map (fun _ => entryMetadataBound c n s)).sum = p.routeAssignments.length * entryMetadataBound c n s := by simp
    exact hp.trans (he ▸ Nat.mul_le_mul_right _ p.routeAssignments_length_le)
  have hZero := indexedLoopMetadataBitWork_bound primitive c hPrimitive n
  have hPatch := (indexedLoopMetadataBitWork_bound primitive c hPrimitive p.routeAssignments.length).trans
    (indexedLoopMetadataBound_mono c p.routeAssignments_length_le)
  have hCount : i.groups.length ≤ 3 := by rcases i.groups_count with h | h <;> omega
  have hGroups := (indexedLoopMetadataBitWork_bound primitive c hPrimitive i.groups.length).trans (indexedLoopMetadataBound_mono c hCount)
  have hMember : ∀ g : Fin i.groups.length, (p.groups.read g).1.length ≤ n := by
    intro g
    rw [p.members_correct]
    simpa only [RationalTerminalLotto.partition, Fintype.card_fin] using (i.partition.nodup g).length_le_card
  have hMembers : (∑ g : Fin i.groups.length, indexedLoopMetadataBitWork primitive 0 (p.groups.read g).1.length) ≤
      3 * indexedLoopMetadataBound c n := by
    calc
      _ ≤ ∑ _g : Fin i.groups.length, indexedLoopMetadataBound c n := Finset.sum_le_sum (fun g _ =>
        (indexedLoopMetadataBitWork_bound primitive c hPrimitive _).trans (indexedLoopMetadataBound_mono c (hMember g)))
      _ = i.groups.length * indexedLoopMetadataBound c n := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hCount
  unfold routingMetadataWork routingMetadataBound
  omega

end Blotto.RationalTerminalPacking
