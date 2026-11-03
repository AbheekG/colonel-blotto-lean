import Blotto.GeneralPaperEqualBooleanCopyLifetime

/-! The actual retained route-table copy has distinct source and target
route-record encodings, one active scalar route copy and all wrapper prices.
No n-fold original budget payload enters this table. -/
namespace Blotto.GeneralPaperEqualRouteCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperEqualRetainedStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def payload (A m c : ℕ) : ℕ := 4 + binaryWordWidth m + 2 * c + 16 * A
def parentCap (S A n m c : ℕ) : ℕ := GeneralPaperEqualRationalCopy.routesPrice S A n m c + n + m + S + A + 64 * (S + A + 1)

def window {n m : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ) (source : PreparedGroupOutput G)
    (j : ℕ) (hj : j ≤ n) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.window S A (routeFoot S) (routeFoot A)
    (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table
    (fun i => GeneralPaperScalarTableCopyLifetime.scalarWindow S A (routeFoot A) (source.table.read i)) j hj +
    fields S [n,m,S,A,
      (GeneralPaperReferenceCopy.array S A (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table).2,
      (GeneralPaperEqualRationalCopy.routes S A source).2,64 * (S + A + 1)] + 128 * (S + A + 1)

def profile (S A n m c : ℕ) : ℕ :=
  GeneralPaperReferenceArrayCopyLifetime.profile S A (arrayProfile S n (payload S m c))
    (n * payload A m c) (payload A m c) n (payload A m c + 32 * (S + A + 1))
    (GeneralPaperScalarTableCopyLifetime.scalarProfile S A (payload A m c)) +
    7 * (natBits (parentCap S A n m c) + S) + 32 * S + 128 * (S + A + 1)

theorem all_cursors {n m c : ℕ} {G : RationalProportionalGroups n m} (S A : ℕ)
    (source : PreparedGroupOutput G) (h : ∀ i,RationalHeight (source.table.read i).2 c)
    (hA : 1 ≤ A) (hIndex : binaryWordWidth (n + 1) ≤ A) (j : ℕ) (hj : j ≤ n) :
    window S A source j hj ≤ profile S A n m c := by
  have hP : ∀ i,routeFoot A (source.table.read i) ≤ payload A m c := fun i => route_bound A _ (h i)
  have hB := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hP i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hB
  have hFill := GeneralPaperReferenceArrayCopyLifetime.all_cursors S A _ (n * payload A m c)
    (payload A m c) (payload A m c + 32 * (S + A + 1))
    (GeneralPaperScalarTableCopyLifetime.scalarProfile S A (payload A m c))
    (routeFoot S) (routeFoot A) (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table
    (fun i => GeneralPaperScalarTableCopyLifetime.scalarWindow S A (routeFoot A) (source.table.read i))
    (array_bound S _ _ source.table (fun i => route_bound S _ (h i))) hB hP
    (fun i => Nat.add_le_add_right (hP i) _)
    (fun i => GeneralPaperScalarTableCopyLifetime.scalar_bound S A _ _ _ (hP i)) hA hIndex j hj
  have hWork := GeneralPaperEqualRationalCopy.routes_work S A source h
  have hReturn : (GeneralPaperEqualRationalCopy.routes S A source).2 =
      (GeneralPaperReferenceCopy.array S A (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table).2 +
      64 * (S + A + 1) := rfl
  have hf := fields_bound S (natBits (parentCap S A n m c))
    [n,m,S,A,
      (GeneralPaperReferenceCopy.array S A (GeneralPaperReferenceCopy.scalar S A (routeFoot A)) source.table).2,
      (GeneralPaperEqualRationalCopy.routes S A source).2,64 * (S + A + 1)] (by
        intro a ha
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap; omega)
  change fields S _ ≤ 7 * (natBits (parentCap S A n m c) + S) + 32 * S at hf
  dsimp only [window,profile]
  dsimp only [payload] at hFill ⊢
  omega

end Blotto.GeneralPaperEqualRouteCopyLifetime
