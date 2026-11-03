import Blotto.GeneralPaperEqualSegmentCopyLifetime

/-! Complete prepared-cache copy reserve: old and returned cache owners,
all child array cursors, active scalar copies and exact partial/total native
work fields coexist. The original budget is a fixed number of additive
owners/scratch values, never one value per route or matrix coordinate. -/
namespace Blotto.GeneralPaperEqualPreparedCopyLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperEqualRetainedStorage
open GeneralPaperPositiveSegmentCompaction (compact count)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem owner {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (W : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l) (hl : (compact l).HeightAt s)
    (hc : ∀ j,RationalHeight (p.routes.table.read j).2 c) (hd : ∀ i,binaryWordWidth (p.counts.read i) ≤ d)
    (hp : ∀ x ∈ [p.D,p.rangeBits,p.midpointBits,p.midpointCount],natBits x ≤ P) :
    preparedFoot W p ≤ preparedProfile W n m (count l) s c d P (rationalWordWidth p.budget) := by
  have hRoutes := array_bound W (4 + binaryWordWidth m + 2 * c + 16 * W) (routeFoot W) p.routes.table
    (fun j => route_bound W _ (hc j))
  have hSegments := segment_bound W p.segments hl
  have hCounts := array_bound W (1 + d) natBits p.counts (fun i => Nat.add_le_add_left (hd i) 1)
  have hFields := fields_bound W P [p.D,p.rangeBits,p.midpointBits,p.midpointCount] hp
  change fields W _ ≤ 4 * (P + W) + 32 * W at hFields
  dsimp only [preparedFoot,preparedProfile]
  omega

def controls {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l) : List ℕ :=
  let routes := (GeneralPaperEqualRationalCopy.routes S A p.routes).2
  let segments := (GeneralPaperEqualRationalCopy.segments S A p.segments).2
  let counts := (GeneralPaperScalarTableCopy.run S A natBits p.counts).2
  let denominator := natBits p.D + 32 * (S + A + 1)
  let width := natBits p.rangeBits + 32 * (S + A + 1)
  let bits := natBits p.midpointBits + 32 * (S + A + 1)
  let midpoint := natBits p.midpointCount + 32 * (S + A + 1)
  let budget := rationalWordWidth p.budget + 32 * (S + A + 1)
  [n,m,count l,S,A,routes,segments,counts,denominator,width,bits,midpoint,budget,
    routes+segments,routes+segments+counts,routes+segments+counts+denominator,
    routes+segments+counts+denominator+width,routes+segments+counts+denominator+width+bits,
    routes+segments+counts+denominator+width+bits+midpoint,
    routes+segments+counts+denominator+width+bits+midpoint+budget,(GeneralPaperEqualPreparedCopy.run S A p).2]

def parentCap (S A n m r s c d P b : ℕ) : ℕ :=
  GeneralPaperEqualPreparedCopy.price S A n m r s c d P b + n + m + r + S + A

def window {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l)
    (q : ℕ) (hq : q ≤ n) (i : ℕ) (hi : i ≤ count l) (j : ℕ) (hj : j ≤ m) : ℕ :=
  preparedFoot S p + preparedFoot A (GeneralPaperEqualPreparedCopy.run S A p).1 +
    GeneralPaperEqualRouteCopyLifetime.window S A p.routes q hq +
    GeneralPaperEqualSegmentCopyLifetime.window S A p.segments i hi j hj +
    GeneralPaperScalarTableCopyLifetime.window S A natBits p.counts i hi +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits p.D +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits p.rangeBits +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits p.midpointBits +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A natBits p.midpointCount +
    GeneralPaperScalarTableCopyLifetime.scalarWindow S A rationalWordWidth p.budget +
    fields S (controls S A p) + 256 * (S + A + 1)

def profile (S A n m r s c d P b : ℕ) : ℕ :=
  preparedProfile S n m r s c d P b + preparedProfile A n m r s c d P b +
    GeneralPaperEqualRouteCopyLifetime.profile S A n m c +
    GeneralPaperEqualSegmentCopyLifetime.profile S A m r (1 + 2 * s) +
    GeneralPaperScalarTableCopyLifetime.profile S A r (r * (1 + d)) (1 + d) +
    4 * GeneralPaperScalarTableCopyLifetime.scalarProfile S A P +
    GeneralPaperScalarTableCopyLifetime.scalarProfile S A b +
    21 * (natBits (parentCap S A n m r s c d P b) + S) + 32 * S + 256 * (S + A + 1)

theorem all_cursors {n m r s c d P : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (S A : ℕ) (p : GeneralPaperEqualPreparedCache.Prepared G l) (hl : (compact l).HeightAt s)
    (hc : ∀ j,RationalHeight (p.routes.table.read j).2 c) (hd : ∀ i,binaryWordWidth (p.counts.read i) ≤ d)
    (hp : ∀ x ∈ [p.D,p.rangeBits,p.midpointBits,p.midpointCount],natBits x ≤ P)
    (hA : 1 ≤ A) (hIndexN : binaryWordWidth (n + 1) ≤ A)
    (hIndexM : binaryWordWidth (m + 1) ≤ A) (hIndexR : binaryWordWidth (count l + 1) ≤ A)
    (q : ℕ) (hq : q ≤ n) (i : ℕ) (hi : i ≤ count l) (j : ℕ) (hj : j ≤ m) :
    window S A p q hq i hi j hj ≤ profile S A n m (count l) s c d P (rationalWordWidth p.budget) := by
  have hSource := owner S p hl hc hd hp
  have hTarget : preparedFoot A (GeneralPaperEqualPreparedCopy.run S A p).1 ≤
      preparedProfile A n m (count l) s c d P (rationalWordWidth p.budget) := by
    rw [GeneralPaperEqualPreparedCopy.data]
    exact owner A p hl hc hd hp
  have hRoutes := GeneralPaperEqualRouteCopyLifetime.all_cursors S A p.routes hc hA hIndexN q hq
  have hSegments := GeneralPaperEqualSegmentCopyLifetime.all_cursors S A p.segments
    (fun a => by rw [p.segments.weight_correct]; exact rationalWordWidth_of_height (hl.1 a))
    (fun a b => by rw [p.segments.left_correct]; exact rationalWordWidth_of_height (hl.2 a b).1)
    (fun a b => by rw [p.segments.right_correct]; exact rationalWordWidth_of_height (hl.2 a b).2)
    hA hIndexM hIndexR i hi j hj
  have hCountPayload : ∀ a,natBits (p.counts.read a) ≤ 1 + d := fun a => Nat.add_le_add_left (hd a) 1
  have hCountSum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hCountPayload a)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hCountSum
  have hCounts := GeneralPaperScalarTableCopyLifetime.all_cursors S A (count l * (1 + d)) (1 + d)
    natBits p.counts hCountSum hCountPayload hA hIndexR i hi
  have hD := GeneralPaperScalarTableCopyLifetime.scalar_bound S A P natBits p.D (hp _ (by simp))
  have hR := GeneralPaperScalarTableCopyLifetime.scalar_bound S A P natBits p.rangeBits (hp _ (by simp))
  have hK := GeneralPaperScalarTableCopyLifetime.scalar_bound S A P natBits p.midpointBits (hp _ (by simp))
  have hN := GeneralPaperScalarTableCopyLifetime.scalar_bound S A P natBits p.midpointCount (hp _ (by simp))
  have hB := GeneralPaperScalarTableCopyLifetime.scalar_bound S A (rationalWordWidth p.budget)
    rationalWordWidth p.budget le_rfl
  have hWork := GeneralPaperEqualPreparedCopy.work S A p hl hc hd hp
  have hReturn : (GeneralPaperEqualPreparedCopy.run S A p).2 =
      (GeneralPaperEqualRationalCopy.routes S A p.routes).2 + (GeneralPaperEqualRationalCopy.segments S A p.segments).2 +
      (GeneralPaperScalarTableCopy.run S A natBits p.counts).2 + (natBits p.D + 32 * (S + A + 1)) +
      (natBits p.rangeBits + 32 * (S + A + 1)) + (natBits p.midpointBits + 32 * (S + A + 1)) +
      (natBits p.midpointCount + 32 * (S + A + 1)) + (rationalWordWidth p.budget + 32 * (S + A + 1)) +
      128 * (S + A + 1) := rfl
  have hf := fields_bound S (natBits (parentCap S A n m (count l) s c d P (rationalWordWidth p.budget)))
    (controls S A p) (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      dsimp only [controls] at ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold parentCap; omega)
  change fields S _ ≤ 21 * (natBits (parentCap S A n m (count l) s c d P (rationalWordWidth p.budget)) + S) + 32 * S at hf
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualPreparedCopyLifetime
