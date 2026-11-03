import Blotto.GeneralPaperRayAffineComparison

/-! Actual per-score pair crossing batches. The runtime visits at most
(S+1)*K*K ordered pairs of affine predecessor candidates; parallel pairs
contribute nothing, and repeated roots are left for sort/dedup. There is
no whole-tuple enumeration.
-/
namespace Blotto.GeneralPaperRayCrossingPairs
open GeneralPaperRayAffine GeneralPaperRayAffineComparison
set_option autoImplicit false
set_option maxHeartbeats 2500000

def crossing (a b : Affine) : Option ℚ :=
  if a.slope=b.slope then none else some (difference a b).crossing

def optional : Option Affine → Option Affine → Option ℚ
  | some a,some b => crossing a b
  | _,_ => none

def pairs {i : Type*} (options : i → Option Affine) (xs : List i) : List ℚ :=
  xs.flatMap (fun a => xs.filterMap (fun b => optional (options a) (options b)))

def batch {S K : ℕ} (options : Fin (S+1) → Fin K → Option Affine) : List ℚ :=
  (List.finRange (S+1)).flatMap (fun s => pairs (options s) (List.finRange K))

theorem crossing_eq (a b : Affine) (h : a.slope≠b.slope) : crossing a b=some (difference a b).crossing := by
  simp only [crossing,h,ite_false]

theorem crossing_value (a b : Affine) (h : a.slope≠b.slope) (t : ℚ) :
    a.value t=b.value t ↔ t=(difference a b).crossing := by
  rw [←sub_eq_zero,←difference_value]
  exact zero_iff _ (sub_ne_zero.mpr h) t

theorem pairs_complete {i : Type*} (options : i → Option Affine) (xs : List i)
    (a b : i) (ha : a∈xs) (hb : b∈xs) (f g : Affine)
    (hf : options a=some f) (hg : options b=some g) (hSlope : f.slope≠g.slope) :
    (difference f g).crossing∈pairs options xs := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_filterMap.mpr ⟨b,hb,?_⟩⟩
  simp only [hf,hg,optional,crossing_eq f g hSlope]

theorem batch_complete {S K : ℕ} (options : Fin (S+1) → Fin K → Option Affine)
    (s : Fin (S+1)) (a b : Fin K) (f g : Affine)
    (hf : options s a=some f) (hg : options s b=some g) (hSlope : f.slope≠g.slope) :
    (difference f g).crossing∈batch options := by
  exact List.mem_flatMap.mpr ⟨s,List.mem_finRange _,pairs_complete (options s) (List.finRange K)
    a b (List.mem_finRange _) (List.mem_finRange _) f g hf hg hSlope⟩

theorem pairs_length {i : Type*} (options : i → Option Affine) (xs : List i) :
    (pairs options xs).length≤xs.length*xs.length := by
  have hh := List.sum_le_sum (fun a (_ : a∈xs) => List.length_filterMap_le (f := fun b => optional (options a) (options b)) (l := xs))
  simpa only [pairs,List.length_flatMap,List.sum_replicate,List.map_const',nsmul_eq_mul,Nat.cast_id] using hh

theorem batch_length {S K : ℕ} (options : Fin (S+1) → Fin K → Option Affine) :
    (batch options).length≤(S+1)*(K*K) := by
  have hh := List.sum_le_sum (fun s (_ : s∈List.finRange (S+1)) => pairs_length (options s) (List.finRange K))
  simpa only [batch,List.length_flatMap,List.length_finRange,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id] using hh

end Blotto.GeneralPaperRayCrossingPairs
