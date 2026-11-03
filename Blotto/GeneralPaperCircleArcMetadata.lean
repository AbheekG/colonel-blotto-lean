import Blotto.GeneralPaperCircleCursorSweep

/-! Native one-pass arc metadata preparation from retained integer
weights. Prefix offsets are accumulated, never queried from an input
encoding or supplied as an ordered-arc oracle. List construction is linear. -/
namespace Blotto.GeneralPaperCircleArcMetadata
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Result where
  arcs : List (ℕ×ℕ)
  total : ℕ

def run (price : ℕ → ℕ) (W R : ℕ) : List ℕ → ℕ → Result × ℕ
  | [],offset => (⟨[],offset⟩,16*W+price (GeneralPaperNaturalPrimitivePrice.word offset))
  | w::tail,offset =>
    let length := R*w
    let next := offset+length
    let later := run price W R tail next
    (⟨(offset,length)::later.1.arcs,later.1.total⟩,later.2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) R w+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) offset length+
      price (GeneralPaperNaturalPrimitivePrice.word offset)+32*W)

theorem length (price : ℕ → ℕ) (W R : ℕ) (weights : List ℕ) (offset : ℕ) :
    (run price W R weights offset).1.arcs.length=weights.length := by
  induction weights generalizing offset with
  | nil => rfl
  | cons w tail ih => simpa only [run,List.length_cons] using congrArg (fun n => n+1) (ih _)

theorem total (price : ℕ → ℕ) (W R : ℕ) (weights : List ℕ) (offset : ℕ) :
    (run price W R weights offset).1.total=offset+R*weights.sum := by
  induction weights generalizing offset with
  | nil => simp only [run,List.sum_nil,Nat.mul_zero,Nat.add_zero]
  | cons w tail ih =>
    dsimp only [run]
    rw [ih]
    simp only [List.sum_cons]
    ring

theorem starts_ge (price : ℕ → ℕ) (W R : ℕ) (weights : List ℕ) (offset : ℕ) :
    ∀ arc∈(run price W R weights offset).1.arcs,offset≤arc.1 := by
  induction weights generalizing offset with
  | nil => simp only [run,List.not_mem_nil,false_implies,forall_const]
  | cons w tail ih =>
    intro arc hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_rfl
    · exact (Nat.le_add_right offset (R*w)).trans (ih _ arc hm)

theorem ranges (price : ℕ → ℕ) (W R : ℕ) (weights : List ℕ) (offset : ℕ) :
    ∀ arc∈(run price W R weights offset).1.arcs,arc.1+arc.2≤(run price W R weights offset).1.total := by
  induction weights generalizing offset with
  | nil => simp only [run,List.not_mem_nil,false_implies,forall_const]
  | cons w tail ih =>
    intro arc hm
    rcases List.mem_cons.mp hm with rfl | hm
    · dsimp only [run]
      rw [total]
      exact Nat.le_add_right _ _
    · exact ih _ arc hm

theorem ordered (price : ℕ → ℕ) (W R : ℕ) (weights : List ℕ) (offset : ℕ) :
    (run price W R weights offset).1.arcs.Pairwise (fun arc other => arc.1≤other.1) := by
  induction weights generalizing offset with
  | nil => exact List.Pairwise.nil
  | cons w tail ih =>
    apply List.Pairwise.cons
    · intro arc hm
      exact (Nat.le_add_right offset (R*w)).trans (starts_ge price W R tail (offset+R*w) arc hm)
    · exact ih _

theorem models_data (price price' : ℕ → ℕ) (W W' R : ℕ) (weights : List ℕ) (offset : ℕ) :
    (run price W R weights offset).1=(run price' W' R weights offset).1 := by
  induction weights generalizing offset with
  | nil => rfl
  | cons w tail ih => dsimp only [run];rw [ih]

theorem work_bound (price : ℕ → ℕ) (hMono : Monotone price) (W R : ℕ) (weights : List ℕ) (offset M : ℕ)
    (hR : R≤M) (hTotal : offset+R*weights.sum≤M) (hWeights : ∀ w∈weights,w≤M) :
    (run price W R weights offset).2≤(weights.length+1)*(64*W+8*price (1+binaryWordWidth M)) := by
  let P := price (1+binaryWordWidth M)
  induction weights generalizing offset with
  | nil =>
    have hOff : offset≤M := by simpa only [List.sum_nil,Nat.mul_zero,Nat.add_zero] using hTotal
    have hp := hMono (Nat.add_le_add_left (binaryWordWidth_mono hOff) 1)
    change 16*W+price (GeneralPaperNaturalPrimitivePrice.word offset)≤(0+1)*(64*W+8*P)
    change price (GeneralPaperNaturalPrimitivePrice.word offset)≤P at hp
    omega
  | cons w tail ih =>
    have hWgt := hWeights w List.mem_cons_self
    have hTail : offset+R*w+R*tail.sum≤M := by
      simp only [List.sum_cons] at hTotal
      nlinarith only [hTotal]
    have hOff : offset≤M := by omega
    have hLen : R*w≤M := by omega
    have hNext : offset+R*w≤M := by omega
    have hIh := ih (offset+R*w) hTail (fun w hm => hWeights w (List.mem_cons_of_mem _ hm))
    have hMul := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) R w M hR hWgt hLen
    have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) offset (R*w) M hOff hLen hNext
    have hp := hMono (Nat.add_le_add_left (binaryWordWidth_mono hOff) 1)
    change price (GeneralPaperNaturalPrimitivePrice.word offset)≤P at hp
    change (run price W R tail (offset+R*w)).2+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) R w+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) offset (R*w)+
      price (GeneralPaperNaturalPrimitivePrice.word offset)+32*W≤_
    simp only [List.length_cons]
    change (run price W R tail (offset+R*w)).2≤(tail.length+1)*(64*W+8*P) at hIh
    nlinarith only [hIh,hMul,hAdd,hp]

end Blotto.GeneralPaperCircleArcMetadata
