import Blotto.GeneralPaperCircleUnrolledChoice

/-! One native arithmetic sweep over ordered arc metadata. The returned
bin/next state is carried across arcs. Advance counts telescope to the
final bin, giving fewer than 2R advances over the entire draw. Native arc
table preparation and complete bit/output prices remain separate joins. -/
namespace Blotto.GeneralPaperCircleCursorSweep
open GeneralPaperCircleCell GeneralPaperCircleUnrolledChoice
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

structure Result where
  indices : List ℕ
  bin : ℕ
  next : ℕ
  advances : ℕ
  work : ℕ

def run (R W t : ℕ) : List (ℕ×ℕ) → ℕ → ℕ → Result
  | [],a,next => ⟨[],a,next,0,4⟩
  | (offset,length)::tail,a,next =>
    let left := 2*(t+offset)+1
    let right := 2*(t+offset+length)+1
    let advanced := GeneralPaperCircleBinAdvance.run (2*W) left (2*R) a next
    let chosen := select R (R*W) left right advanced.bin
    let later := run R W t tail advanced.bin advanced.next
    ⟨chosen::later.indices,later.bin,later.next,advanced.advances+later.advances,advanced.work+later.work+32⟩

theorem indices_length (R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) :
    (run R W t arcs a next).indices.length=arcs.length := by
  induction arcs generalizing a next with
  | nil => rfl
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    simpa only [run,List.length_cons] using congrArg (fun n => n+1) (ih _ _)

theorem bin_eq (R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) :
    (run R W t arcs a next).bin=a+(run R W t arcs a next).advances := by
  induction arcs generalizing a next with
  | nil => rfl
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    dsimp only [run]
    rw [ih,GeneralPaperCircleBinAdvance.bin_eq]
    omega

theorem next_invariant (R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) (hNext : next=(a+1)*(2*W)) :
    (run R W t arcs a next).next=((run R W t arcs a next).bin+1)*(2*W) := by
  induction arcs generalizing a next with
  | nil => exact hNext
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    dsimp only [run]
    exact ih _ _ (GeneralPaperCircleBinAdvance.next_invariant _ _ _ a next hNext)

theorem work_eq (R W t : ℕ) (arcs : List (ℕ×ℕ)) (a next : ℕ) :
    (run R W t arcs a next).work=12*(run R W t arcs a next).advances+36*arcs.length+4 := by
  induction arcs generalizing a next with
  | nil => rfl
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    dsimp only [run]
    rw [ih,GeneralPaperCircleBinAdvance.work_eq]
    simp only [List.length_cons]
    ring

theorem correct (R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ)) (a next : ℕ) (hA : a<2*R) (hNext : next=(a+1)*(2*W))
    (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W)
    (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1))
    (hLower : ∀ arc∈arcs,a*(2*W)<2*(t+arc.1)+1) :
    (run R W t arcs a next).indices=arcs.map (fun arc =>
      (choice R W hR hW (cell (R*W) (Nat.mul_pos hR hW) t arc.1) arc.2).val) ∧
      (run R W t arcs a next).bin<2*R := by
  induction arcs generalizing a next with
  | nil => exact ⟨rfl,hA⟩
  | cons arc tail ih =>
    rcases arc with ⟨offset,length⟩
    have hLength := hRanges (offset,length) (List.mem_cons_self)
    have hLow := hLower (offset,length) (List.mem_cons_self)
    have hU : t+offset<2*(R*W) := by omega
    let advanced := GeneralPaperCircleBinAdvance.run (2*W) (2*(t+offset)+1) (2*R) a next
    have hAdvance := GeneralPaperCircleOddGeometry.cursor_bin R W (t+offset) a next hR hW hU hNext hLow
    have hNx : advanced.next=(advanced.bin+1)*(2*W) :=
      GeneralPaperCircleBinAdvance.next_invariant _ _ _ _ _ hNext
    have hTailRanges : ∀ item∈tail,item.1+item.2≤R*W := fun item hm => hRanges item (List.mem_cons_of_mem _ hm)
    have hPair := List.pairwise_cons.mp hOrder
    have hTailLower : ∀ item∈tail,advanced.bin*(2*W)<2*(t+item.1)+1 := by
      intro item hm
      have hl := GeneralPaperCircleBinAdvance.lower (2*W) (2*(t+offset)+1) (2*R) a next hNext hLow
      have ho := hPair.1 item hm
      change advanced.bin*(2*W)<_ at hl
      omega
    have hi := ih advanced.bin advanced.next hAdvance.2 hNx hTailRanges hPair.2 hTailLower
    have hChoice := cursor_data R W hR hW t offset length a next ht hLength hNext hLow
    constructor
    · change select R (R*W) (2*(t+offset)+1) (2*(t+offset+length)+1) advanced.bin::
        (run R W t tail advanced.bin advanced.next).indices=_
      rw [hChoice,hi.1]
      rfl
    · exact hi.2

theorem total_advances (R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ))
    (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W) (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1)) :
    (run R W t arcs 0 (2*W)).advances<2*R := by
  have hc := correct R W t hR hW ht arcs 0 (2*W) (by omega) (by omega) hRanges hOrder
    (fun arc _ => by simp only [Nat.zero_mul];omega)
  rw [bin_eq,Nat.zero_add] at hc
  exact hc.2

theorem linear_work (R W t : ℕ) (hR : 0<R) (hW : 0<W) (ht : t<R*W)
    (arcs : List (ℕ×ℕ))
    (hRanges : ∀ arc∈arcs,arc.1+arc.2≤R*W) (hOrder : arcs.Pairwise (fun arc other => arc.1≤other.1)) :
    (run R W t arcs 0 (2*W)).work≤24*R+36*arcs.length+4 := by
  have ha := total_advances R W t hR hW ht arcs hRanges hOrder
  rw [work_eq]
  omega

end Blotto.GeneralPaperCircleCursorSweep
