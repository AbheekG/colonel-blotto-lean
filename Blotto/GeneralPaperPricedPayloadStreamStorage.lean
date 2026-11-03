import Blotto.GeneralPaperSourceStaticScanReachedRates

/-! Native list streams with arbitrary explicitly owned payloads. Current
optional values/segments remain retained, append copies only its current
segment, and one active callback reservation is reused. This instantiates
the actual existing filterMap/flatMap/map constructors without data changes. -/
namespace Blotto.GeneralPaperPricedPayloadStreamStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPricedListStream
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def optionFoot {β : Type*} (W : ℕ) (encode : β → ℕ) : Option β → ℕ
  | none => 1
  | some b => 1+encode b+32*W
def optionProfile (W P : ℕ) : ℕ := 1+P+32*W

theorem option_bound {β : Type*} (W P : ℕ) (encode : β → ℕ) (a : Option β)
    (ha : ∀ b,a=some b → encode b≤P) : optionFoot W encode a≤optionProfile W P := by
  cases a with
  | none => dsimp only [optionFoot,optionProfile]; omega
  | some b => have h := ha b rfl; dsimp only [optionFoot,optionProfile]; omega

def listProfile (W P N : ℕ) : ℕ := N*(P+2*W)+32*W
def filterWork (W C N : ℕ) : ℕ := (C+8*W)*N+2*W
def filterCap (W C N : ℕ) : ℕ := N+1+3*filterWork W C N+C+8*W
def filterFrameProfile (W P C N : ℕ) : ℕ :=
  optionProfile W P+8*(natBits (filterCap W C N)+W)+160*W

def filterFrame {α β : Type*} (W : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) : List α → ℕ
  | [] => optionFoot W encode none+fields W [0,2*W]+128*W
  | a::rest =>
    let current := evaluate a
    let child := filterMap W evaluate rest
    let result := filterMap W evaluate (a::rest)
    optionFoot W encode current.1+
      fields W [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W]+128*W

theorem filter_frame {α β : Type*} (W P C N : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → encode t≤P) :
    filterFrame W encode evaluate xs≤filterFrameProfile W P C N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (filterCap W C N)) [0,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> unfold filterCap filterWork <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (filterCap W C N)+W)+32*W at hf
    change 1+GeneralPaperEncodedScalarStorage.fields W [0,2*W]+128*W≤_
    unfold filterFrameProfile optionProfile
    omega
  | cons a rest =>
    let current := evaluate a
    let child := filterMap W evaluate rest
    let result := filterMap W evaluate (a::rest)
    have hCurrent : current.2≤C := hC a List.mem_cons_self
    have hChild := (filterMap_work W C evaluate rest (fun b hb => hC b (List.mem_cons_of_mem _ hb))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (show rest.length≤N by simp only [List.length_cons] at hn; omega)) _)
    have hResult := (filterMap_work W C evaluate (a::rest) hC).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)
    change child.2≤filterWork W C N at hChild
    change result.2≤filterWork W C N at hResult
    have hChildLen := (filterMap_length W evaluate rest).trans (show rest.length≤N by simp only [List.length_cons] at hn; omega)
    have hResultLen := (filterMap_length W evaluate (a::rest)).trans hn
    change child.1.length≤N at hChildLen
    change result.1.length≤N at hResultLen
    have hRoot := option_bound W P encode current.1 (hR a List.mem_cons_self)
    have hf := fields_bound W (natBits (filterCap W C N))
      [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W] (by
        intro b hb
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold filterCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (filterCap W C N)+W)+32*W at hf
    change optionFoot W encode current.1+GeneralPaperEncodedScalarStorage.fields W
      [(a::rest).length,child.1.length,result.1.length,current.2,child.2,result.2,current.2+child.2,8*W]+128*W≤_
    unfold filterFrameProfile
    omega

def filterFrames {α β : Type*} (W : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) : List α → ℕ
  | [] => filterFrame W encode evaluate []
  | a::rest => filterFrame W encode evaluate (a::rest)+filterFrames W encode evaluate rest

theorem filter_frames {α β : Type*} (W P C N : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → encode t≤P) :
    filterFrames W encode evaluate xs≤(xs.length+1)*filterFrameProfile W P C N := by
  induction xs with
  | nil => simpa only [filterFrames,List.length_nil,Nat.zero_add,Nat.one_mul] using filter_frame W P C N encode evaluate [] hn hC hR
  | cons a rest ih =>
    have hc := ih (by simp only [List.length_cons] at hn; omega) (fun b hb => hC b (List.mem_cons_of_mem _ hb))
      (fun b hb => hR b (List.mem_cons_of_mem _ hb))
    exact (Nat.add_le_add (filter_frame W P C N encode evaluate (a::rest) hn hC hR) hc).trans_eq
      (by simp only [List.length_cons]; ring)

def filterWindow {α β : Type*} (W : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) (space : α → ℕ) (active : Option α) (xs : List α) : ℕ :=
  filterFrames W encode evaluate xs+listFootprint W encode (filterMap W evaluate xs).1+GeneralPaperPricedListStreamStorage.activeSpace space active
def filterProfile (W P C N Q : ℕ) : ℕ := (N+1)*filterFrameProfile W P C N+listProfile W P N+Q

theorem filter_bounded {α β : Type*} (W P C N Q : ℕ) (encode : β → ℕ) (evaluate : α → Option β×ℕ) (space : α → ℕ) (active : Option α) (xs : List α)
    (hn : xs.length≤N) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t,(evaluate a).1=some t → encode t≤P) (hQ : ∀ a∈xs,space a≤Q)
    (ha : ∀ a,active=some a → a∈xs) : filterWindow W encode evaluate space active xs≤filterProfile W P C N Q := by
  have hFrames := (filter_frames W P C N encode evaluate xs hn hC hR).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hLen := (filterMap_length W evaluate xs).trans hn
  have hWord : ∀ t∈(filterMap W evaluate xs).1,encode t≤P := by
    intro t ht
    rw [filterMap_data] at ht
    obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp ht
    exact hR a ha t he
  have hOut := (list_bound W (P) encode _ hWord).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  change listFootprint W encode (filterMap W evaluate xs).1≤listProfile W P N at hOut
  have hActive := GeneralPaperPricedListStreamStorage.active_bound Q space active xs hQ ha
  exact Nat.add_le_add (Nat.add_le_add hFrames hOut) hActive

def flatWork (W B C N : ℕ) : ℕ := (C+(8*B+8)*W)*N+2*W
def flatCap (W B C N : ℕ) : ℕ := N+N*B+B+1+3*flatWork W B C N+C+(8*B+8)*W
def flatFrameProfile (W P B C N : ℕ) : ℕ :=
  listProfile W P B+(2*B*W+32*W)+10*(natBits (flatCap W B C N)+W)+160*W

def flatFrame {α β : Type*} (W copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) : List α → ℕ
  | [] => fields W [0,2*W]+128*W
  | a::rest =>
    let current := evaluate a
    let child := flatMap W evaluate rest
    let result := flatMap W evaluate (a::rest)
    let append := (8*current.1.length+8)*W
    listFootprint W encode current.1+GeneralPaperBorrowedListStorage.footprint W (current.1.take copied)+
      fields W [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append]+128*W

theorem flat_frame {α β : Type*} (W P B C N copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,encode t≤P) : flatFrame W copied encode evaluate xs≤flatFrameProfile W P B C N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (flatCap W B C N)) [0,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl <;> unfold flatCap flatWork <;> omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (flatCap W B C N)+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W [0,2*W]+128*W≤_
    unfold flatFrameProfile
    omega
  | cons a rest =>
    let current := evaluate a
    let child := flatMap W evaluate rest
    let result := flatMap W evaluate (a::rest)
    let append := (8*current.1.length+8)*W
    have hCurrent : current.2≤C := hC a List.mem_cons_self
    have hCurrentLen : current.1.length≤B := hB a List.mem_cons_self
    have hChild := (flatMap_work W B C evaluate rest (fun b hb => hB b (List.mem_cons_of_mem _ hb))
      (fun b hb => hC b (List.mem_cons_of_mem _ hb))).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (show rest.length≤N by simp only [List.length_cons] at hn; omega)) _)
    have hResult := (flatMap_work W B C evaluate (a::rest) hB hC).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _)
    change child.2≤flatWork W B C N at hChild
    change result.2≤flatWork W B C N at hResult
    have hChildLen := (flatMap_length W B evaluate rest (fun b hb => hB b (List.mem_cons_of_mem _ hb))).trans
      (Nat.mul_le_mul_right B (show rest.length≤N by simp only [List.length_cons] at hn; omega))
    have hResultLen := (flatMap_length W B evaluate (a::rest) hB).trans (Nat.mul_le_mul_right B hn)
    change child.1.length≤N*B at hChildLen
    change result.1.length≤N*B at hResultLen
    have hAppend : append≤(8*B+8)*W := Nat.mul_le_mul_right W (by omega)
    have hShape : result.2=current.2+child.2+append := rfl
    have hPayload := (list_bound W (P) encode current.1
      (fun t ht => hR a List.mem_cons_self t ht)).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCurrentLen) _)
    change listFootprint W encode current.1≤listProfile W P B at hPayload
    have hCopy := GeneralPaperBorrowedListStorage.bounded W B (current.1.take copied)
      (by simp only [List.length_take]; omega)
    have hf := fields_bound W (natBits (flatCap W B C N))
      [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append] (by
        intro b hb
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
        rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals unfold flatCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤10*(natBits (flatCap W B C N)+W)+32*W at hf
    change listFootprint W encode current.1+GeneralPaperBorrowedListStorage.footprint W (current.1.take copied)+
      GeneralPaperEncodedScalarStorage.fields W [(a::rest).length,current.1.length,child.1.length,result.1.length,current.2,child.2,result.2,append,
        current.2+child.2,current.2+child.2+append]+128*W≤_
    unfold flatFrameProfile
    omega

def flatFrames {α β : Type*} (W copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) : List α → ℕ
  | [] => flatFrame W copied encode evaluate []
  | a::rest => flatFrame W copied encode evaluate (a::rest)+flatFrames W copied encode evaluate rest

theorem flat_frames {α β : Type*} (W P B C N copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,encode t≤P) : flatFrames W copied encode evaluate xs≤(xs.length+1)*flatFrameProfile W P B C N := by
  induction xs with
  | nil => simpa only [flatFrames,List.length_nil,Nat.zero_add,Nat.one_mul] using flat_frame W P B C N copied encode evaluate [] hn hB hC hR
  | cons a rest ih =>
    have hc := ih (by simp only [List.length_cons] at hn; omega) (fun b hb => hB b (List.mem_cons_of_mem _ hb))
      (fun b hb => hC b (List.mem_cons_of_mem _ hb)) (fun b hb => hR b (List.mem_cons_of_mem _ hb))
    exact (Nat.add_le_add (flat_frame W P B C N copied encode evaluate (a::rest) hn hB hC hR) hc).trans_eq
      (by simp only [List.length_cons]; ring)

def flatWindow {α β : Type*} (W copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) (space : α → ℕ) (active : Option α) (xs : List α) : ℕ :=
  flatFrames W copied encode evaluate xs+listFootprint W encode (flatMap W evaluate xs).1+GeneralPaperPricedListStreamStorage.activeSpace space active
def flatProfile (W P B C N Q : ℕ) : ℕ := (N+1)*flatFrameProfile W P B C N+listProfile W P (N*B)+Q

theorem flat_bounded {α β : Type*} (W P B C N Q copied : ℕ) (encode : β → ℕ) (evaluate : α → List β×ℕ) (space : α → ℕ) (active : Option α) (xs : List α)
    (hn : xs.length≤N) (hB : ∀ a∈xs,(evaluate a).1.length≤B) (hC : ∀ a∈xs,(evaluate a).2≤C)
    (hR : ∀ a∈xs,∀ t∈(evaluate a).1,encode t≤P) (hQ : ∀ a∈xs,space a≤Q)
    (ha : ∀ a,active=some a → a∈xs) : flatWindow W copied encode evaluate space active xs≤flatProfile W P B C N Q := by
  have hFrames := (flat_frames W P B C N copied encode evaluate xs hn hB hC hR).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hLen := (flatMap_length W B evaluate xs hB).trans (Nat.mul_le_mul_right B hn)
  have hWord : ∀ t∈(flatMap W evaluate xs).1,encode t≤P := by
    intro t ht
    rw [flatMap_data] at ht
    obtain ⟨a,ha,he⟩ := List.mem_flatMap.mp ht
    exact hR a ha t he
  have hOut := (list_bound W (P) encode _ hWord).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  change listFootprint W encode (flatMap W evaluate xs).1≤listProfile W P (N*B) at hOut
  have hActive := GeneralPaperPricedListStreamStorage.active_bound Q space active xs hQ ha
  exact Nat.add_le_add (Nat.add_le_add hFrames hOut) hActive

def mapWindow {α β : Type*} (W : ℕ) (encode : β → ℕ) (evaluate : α → β×ℕ)
    (space : α → ℕ) (active : Option α) (xs : List α) : ℕ :=
  filterWindow W encode (fun a => let c := evaluate a; (some c.1,c.2)) space active xs

theorem map_bounded {α β : Type*} (W P C N Q : ℕ) (encode : β → ℕ) (evaluate : α → β×ℕ)
    (space : α → ℕ) (active : Option α) (xs : List α) (hn : xs.length≤N)
    (hC : ∀ a∈xs,(evaluate a).2≤C) (hP : ∀ a∈xs,encode (evaluate a).1≤P)
    (hQ : ∀ a∈xs,space a≤Q) (ha : ∀ a,active=some a → a∈xs) :
    mapWindow W encode evaluate space active xs≤filterProfile W P C N Q := by
  exact filter_bounded W P C N Q encode _ space active xs hn hC
    (by intro a ha b hb; cases hb; exact hP a ha) hQ ha

end Blotto.GeneralPaperPricedPayloadStreamStorage
