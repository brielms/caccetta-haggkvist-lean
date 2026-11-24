import checkpoints.shen_extension.InducedPrimeTransition
import LeanCH.BR.BRWeightedThirdExterior

/-! Obstructions in a circular placement of the actual integer vertex weights. -/
namespace LeanCH.BR.ShenCircle
open BRq2 BRq3 BR45 ShenPrimeTransition WeightedSD

abbrev total (V : Finset ℕ) (w : ℕ → ℕ) := ∑ i ∈ V, w i

def heads (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℕ) (v : ℕ) :=
  ∑ i ∈ outN D V v, w i

private theorem score_eq {q D V w i} :
    score q D V w i = w i + q * heads D V w i := by
  simp [score,heads,outN,Finset.sum_filter]

/-- A block cannot contain a whole orbit of q equally spaced slots. -/
theorem width_bound {q D V w} (hq : 2 ≤ q) (hf : QFree D V q)
    (strict : Strict q D V w) {i} (hi : i ∈ V) :
    q*w i + total V w < q*total V w := by
  have high := nat_strict.mp strict i hi
  rw [score_eq] at high
  have wi := Finset.single_le_sum (f:=w) (fun _ _ => Nat.zero_le _) hi
  have ne : (outN D V i).Nonempty := by
    by_contra empty
    rw [heads,Finset.not_nonempty_iff_eq_empty.mp empty,Finset.sum_empty,Nat.mul_zero,Nat.add_zero] at high
    omega
  obtain ⟨j,hj⟩ := ne
  obtain ⟨jV,ij⟩ := mem_outN.mp hj
  have diff : i ≠ j := by rintro rfl; exact loopfree hf (by omega) hi ij
  have iMiss : i ∉ outN D V j := fun h => digonfree hf hq hi jV ij (mem_outN.mp h).2
  have jMiss : j ∉ outN D V j := fun h => loopfree hf (by omega) jV (mem_outN.mp h).2
  have sub : insert i (insert j (outN D V j)) ⊆ V :=
    Finset.insert_subset hi (Finset.insert_subset jV (Finset.filter_subset _ _))
  have bound := Finset.sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (by simpa [diff] using iMiss),Finset.sum_insert jMiss] at bound
  have hjHigh := nat_strict.mp strict j jV
  rw [score_eq] at hjHigh
  change w i + (w j + heads D V w j) ≤ total V w at bound
  have expanded := Nat.mul_le_mul_left q bound
  simp only [Nat.mul_add] at expanded
  have cost : w j ≤ q * w j := by simpa using Nat.mul_le_mul_right (w j) (show 1≤q by omega)
  change total V w < _ at hjHigh
  omega

/-- Slots numbered from zero. The cut is at a boundary between labels.
Every label occupies one contiguous block of q times its weight. -/
structure Blocks (q : ℕ) (V : Finset ℕ) (w : ℕ → ℕ) where
  start : ℕ → ℕ
  owner : ℕ → ℕ
  valid : ∀ x, x < q * total V w → owner x ∈ V
  interval : ∀ x, x < q * total V w →
    start (owner x) ≤ x ∧ x < start (owner x) + q*w (owner x)
  fills : ∀ i ∈ V, ∀ d < q*w i,
    start i+d < q*total V w ∧ owner (start i+d)=i

/-- Append a block at the cut. Repeated insertion realizes any chosen ordering. -/
def Blocks.append {q V w} (B : Blocks q V w) (i : ℕ) (fresh : i ∉ V) :
    Blocks q (insert i V) w := by
  classical
  let N := q*total V w
  have size : q*total (insert i V) w = N+q*w i := by
    simp [total,Finset.sum_insert fresh,N,Nat.mul_add,Nat.add_comm]
  refine ⟨fun j => if j=i then N else B.start j,fun x => if x<N then B.owner x else i,?_,?_,?_⟩
  · intro x _
    split_ifs with lt
    · exact Finset.mem_insert_of_mem (B.valid x lt)
    · exact Finset.mem_insert_self _ _
  · intro x hx
    rw [size] at hx
    by_cases lt : x<N
    · have ne : B.owner x ≠ i := fun eq => fresh (eq ▸ B.valid x lt)
      simpa [lt,ne] using B.interval x lt
    · simp [lt]; omega
  · intro j hj d hd
    rcases Finset.mem_insert.mp hj with rfl | old
    · simp only [ite_true,size]
      exact ⟨by omega,by simp [show ¬N+d<N by omega]⟩
    · have ne : j≠i := fun eq => fresh (eq ▸ old)
      have ⟨less,own⟩ := B.fills j old d hd
      change B.start j+d < N at less
      simp [ne,size,less,own]; omega

theorem blocks_exist (q : ℕ) (V : Finset ℕ) (w : ℕ → ℕ) : Nonempty (Blocks q V w) := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨⟨fun _ => 0,fun _ => 0,by simp [total],by simp [total],by simp⟩⟩
  | insert i V fresh ih => exact ⟨ih.some.append i fresh⟩

private theorem compressed_walk {D U} (f : ℕ → ℕ) {k : ℕ}
    (inside : ∀ j ≤ k, f j ∈ U)
    (step : ∀ j < k, f j = f (j+1) ∨ D (f j) (f (j+1)) = true) :
    ∃ l ≤ k, Walk D U (f 0) (f k) l ∧ (l = 0 → ∀ j ≤ k, f j = f 0) := by
  induction k with
  | zero => exact ⟨0,le_rfl,.refl _,by simp⟩
  | succ k ih =>
    obtain ⟨l,hl,p,flat⟩ := ih (fun _ h => inside _ (by omega)) (fun _ h => step _ (by omega))
    rcases step k (by omega) with eq | edge
    · refine ⟨l,by omega,eq ▸ p,?_⟩
      intro zero j hj
      by_cases h : j ≤ k
      · exact flat zero j h
      · rw [show j = k+1 by omega,← eq]
        exact flat zero k le_rfl
    · exact ⟨l+1,by omega,p.snoc (inside _ le_rfl) edge,by omega⟩

def blocked (D : CH.Digraph) (i j : ℕ) : Prop := i ≠ j ∧ D i j ≠ true

open Classical in
noncomputable def interiorPhases {q V w} (B : Blocks q V w) (D : CH.Digraph) : Finset ℕ :=
  (Finset.range (total V w)).filter fun p => ∃ k < q,
    let x := p+k*total V w
    let i := B.owner x
    x < B.start i + (q*w i - (w i-1)) ∧
      blocked D i (B.owner ((x+total V w) % (q*total V w)))

private theorem orbit_break {q D V w} (hq : 2 ≤ q) (hf : QFree D V q)
    (strict : Strict q D V w) (B : Blocks q V w) {p} (hp : p < total V w) :
    ∃ k < q, let x := p+k*total V w
      blocked D (B.owner x) (B.owner ((x+total V w) % (q*total V w))) := by
  let T := total V w
  let N := q*T
  let f := fun k => B.owner ((p+k*T)%N)
  have last : (q-1)*T + T = N := by
    rw [← Nat.succ_mul,show (q-1).succ=q by omega]
  have limit (k) (hk : k < q) : p + k*T < N := by
    have := Nat.mul_le_mul_right T (show k≤q-1 by omega)
    change p < T at hp
    omega
  have pn : p < N := by simpa using limit 0 (by omega)
  have wrap : f q = f 0 := by simp [f,N,Nat.mod_eq_of_lt pn]
  have unroll (k) (hk : k < q) : f k = B.owner (p+k*T) := by
    simp [f,Nat.mod_eq_of_lt (limit k hk)]
  by_contra! none
  have legal (j) (hj : j < q) : f j = f (j+1) ∨ D (f j) (f (j+1)) = true := by
    by_contra! bad
    apply none j hj
    change blocked D (B.owner (p+j*T)) (B.owner ((p+j*T+T)%N))
    rw [← unroll j hj,← show p+(j+1)*T = p+j*T+T by rw [Nat.succ_mul]; omega]
    exact bad
  obtain ⟨l,len,walk,flat⟩ := compressed_walk f (k:=q)
    (fun j _ => B.valid _ (Nat.mod_lt _ (by omega : 0<N))) legal
  rw [wrap] at walk
  have zero : l=0 := by by_contra! pos; exact hf _ l (by omega) len walk
  have same := flat zero (q-1) (by omega)
  rw [unroll _ (by omega),unroll 0 (by omega),Nat.zero_mul,Nat.add_zero] at same
  have atEnd := (B.interval _ (limit (q-1) (by omega))).2
  rw [same] at atEnd
  have atStart := (B.interval p pn).1
  have width := width_bound hq hf strict (B.valid p pn)
  change q*w (B.owner p)+T < N at width
  omega

/-- Every ordering of a surviving witness has at least one distinct defective
phase per support vertex, in aggregate. Defects are counted modulo the total
weight, so multiple failures on the same orbit only count once. -/
theorem phase_lower {q D V w} (hq : 2 ≤ q) (hf : QFree D V q)
    (pos : ∀ i ∈ V, 0 < w i) (strict : Strict q D V w) (B : Blocks q V w) :
    V.card ≤ (interiorPhases B D).card := by
  classical
  let T := total V w
  let tails := fun i => (Finset.range (w i-1)).image
    (fun j => (B.start i + (q*w i-(w i-1)) + j)%T)
  have cover : Finset.range T ⊆ interiorPhases B D ∪ V.biUnion tails := by
    intro p hp
    obtain ⟨k,hk,miss⟩ := orbit_break hq hf strict B (Finset.mem_range.mp hp)
    let x := p+k*T
    let i := B.owner x
    have lim : x < q*T := by
      have h := Nat.mul_le_mul_right T (show k+1 ≤ q by omega)
      rw [Nat.succ_mul] at h
      have pT := Finset.mem_range.mp hp
      dsimp [x]; omega
    have vi := B.valid x lim
    have xmax := (B.interval x lim).2
    let endPrefix := B.start i + (q*w i - (w i-1))
    by_cases early : x < endPrefix
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,k,hk,early,miss⟩)
    apply Finset.mem_union_right _
    apply Finset.mem_biUnion.mpr
    refine ⟨i,vi,Finset.mem_image.mpr ⟨x-endPrefix,Finset.mem_range.mpr ?_,?_⟩⟩
    · change x < B.start i + q*w i at xmax
      dsimp [endPrefix] at *
      omega
    · change (endPrefix + (x-endPrefix))%T=p
      rw [Nat.add_sub_of_le (Nat.le_of_not_gt early)]
      simp [x,Nat.mod_eq_of_lt (Finset.mem_range.mp hp)]
  have cost (i) (_hi : i∈V) : (tails i).card ≤ w i-1 :=
    Finset.card_image_le.trans (Finset.card_range _).le
  have bound := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at bound
  have sumBound := Finset.card_biUnion_le.trans (Finset.sum_le_sum cost)
  have totalEq : (∑ i∈V,(w i-1)) + V.card = T := by
    calc
      _ = ∑ i∈V, ((w i-1) + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun i hi => by have := pos i hi; omega)
  omega

open Classical in
/-- A hole is a blocked hop ending within the clockwise run of slots
budgeted by the current label and its actual outgoing weight. -/
noncomputable def holes {q V w} (B : Blocks q V w) (D : CH.Digraph) : Finset ℕ :=
  (Finset.range (total V w)).filter fun p => ∃ k < q,
    let x := p+k*total V w
    let i := B.owner x
    x + total V w < B.start i + q*w i + q*heads D V w i ∧
      blocked D i (B.owner ((x+total V w) % (q*total V w)))

theorem holes_lower {q D V w} (hq : 2 ≤ q) (hf : QFree D V q)
    (pos : ∀ i ∈ V, 0 < w i) (strict : Strict q D V w) (B : Blocks q V w) :
    V.card ≤ (holes B D).card := by
  classical
  apply (phase_lower hq hf pos strict B).trans
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,k,hk,early,miss⟩ := Finset.mem_filter.mp hp
  let T := total V w
  let x := p+k*T
  let i := B.owner x
  have bound := Nat.mul_le_mul_right T (show k+1 ≤ q by omega)
  rw [Nat.succ_mul] at bound
  have pT : p<T := Finset.mem_range.mp hp
  have vi : i∈V := B.valid x (by dsimp [x]; change _ < q*T; omega)
  have row := nat_strict.mp strict i vi
  rw [score_eq] at row
  change T < w i + q*heads D V w i at row
  change x < B.start i + (q*w i - (w i-1)) at early
  have enough : w i ≤ q*w i := by simpa using Nat.mul_le_mul_right (w i) (show 1≤q by omega)
  exact Finset.mem_filter.mpr ⟨hp,k,hk,show x+T < B.start i + q*w i + q*heads D V w i by omega,miss⟩

/-- Clockwise offset of a slot from a chosen boundary of the circle. -/
def offset (N start x : ℕ) := if start ≤ x then x-start else N-start+x

private theorem offset_injective {N s x y : ℕ} (hs : s<N) (hx : x<N) (hy : y<N)
    (eq : offset N s x = offset N s y) : x=y := by
  unfold offset at eq
  split_ifs at eq <;> omega

private theorem offset_hop {N s x T : ℕ} (hs : s ≤ x) (hx : x<N)
    (short : x-s+T<N) : offset N s ((x+T)%N) = x-s+T := by
  by_cases wrap : N ≤ x+T
  · have h : x+T = (x+T-N) + N := by omega
    have rem : (x+T)%N=x+T-N := by
      conv_lhs => rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    simp [offset,rem,show ¬s≤x+T-N by omega]; omega
  · simp [offset,Nat.mod_eq_of_lt (by omega : x+T<N), show s≤x+T by omega]; omega

/-- In the clockwise order starting at each label's first slot, the label
and all its heads precede every other label. This compares positions only. -/
def PrefixOrder {q V w} (B : Blocks q V w) (D : CH.Digraph) : Prop :=
  ∀ i ∈ V, ∀ x < q*total V w, ∀ y < q*total V w,
    (B.owner x=i ∨ D i (B.owner x)=true) → blocked D i (B.owner y) →
      offset (q*total V w) (B.start i) x < offset (q*total V w) (B.start i) y

private theorem blocked_offset {q D V w} (hq : 2 ≤ q) (hf : QFree D V q)
    (pos : ∀ i ∈ V, 0 < w i) (B : Blocks q V w) (ord : PrefixOrder B D)
    {i y} (hi : i∈V) (hy : y < q*total V w) (miss : blocked D i (B.owner y)) :
    q*w i + q*heads D V w i ≤ offset (q*total V w) (B.start i) y := by
  classical
  let N := q*total V w
  let J := insert i (outN D V i)
  let slots := fun j => (Finset.range (q*w j)).image (fun d => B.start j+d)
  have sub : J ⊆ V := Finset.insert_subset hi (Finset.filter_subset _ _)
  have decode {j x} (hj : j∈J) (hx : x∈slots j) : x<N ∧ B.owner x=j := by
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hx
    exact B.fills j (sub hj) d (Finset.mem_range.mp hd)
  have disjoint : (J : Set ℕ).PairwiseDisjoint slots := by
    intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro x xa xb
    exact ne ((decode ha xa).2.symm.trans (decode hb xb).2)
  have count : (J.biUnion slots).card = q*w i + q*heads D V w i := by
    rw [Finset.card_biUnion disjoint]
    have counts (j) : (slots j).card = q*w j := by
      unfold slots
      rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h), Finset.card_range]
    simp only [counts,J]
    rw [Finset.sum_insert (fun h => loopfree hf (by omega) hi (mem_outN.mp h).2)]
    simp [heads, Finset.mul_sum]
  have ico : B.start i<N := by
    simpa using (B.fills i hi 0 (Nat.mul_pos (by omega) (pos i hi))).1
  have within {x} (hx : x∈J.biUnion slots) : x<N := by
    obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    exact (decode hj hx).1
  rw [← count,← Finset.card_range (offset _ _ y)]
  apply Finset.card_le_card_of_injOn (offset N (B.start i))
  · intro x hx
    obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨lim,eq⟩ := decode hj hx
    apply Finset.mem_range.mpr (ord i hi x lim y hy ?_ miss)
    rw [eq]
    exact (Finset.mem_insert.mp hj).imp_right (fun h => (mem_outN.mp h).2)
  · intro x hx z hz eq
    exact offset_injective ico (within hx) (within hz) eq

theorem no_prefix_order {q D V w} (hq : 2≤q) (hf : QFree D V q) (ne : V.Nonempty)
    (pos : ∀ i ∈ V, 0 < w i) (strict : Strict q D V w) (B : Blocks q V w) :
    ¬PrefixOrder B D := by
  classical
  intro ord
  have h := holes_lower hq hf pos strict B
  obtain ⟨p,hp⟩ := Finset.card_pos.mp ((Finset.card_pos.mpr ne).trans_le h)
  obtain ⟨bound,k,hk,early,miss⟩ := Finset.mem_filter.mp hp
  let T := total V w
  let N := q*T
  let x := p+k*T
  let i := B.owner x
  have pT : p<T := Finset.mem_range.mp bound
  have lim : x<N := by
    have a := Nat.mul_le_mul_right T (show k+1≤q by omega)
    rw [Nat.succ_mul] at a
    dsimp [x,N]; omega
  have vi := B.valid x lim
  have ⟨lo,up⟩ := B.interval x lim
  change B.start i≤x at lo
  change x<B.start i+q*w i at up
  have cap := width_bound hq hf strict vi
  change q*w i+T<N at cap
  have e := blocked_offset hq hf pos B ord vi (Nat.mod_lt (x+T) (by omega : 0<N)) miss
  change q*w i+q*heads D V w i ≤ offset N (B.start i) ((x+T)%N) at e
  rw [offset_hop lo lim (by omega)] at e
  change x+T < B.start i + q*w i + q*heads D V w i at early
  omega

theorem cycle_of_few_holes {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (close : ∀ X : Witness q D (Finset.range n) n, X.Minimal →
      ∃ B : Blocks q X.carrier X.weights, (holes B D).card < X.carrier.card) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨X,least,free,_⟩ := prime_frontier (by omega) hn order loop degree no
  obtain ⟨B,small⟩ := close X least
  exact small.not_ge (holes_lower hq free X.positive X.strict B)

/-- a precedes b in the circular order read from r, including r itself. -/
def cyclicLT (r a b : ℕ) : Prop :=
  (r≤a ∧ a<b) ∨ (a<b ∧ b<r) ∨ (b<r ∧ r≤a)

/-- A graph-only order. For each vertex its own label and its out-neighbours
form the initial segment of the circle read from that vertex. -/
def Consecutive (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ key : ℕ → ℕ, Set.InjOn key V ∧ ∀ i ∈ V, ∀ a ∈ V, ∀ b ∈ V,
    (a=i ∨ D i a=true) → blocked D i b → cyclicLT (key i) (key a) (key b)

private def Respects {q V w} (B : Blocks q V w) (key : ℕ → ℕ) :=
  ∀ a ∈ V, ∀ b ∈ V, key a < key b → B.start a + q*w a ≤ B.start b

private theorem ordered_blocks {q V w} (hq : 0<q) (pos : ∀ i ∈ V, 0<w i) (key : ℕ → ℕ) :
    ∃ B : Blocks q V w, Respects B key := by
  classical
  by_cases ne : V.Nonempty
  · obtain ⟨i,hi,maxi⟩ := V.exists_max_image key ne
    let U := V.erase i
    have sub : U ⊆ V := Finset.erase_subset _ _
    have fresh : i ∉ U := Finset.notMem_erase _ _
    obtain ⟨B,sorted⟩ := ordered_blocks (V:=U) hq (fun j hj => pos j (sub hj)) key
    have restore : insert i U=V := Finset.insert_erase hi
    suffices step : ∃ C : Blocks q (insert i U) w, Respects C key by rwa [restore] at step
    refine ⟨B.append i fresh,?_⟩
    intro a ha b hb ab
    change (if a=i then q*total U w else B.start a) + q*w a ≤
      (if b=i then q*total U w else B.start b)
    rcases Finset.mem_insert.mp ha with rfl | au
    · have := maxi b (restore ▸ hb)
      omega
    have na : a≠i := (Finset.mem_erase.mp au).1
    simp only [na, ↓reduceIte]
    rcases Finset.mem_insert.mp hb with rfl | bu
    · have pw := Nat.mul_pos hq (pos a (sub au))
      have lim := (B.fills a au (q*w a-1) (by omega)).1
      simp only [ite_true]; omega
    · simpa [(Finset.mem_erase.mp bu).1] using sorted a au b bu ab
  · exact ⟨(blocks_exist q V w).some,fun a ha => (ne ⟨a,ha⟩).elim⟩
termination_by V.card
decreasing_by exact Finset.card_erase_lt_of_mem hi

private theorem ordered_prefix {q D V w key} (B : Blocks q V w) (sort : Respects B key)
    (inj : Set.InjOn key V) (ord : ∀ i ∈ V, ∀ a ∈ V, ∀ b ∈ V,
      (a=i ∨ D i a=true) → blocked D i b → cyclicLT (key i) (key a) (key b)) :
    PrefixOrder B D := by
  intro i hi x hx y hy allowed miss
  have ax := B.valid x hx
  have byV := B.valid y hy
  have ⟨lx,ux⟩ := B.interval x hx
  have ⟨ly,uy⟩ := B.interval y hy
  have after (h : key i ≤ key (B.owner x)) : B.start i ≤ x := by
    rcases lt_or_eq_of_le h with lt | eq
    · have := sort i hi _ ax lt; omega
    · exact (inj hi ax eq) ▸ lx
  have between (h : key (B.owner x) < key (B.owner y)) : x < y := by
    have := sort _ ax _ byV h; omega
  have before (h : key (B.owner y) < key i) : y < B.start i := by
    have := sort _ byV i hi h; omega
  rcases ord i hi _ ax _ byV allowed miss with ⟨h,a⟩ | ⟨a,h⟩ | ⟨h,a⟩
  · have := after h; have := between a
    simp [offset,show B.start i≤x by omega,show B.start i≤y by omega]; omega
  · have := between a; have := before h
    simp [offset,show ¬B.start i≤x by omega,show ¬B.start i≤y by omega]; omega
  · have := before h; have := after a
    simp [offset,show B.start i≤x by omega,show ¬B.start i≤y by omega]; omega

theorem no_consecutive {q D V w} (hq : 2≤q) (hf : QFree D V q) (ne : V.Nonempty)
    (pos : ∀ i ∈ V, 0<w i) (strict : Strict q D V w) : ¬ Consecutive D V := by
  rintro ⟨key,inj,ord⟩
  obtain ⟨B,hB⟩ := ordered_blocks (by omega : 0<q) pos key
  exact no_prefix_order hq hf ne pos strict B (ordered_prefix B hB inj ord)

/-- The minimum witness now also avoids all circularly consecutive prime
graphs and the existing small weighted bases for the same cutoff. -/
theorem survivor {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ X : Witness q D (Finset.range n) n, X.Minimal ∧ QFree D X.carrier q ∧
      q+2<X.carrier.card ∧ (4≤q → q+3<X.carrier.card) ∧ ¬Consecutive D X.carrier ∧
      ∀ B : Blocks q X.carrier X.weights, X.carrier.card ≤ (holes B D).card := by
  obtain ⟨X,least,hf,_⟩ := prime_frontier (by omega) hn order loop degree no
  have bad (h : SmallRow q D X.carrier) : False :=
    h.no_strict X.nonempty _ (fun _ _ => Nat.cast_nonneg _) X.strict
  refine ⟨X,least,hf,?_,?_,no_consecutive hq hf X.nonempty X.positive X.strict,
    holes_lower hq hf X.positive X.strict⟩
  · by_contra! small
    exact bad (smallRow_of_card_le_add_two hq hf small)
  · intro four
    by_contra! small
    exact bad (smallRow_of_card_le_add_three four hf small)

theorem cycle_of_prime_orders {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (classified : ∀ U ⊆ Finset.range n, Prime D U →
      U.card ≤ q+2 ∨ (4≤q ∧ U.card ≤ q+3) ∨ Consecutive D U) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨X,_,_,large,larger,nc,_⟩ := survivor hq hn order loop degree no
  rcases classified _ X.subset X.prime with sm | ⟨four,sm⟩ | circ
  · omega
  · exact (larger four).not_ge sm
  · exact nc circ

private theorem quotient_free {q D E V I} (P : Substitution D E V I) (free : QFree D V q) :
    QFree E I q := by
  classical
  let rep := fun i => if hi : i∈I then (P.nonempty i hi).choose else i
  have inside (i) (hi : i∈I) : rep i ∈ P.fiber i := by
    simpa [rep,hi] using (P.nonempty i hi).choose_spec
  have lift {a b l} (walk : Walk E I a b l) (ha : a∈I) : Walk D V (rep a) (rep b) l := by
    induction walk with
    | refl => exact .refl _
    | @step a j c k hj aj rest ih =>
      have diff : a≠j := by rintro rfl; simp [P.loopless _ ha] at aj
      refine .step (P.fiber_subset hj (inside j hj)) ?_ (ih hj)
      exact (P.cross a ha j hj diff _ (inside a ha) _ (inside j hj)).trans aj
  intro a l hl bl walk
  have ha : a ∈ I := by
    cases l with
    | zero => omega
    | succ k => exact walk.unsnoc.choose_spec.2.1
  exact free _ l hl bl (lift walk ha)

/-- Arbitrary finite substitution trees with graph-only leaves. -/
inductive Decomposed (q : ℕ) : CH.Digraph → Finset ℕ → Prop where
  | small {D V} : V.card ≤ q+2 ∨ (4≤q ∧ V.card ≤ q+3) → Decomposed q D V
  | circle {D V} : Consecutive D V → Decomposed q D V
  | substitute {D E V I} (P : Substitution D E V I) :
      Decomposed q E I → (∀ i∈I, Decomposed q D (P.fiber i)) → Decomposed q D V

theorem Decomposed.excludes {q D V} (tree : Decomposed q D V) (hq : 2≤q)
    (free : QFree D V q) (ne : V.Nonempty) (w : ℕ → ℕ) (pos : ∀ i∈V, 0<w i) :
    ¬Strict q D V w := by
  induction tree generalizing w with
  | small h =>
    have base : SmallRow q _ _ := h.elim (smallRow_of_card_le_add_two hq free)
      (fun ⟨four,size⟩ => smallRow_of_card_le_add_three four free size)
    exact base.no_strict ne _ (fun _ _ => Nat.cast_nonneg _)
  | circle ord => exact fun strict => no_consecutive hq free ne pos strict ord
  | substitute P _ _ quotient child =>
    intro strict
    rcases strict_fork P strict with ⟨i,hi,inner⟩ | outer
    · exact child i hi (free.mono_set (P.fiber_subset hi)) (P.nonempty i hi) w
        (fun a ha => pos a (P.fiber_subset hi ha)) inner
    · obtain ⟨a,ha⟩ := ne
      obtain ⟨i,hi,_⟩ := Finset.mem_biUnion.mp (P.cover ▸ ha)
      apply quotient (quotient_free P free) ⟨i,hi⟩ _ _ outer
      intro j hj
      obtain ⟨b,hb⟩ := P.nonempty j hj
      exact (pos b (P.fiber_subset hj hb)).trans_le (Finset.single_le_sum (f:=w) (by intros; omega) hb)

theorem cycle_of_decomposition {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (tree : Decomposed q D (Finset.range n)) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  apply tree.excludes hq (qfree_of_noShort loop no) ⟨0,Finset.mem_range.mpr hn⟩ (fun _ => 1)
    (by intros; decide)
  apply nat_strict.mpr
  intro i hi
  have hd : s ≤ (outN D (Finset.range n) i).card := Compose.FloorSix.out_card degree (Finset.mem_range.mp hi)
  have := Nat.mul_le_mul_left q hd
  simp [score_eq,heads]
  omega

#print axioms blocks_exist
#print axioms width_bound
#print axioms phase_lower
#print axioms holes_lower
#print axioms no_prefix_order
#print axioms cycle_of_few_holes
#print axioms no_consecutive
#print axioms survivor
#print axioms cycle_of_prime_orders
#print axioms cycle_of_decomposition
end LeanCH.BR.ShenCircle
