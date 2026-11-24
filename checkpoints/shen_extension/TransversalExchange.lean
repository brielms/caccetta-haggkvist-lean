import checkpoints.shen_extension.CenterTablePaidReturn
import Mathlib.Data.Fintype.BigOperators

/-! Choose one representative per layer. A sink of the induced transversal
must miss its prescribed successor. Vary two representatives to force a
second miss on the very same transversal. -/
namespace LeanCH.BR.ShenTransversal
open BRq2 BRq3 Finset
open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def block (V : Finset ℕ) (layer : ℕ → ι) (i : ι) := V.filter (fun x => layer x=i)

abbrev Rep (V : Finset ℕ) (layer : ℕ → ι) (f : ι → ℕ) := ∀ i, f i∈block V layer i

def misses (D : CH.Digraph) (step : Equiv.Perm ι) (f : ι → ℕ) :=
  univ.filter (fun i => D (f i) (f (step i))=false)

omit [Fintype ι] [Nonempty ι] in
private theorem rep_update {V layer f} (hf : Rep (ι:=ι) V layer f)
    {i x} (hx : x∈block V layer i) : Rep V layer (Function.update f i x) := by
  intro j
  by_cases h : j=i
  · simpa [h] using hx
  · simpa [h] using hf j

private theorem sink_index {q D V layer f} (free : QFree D V q)
    (size : Fintype.card ι ≤ q) (hf : Rep V layer f) (step : Equiv.Perm ι) :
    ∃ i ∈ misses D step f, ∀ j, D (f i) (f j) ≠ true := by
  let U := univ.image f
  have sub : U ⊆ V := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp (hf i)).1
  have cap : U.card ≤ q := card_image_le.trans (by simpa using size)
  obtain ⟨x,hx,sink⟩ := exists_sink (free.mono_set sub) (univ_nonempty.image f) cap
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  have stop (j) : D (f i) (f j) ≠ true := sink _ (mem_image_of_mem _ (mem_univ j))
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,Bool.eq_false_iff.mpr (stop _)⟩,stop⟩

def SinkOnReps (D : CH.Digraph) (V : Finset ℕ) (layer : ℕ → ι) : Prop :=
  ∀ f, Rep V layer f → ∃ i, ∀ j, D (f i) (f j) ≠ true

private theorem sink_mark {D V layer} (sinks : SinkOnReps (ι:=ι) D V layer) {f}
    (hf : Rep V layer f) (step : Equiv.Perm ι) :
    ∃ i ∈ misses D step f, ∀ j, D (f i) (f j) ≠ true := by
  obtain ⟨i,stop⟩ := sinks f hf
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,Bool.eq_false_iff.mpr (stop _)⟩,stop⟩

theorem two_on_one_of_sinks {D V} (layer : ℕ → ι) (sinks : SinkOnReps D V layer)
    (inh : ∀ i, (block V layer i).Nonempty)
    (step : Equiv.Perm ι) (move : ∀ i, step i ≠ i) (turn : ∀ i, step (step i) ≠ i)
    (escape : ∀ x∈V, ∃ y∈outN D V x, layer y ≠ layer x) :
    ∃ f, Rep V layer f ∧ 2 ≤ (misses D step f).card := by
  classical
  by_contra! none
  let base := fun i => (inh i).choose
  have rep : Rep V layer base := fun i => (inh i).choose_spec
  have unique {f} (hf : Rep V layer f) {i j} (hi : i∈misses D step f) (hj : j∈misses D step f) :
      i=j := Finset.card_le_one.mp (by have := none f hf; omega) _ hi _ hj
  have forward {i x} (hx : x∈block V layer i) : ∃ y∈block V layer (step i), D x y=true := by
    obtain ⟨y,hy,other⟩ := escape x (mem_filter.mp hx).1
    have diff : layer y≠i := (mem_filter.mp hx).2 ▸ other
    let f := Function.update (Function.update base i x) (layer y) y
    have hf : Rep V layer f := rep_update (rep_update rep hx) (mem_filter.mpr ⟨(mem_outN.mp hy).1,rfl⟩)
    have fx : f i=x := by simp [f,diff.symm]
    have fy : f (layer y)=y := by simp [f]
    obtain ⟨j,hj,sink⟩ := sink_mark sinks hf step
    refine ⟨f (step i),hf _,?_⟩
    by_contra! fail
    have mi : i∈misses D step f := mem_filter.mpr ⟨mem_univ _,by simpa [fx] using Bool.eq_false_iff.mpr fail⟩
    have stop := sink (layer y)
    rw [unique hf hj mi,fx,fy] at stop
    exact stop (mem_outN.mp hy).2
  obtain ⟨i,hi,_⟩ := sink_mark sinks rep step
  obtain ⟨b,hb,ab⟩ := forward (rep i)
  obtain ⟨c,hc,bc⟩ := forward hb
  let f := Function.update base (step (step i)) c
  let g := Function.update f (step i) b
  have hf : Rep V layer f := rep_update rep hc
  have hg : Rep V layer g := rep_update hf hb
  have fi : f i=base i := by simp [f,(turn i).symm]
  have fj : f (step i)=base (step i) := by simp [f,(move (step i)).symm]
  have mi : i∈misses D step f := mem_filter.mpr ⟨mem_univ _,by rw [fi,fj]; exact (mem_filter.mp hi).2⟩
  obtain ⟨k,mk,_⟩ := sink_mark sinks hg step
  have broken := (mem_filter.mp mk).2
  by_cases ki : k=i
  · subst k
    simp [g,(move i).symm,fi,ab] at broken
  by_cases kj : k=step i
  · subst k
    simp [g,f,move (step i),bc] at broken
  have sk : step k≠step i := fun eq => ki (step.injective eq)
  have mkf : k∈misses D step f :=
    mem_filter.mpr ⟨mem_univ _,by simpa [g,kj,sk] using broken⟩
  exact ki (unique hf mkf mi)

private theorem sinks_of_small_order {q D V} (free : QFree D V q)
    (size : Fintype.card ι ≤ q) (layer : ℕ → ι) : SinkOnReps D V layer := by
  intro f hf
  obtain ⟨i,_,sink⟩ := sink_index free size hf (Equiv.refl ι)
  exact ⟨i,sink⟩

omit [Fintype ι] [Nonempty ι] in
/-- Loop exclusion supplies an escaping neighbour when a layer is no bigger
than the minimum out-degree. Equal size is unnecessary for this step. -/
theorem escape_of_degree {D V q s} (hq : 0<q) (free : QFree D V q)
    (degree : ∀ x∈V, s≤(outN D V x).card) (layer : ℕ → ι)
    (caps : ∀ i, (block V layer i).card≤s) :
    ∀ x∈V, ∃ y∈outN D V x, layer y ≠ layer x := by
  intro x hx
  by_contra! stuck
  have sub : outN D V x ⊆ (block V layer (layer x)).erase x := by
    intro y hy
    exact mem_erase.mpr ⟨fun eq => loopfree free hq hx (eq ▸ (mem_outN.mp hy).2),
      mem_filter.mpr ⟨(mem_outN.mp hy).1,stuck y hy⟩⟩
  have card := card_le_card sub
  have gap := card_erase_add_one (show x∈block V layer (layer x) from mem_filter.mpr ⟨hx,rfl⟩)
  have cap := caps (layer x)
  have lower := degree x hx
  omega

def absentPairs (D : CH.Digraph) (A B : Finset ℕ) :=
  ∑ a∈A, (B.filter (fun b => D a b=false)).card

omit [Nonempty ι] in
private theorem fixed_pair (B : ι → Finset ℕ) {i j : ι} (ji : j≠i)
    {a b} (ha : a∈B i) (hb : b∈B j) :
    (((Fintype.piFinset B).filter (fun f => f i=a)).filter (fun f => f j=b)).card =
      ∏ k∈(univ.erase j).erase i, (B k).card := by
  classical
  rw [← Fintype.piFinset_update_singleton_eq_filter_piFinset_eq B i ha]
  have hb' : b∈Function.update B i {a} j := by simpa [ji] using hb
  rw [Fintype.card_filter_piFinset_eq_of_mem _ _ hb']
  have counts (k) : (Function.update B i {a} k).card =
      Function.update (fun l => (B l).card) i 1 k := by
    by_cases h : k=i <;> simp [h]
  simp_rw [counts]
  rw [prod_update_of_mem (mem_erase.mpr ⟨ji.symm,mem_univ i⟩)]
  simp [Finset.erase_eq]

private theorem link_count (B : ι → Finset ℕ) (D : CH.Digraph) {i j : ι} (ji : j≠i) :
    (∑ f∈Fintype.piFinset B, if D (f i) (f j)=false then 1 else 0) =
      absentPairs D (B i) (B j) * ∏ k∈(univ.erase j).erase i, (B k).card := by
  classical
  let F := Fintype.piFinset B
  let C := ∏ k∈(univ.erase j).erase i, (B k).card
  let value := fun f : ι → ℕ => if D (f i) (f j)=false then 1 else 0
  have first (f) (hf : f∈F) : f i∈B i := Fintype.mem_piFinset.mp hf i
  rw [← sum_fiberwise_of_maps_to first value]
  unfold absentPairs
  rw [sum_mul]
  apply sum_congr rfl
  intro a ha
  let A := F.filter (fun f => f i=a)
  have second (f) (hf : f∈A) : f j∈B j := Fintype.mem_piFinset.mp (mem_filter.mp hf).1 j
  rw [← sum_fiberwise_of_maps_to second value,card_filter,sum_mul]
  apply sum_congr rfl
  intro b hb
  let S := A.filter (fun f => f j=b)
  have eq (f) (hf : f∈S) : value f = if D a b=false then 1 else 0 := by
    have data := mem_filter.mp hf
    simp only [value,(mem_filter.mp data.1).2,data.2]
  rw [sum_congr rfl eq,sum_const_nat (fun _ _ => rfl)]
  change S.card * _ = _ * C
  rw [show S.card=C from fixed_pair B ji ha hb,Nat.mul_comm]

/-- Exact number of incidences between representative choices and broken links. -/
theorem miss_count (B : ι → Finset ℕ) (D : CH.Digraph) (step : Equiv.Perm ι)
    (move : ∀ i, step i≠i) :
    (∑ f∈Fintype.piFinset B, (misses D step f).card) =
      ∑ i, absentPairs D (B i) (B (step i)) *
        ∏ k∈(univ.erase (step i)).erase i, (B k).card := by
  simp only [misses,card_filter]
  rw [sum_comm]
  exact sum_congr rfl (fun i _ => link_count B D (move i))

theorem product_bound {D V} (layer : ℕ → ι) (sinks : SinkOnReps D V layer)
    (inh : ∀ i, (block V layer i).Nonempty)
    (step : Equiv.Perm ι) (move : ∀ i, step i ≠ i) (turn : ∀ i, step (step i) ≠ i)
    (escape : ∀ x∈V, ∃ y∈outN D V x, layer y ≠ layer x) :
    let B := block V layer
    (∏ i, (B i).card) < ∑ i, absentPairs D (B i) (B (step i)) *
      ∏ k∈(univ.erase (step i)).erase i, (B k).card := by
  classical
  let B := block V layer
  let F := Fintype.piFinset B
  obtain ⟨g,hg,two⟩ := two_on_one_of_sinks layer sinks inh step move turn escape
  have one (f) (hf : f∈F) : 1 ≤ (misses D step f).card := by
    obtain ⟨i,hi,_⟩ := sink_mark sinks (Fintype.mem_piFinset.mp hf : Rep V layer f) step
    exact card_pos.mpr ⟨i,hi⟩
  have strict := sum_lt_sum one ⟨g,Fintype.mem_piFinset.mpr hg,two⟩
  change _ < ∑ i, absentPairs D (B i) (B (step i)) * _
  rw [← miss_count B D step move]
  simpa [F,B] using strict

theorem square_bound {q s D V} (hq : 0<q) (free : QFree D V q)
    (size : Fintype.card ι ≤ q) (three : 3≤Fintype.card ι)
    (degree : ∀ x∈V, s≤(outN D V x).card) (hs : 0<s)
    (layer : ℕ → ι) (sizes : ∀ i, (block V layer i).card=s)
    (step : Equiv.Perm ι) (move : ∀ i, step i ≠ i) (turn : ∀ i, step (step i) ≠ i) :
    s*s < ∑ i, absentPairs D (block V layer i) (block V layer (step i)) := by
  have h := product_bound layer (sinks_of_small_order free size layer) (fun i => card_pos.mp (by rw [sizes]; exact hs))
    step move turn (escape_of_degree hq free degree layer (fun i => (sizes i).le))
  dsimp only at h
  have cardExp (i) : ((univ.erase (step i)).erase i).card=Fintype.card ι-2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨(move i).symm,mem_univ _⟩),card_erase_of_mem (mem_univ _),card_univ]
    omega
  simp only [sizes,prod_const,card_univ,cardExp] at h
  rw [← sum_mul] at h
  have factor : s^(Fintype.card ι) = s*s*s^(Fintype.card ι-2) := by
    conv_lhs => rw [show Fintype.card ι=2+(Fintype.card ι-2) by omega,pow_add,pow_two]
  rw [factor] at h
  exact Nat.lt_of_mul_lt_mul_right h

/-- A path cycle using distinct row labels spends each row's budget at most
once. The stored return walks all end at the same current representative. -/
private theorem grow_until_return {q D V} (free : QFree D V q) (f : ι → ℕ)
    (r : ι → ℕ) (budget : (∑ j, r j) ≤ q)
    (next : ∀ i, ∃ j l, 0<l ∧ l≤r i ∧ Walk D V (f i) (f j) l)
    (seen : Finset ι) (i : ι) (fresh : i∉seen)
    (history : ∀ j∈seen, ∃ l, 0<l ∧ l≤∑ a∈seen, r a ∧ Walk D V (f j) (f i) l) : False := by
  classical
  obtain ⟨j,d,pd,cap,edge⟩ := next i
  have total : r i + (∑ a∈seen, r a) = ∑ a∈insert i seen, r a := (sum_insert fresh).symm
  have room := (sum_le_sum_of_subset_of_nonneg (f:=r) (subset_univ (insert i seen))
    (fun _ _ _ => Nat.zero_le _)).trans budget
  by_cases same : j=i
  · subst j
    exact free _ d pd (by omega) edge
  by_cases old : j∈seen
  · obtain ⟨l,pl,cl,back⟩ := history j old
    exact free _ (l+d) (by omega) (by omega) (back.append edge)
  apply grow_until_return free f r budget next (insert i seen) j (by simp [same,old])
  intro a ha
  rcases mem_insert.mp ha with rfl | past
  · exact ⟨d,pd,by omega,edge⟩
  · obtain ⟨l,pl,cl,p⟩ := history a past
    exact ⟨l+d,by omega,by omega,p.append edge⟩
termination_by Fintype.card ι - seen.card
decreasing_by
  have := card_le_card (subset_univ (insert i seen))
  simp only [card_univ,card_insert_of_notMem fresh] at *
  omega

noncomputable def reach (D : CH.Digraph) (V : Finset ℕ) (layer : ℕ → ι) (r : ι → ℕ) :
    CH.Digraph := fun a b => decide (∃ d, 0<d ∧ d≤r (layer a) ∧ Walk D V a b d)

omit [Fintype ι] [Nonempty ι] in
theorem escape_of_ball {D V} (layer : ℕ → ι) (r : ι → ℕ)
    (growth : ∀ x∈V, (block V layer (layer x)).card < (ball D V x (r (layer x))).card) :
    ∀ x∈V, ∃ y∈outN (reach D V layer r) V x, layer y ≠ layer x := by
  intro x hx
  have outside : ¬ball D V x (r (layer x)) ⊆ block V layer (layer x) :=
    fun sub => (growth x hx).not_ge (card_le_card sub)
  obtain ⟨y,hy,excluded⟩ := Finset.not_subset.mp outside
  obtain ⟨yv,d,cap,path⟩ := mem_ball.mp hy
  have diff : layer y ≠ layer x := fun h => excluded (mem_filter.mpr ⟨yv,h⟩)
  have pos : 0<d := by
    cases d with
    | zero => cases path; exact (diff rfl).elim
    | succ => omega
  refine ⟨y,mem_outN.mpr ⟨yv,?_⟩,diff⟩
  exact decide_eq_true (show ∃ l, 0<l ∧ l≤r (layer x) ∧ Walk D V x y l from ⟨d,pos,cap,path⟩)

theorem sinks_of_budget {q D V} (free : QFree D V q) (layer : ℕ → ι) (r : ι → ℕ)
    (budget : (∑ i, r i) ≤ q) : SinkOnReps (reach D V layer r) V layer := by
  classical
  intro f hf
  by_contra! next
  apply grow_until_return free f r budget ?_ ∅ (Classical.arbitrary ι) (by simp) (by simp)
  intro i
  obtain ⟨j,walk⟩ := next i
  exact ⟨j,by simpa [reach,(mem_filter.mp (hf i)).2] using walk⟩

def layerProduct (V : Finset ℕ) (layer : ℕ → ι) :=
  ∏ i, (block V layer i).card

def missingProduct (E : CH.Digraph) (V : Finset ℕ) (layer : ℕ → ι) (step : Equiv.Perm ι) :=
  ∑ i, absentPairs E (block V layer i) (block V layer (step i)) *
    ∏ k∈(univ.erase (step i)).erase i, (block V layer k).card

theorem reach_bound {q D V} (free : QFree D V q) (layer : ℕ → ι) (r : ι → ℕ)
    (budget : (∑ i, r i) ≤ q) (inh : ∀ i, (block V layer i).Nonempty)
    (step : Equiv.Perm ι) (move : ∀ i, step i ≠ i) (turn : ∀ i, step (step i) ≠ i)
    (escape : ∀ x∈V, ∃ y∈outN (reach D V layer r) V x, layer y ≠ layer x) :
    layerProduct V layer < missingProduct (reach D V layer r) V layer step :=
  product_bound layer (sinks_of_budget free layer r budget) inh step move turn escape

/-- An input class specified without a no-cycle assumption. A block is
allowed its own reach radius. The certificate compares two explicit finite counts. -/
def ExchangeTest (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ m : ℕ, ∃ layer : ℕ → Fin (m+1), ∃ r : Fin (m+1) → ℕ, ∃ step : Equiv.Perm (Fin (m+1)),
    (∑ i, r i) ≤ q ∧ (∀ i, (block V layer i).Nonempty) ∧
    (∀ i, step i≠i) ∧ (∀ i, step (step i)≠i) ∧
    (∀ x∈V, ∃ y∈outN (reach D V layer r) V x, layer y≠layer x) ∧
    missingProduct (reach D V layer r) V layer step ≤ layerProduct V layer

theorem cycle_of_exchange {q n D} (loop : CH.Loopless D n)
    (test : ExchangeTest q D (Finset.range n)) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨_,layer,r,step,budget,inh,move,turn,escape,small⟩ := test
  exact small.not_gt (reach_bound (qfree_of_noShort loop no) layer r budget inh step move turn escape)

#print axioms two_on_one_of_sinks
#print axioms escape_of_degree
#print axioms miss_count
#print axioms product_bound
#print axioms square_bound
#print axioms reach_bound
#print axioms escape_of_ball
#print axioms cycle_of_exchange
end LeanCH.BR.ShenTransversal
