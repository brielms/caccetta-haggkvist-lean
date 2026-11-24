import checkpoints.shen_extension.SharedHeadPairTransfer

namespace LeanCH.BR.ShenTransitions
open BRq2 BRq3 BR45 ShenSharedHead
open Classical

/-- The class of candidate graphs for a fixed permissible pair-test threshold. -/
structure Candidate (D : CH.Digraph) (V : Finset ℕ) (s g k : ℕ) : Prop where
  free : QFree D V 3
  regular : OutEq s D V
  nonempty : V.Nonempty
  degree_pos : 0<s
  gap_pos : 0<g
  order_gap : V.card+g=3*s+1
  price : (k-2)*(k-3)<2*s*g

def LowOverlap (D : CH.Digraph) (V : Finset ℕ) (s : ℕ) :=
  ∀ u∈V,∀ v∈outN D V u,(commonOut D V u v).card≤(s+1)/2

def HardArc (D : CH.Digraph) (V : Finset ℕ) (k u v : ℕ) :=
  u∈V ∧ v∈activeParents D V u ∧
    ∀ i∈commonOut D V u v,∀ j∈commonOut D V u v,absent D i j=true →
      k+(commonIn D (outN D V v) i j).card<(commonOut D V i j).card

/-- A checkable configuration in one graph, with one parent arc throughout. -/
def FanOn (D : CH.Digraph) (V : Finset ℕ) (s k u v : ℕ) :=
  let T := commonOut D V u v
    ∃ x∈T,∃ y∈outN D T x,let Z := outN D T y \ outN D T x
      9*residual D V u v<14*Z.card ∧
      s+residual D V u v≤T.card+(commonOut D V v x).card ∧
      (∀ z∈Z,absent D x z=true ∧ k+(commonIn D (outN D V v) x z).card<(commonOut D V x z).card) ∧
      ∃ h∈outN D V x,Z.card*(k+1)≤s*(inN D Z h).card

def MarkedFan (D : CH.Digraph) (V : Finset ℕ) (s k : ℕ) :=
  ∃ u∈V,∃ v∈activeParents D V u,FanOn D V s k u v

theorem hard_arc_of_not_cheap {D V k} (fail : ¬CheapPairOnEachActiveArc D V k) :
    ∃ u v,HardArc D V k u v := by
  unfold CheapPairOnEachActiveArc at fail
  push Not at fail
  obtain ⟨u,hu,v,hv,bad⟩ := fail
  exact ⟨u,v,hu,hv,bad⟩

private theorem share_head {D : CH.Digraph} {V Z : Finset ℕ} {s k x}
    (hm : OutEq s D V) (hx : x∈V) (hs : 0<s)
    (shared : ∀ z∈Z,k<(commonOut D V x z).card) :
    ∃ h∈outN D V x,Z.card*(k+1)≤s*(inN D Z h).card := by
  let O := outN D V x
  have size : O.card=s := hm x hx
  obtain ⟨h,hh,largest⟩ := O.exists_max_image (fun w => (inN D Z w).card)
    (Finset.card_pos.mp (by omega))
  have lo := Finset.sum_le_sum (fun z (hz : z∈Z) => (show k+1≤(commonOut D V x z).card from shared z hz))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at lo
  have transfer : (∑ z∈Z,(commonOut D V x z).card)=∑ w∈O,(inN D Z w).card := by
    have eq (z) : commonOut D V x z=outN D O z := by ext w; simp [O,commonOut,outN]; tauto
    simp only [eq,outN,inN,Finset.card_filter]
    exact Finset.sum_comm
  have hi := Finset.sum_le_sum largest
  rw [Finset.sum_const_nat (fun _ _ => rfl),size] at hi
  exact ⟨h,hh,lo.trans (transfer ▸ hi)⟩

/-- Inside the marked bank choose a minimum row x. Inside x's internal
outgoing row choose a second minimum y. All newly reached labels keep x,y
and the original expensive arc u→v as simultaneous witnesses. -/
theorem hard_to_fan_on {D V s g k u v} (G : Candidate D V s g k) (hard : HardArc D V k u v) :
    FanOn D V s k u v := by
  obtain ⟨hu,hv,expensive⟩ := hard
  let T := commonOut D V u v
  have tv : T⊆V := Finset.inter_subset_left.trans (Finset.filter_subset _ _)
  have vV := (mem_outN.mp (Finset.mem_filter.mp hv).1).1
  let d := residual D V u v
  have pos : 0<d := (Finset.mem_filter.mp hv).2
  have unpaid : d+(endpoints D V u v).card=T.card := by
    change 0<T.card-(endpoints D V u v).card at pos
    change T.card-(endpoints D V u v).card+_=T.card; omega
  obtain ⟨x,hx,low⟩ := T.exists_min_image (fun w => (outN D T w).card)
    (Finset.card_pos.mp (by omega))
  let O := outN D T x
  have paid := bank_payment G.regular vV hx
  change T.card≤_+O.card at paid
  have dO : d≤O.card := by omega
  have oT : O⊆T := Finset.filter_subset _ _
  obtain ⟨y,hy,lower⟩ := O.exists_min_image (fun w => (outN D O w).card)
    (Finset.card_pos.mp (by omega))
  let Z := outN D T y \ O
  have narrow := order_bound (a:=14) (b:=5) (by decide) (by decide)
    (G.free.mono_set (oT.trans tv)) lower (Finset.card_pos.mp (by omega : 0<O.card))
  have cover : outN D T y⊆outN D O y ∪ Z := by
    intro z hz
    by_cases hit : z∈O
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hit,(mem_outN.mp hz).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz,hit⟩)
  have enough := (low y (oT hy)).trans ((Finset.card_le_card cover).trans (Finset.card_union_le _ _))
  change O.card≤(outN D O y).card+Z.card at enough
  have geometry (z) (hz : z∈Z) : absent D x z=true ∧
      k+(commonIn D (outN D V v) x z).card<(commonOut D V x z).card := by
    obtain ⟨yz,notHead⟩ := Finset.mem_sdiff.mp hz
    have zT := (mem_outN.mp yz).1
    have xy := (mem_outN.mp hy).2
    have edge := (mem_outN.mp yz).2
    have missing : absent D x z=true := by
      apply decide_eq_true
      exact ⟨fun eq => digonfree G.free (by decide) (tv hx) (tv (oT hy)) xy (eq.symm ▸ edge),
        fun xz => notHead (mem_outN.mpr ⟨zT,xz⟩),fun zx =>
          G.free x 3 (by decide) le_rfl (.step (tv (oT hy)) xy (.step (tv zT) edge (.step (tv hx) zx (.refl _))))⟩
    exact ⟨missing,expensive x hx z zT missing⟩
  have next := successor_pressure G.regular hx
  exact ⟨x,hx,y,hy,by change 9*d<14*Z.card; omega,by change s+d≤T.card+_; omega,geometry,
    share_head G.regular (tv hx) G.degree_pos (fun z hz => by have := (geometry z hz).2; omega)⟩

theorem hard_to_fan {D V s g k u v} (G : Candidate D V s g k) (hard : HardArc D V k u v) :
    MarkedFan D V s k :=
  ⟨u,hard.1,v,hard.2.1,hard_to_fan_on G hard⟩

inductive Node
  | candidate | lowOverlap | largeOverlap | cheapPairs | hardArc | markedFan
  deriving DecidableEq, Repr

def children : Node → List Node
  | .candidate => [.lowOverlap,.largeOverlap]
  | .largeOverlap => [.cheapPairs,.hardArc]
  | .hardArc => [.markedFan]
  | _ => []

def rank : Node → ℕ
  | .candidate => 3
  | .largeOverlap => 2
  | .hardArc => 1
  | _ => 0

theorem rank_drops {a b : Node} (edge : b∈children a) : rank b<rank a := by
  cases a <;> cases b <;> simp_all [children,rank]

/-- The carrier, regular graph and thresholds stay fixed across the fork. -/
def Holds (D : CH.Digraph) (V : Finset ℕ) (s g k : ℕ) (a : Node) : Prop :=
  Candidate D V s g k ∧ match a with
    | .candidate => True
    | .lowOverlap => LowOverlap D V s
    | .largeOverlap => ¬LowOverlap D V s
    | .cheapPairs => ¬LowOverlap D V s ∧ CheapPairOnEachActiveArc D V k
    | .hardArc => ¬LowOverlap D V s ∧ ∃ u v,HardArc D V k u v
    | .markedFan => ¬LowOverlap D V s ∧ MarkedFan D V s k

theorem covers {D V s g k a} (state : Holds D V s g k a) (internal : children a≠[]) :
    ∃ b∈children a,Holds D V s g k b := by
  obtain ⟨G,facts⟩ := state
  cases a with
  | candidate =>
    by_cases h : LowOverlap D V s
    · exact ⟨.lowOverlap,by decide,G,h⟩
    · exact ⟨.largeOverlap,by decide,G,h⟩
  | largeOverlap =>
    by_cases h : CheapPairOnEachActiveArc D V k
    · exact ⟨.cheapPairs,by decide,G,facts,h⟩
    · exact ⟨.hardArc,by decide,G,facts,hard_arc_of_not_cheap h⟩
  | hardArc =>
    obtain ⟨large,u,v,hard⟩ := facts
    exact ⟨.markedFan,by decide,G,large,hard_to_fan G hard⟩
  | lowOverlap | cheapPairs | markedFan => exact (internal rfl).elim

theorem low_closed {D V s g k} (state : Holds D V s g k .lowOverlap) : False := by
  obtain ⟨G,low⟩ := state
  let m := (s+1)/2
  have pos := G.degree_pos
  have gp := G.gap_pos
  have cap := arc_pressure_bound (m:=m) G.free G.regular G.nonempty pos G.order_gap
    (by dsimp [m]; omega) low
  have a := Nat.mul_le_mul_right (s-1) (show 2*m-s≤1 by dsimp [m]; omega)
  have b := Nat.mul_le_mul_left (2*m) (show 1≤g by omega)
  have c : s≤2*m := by dsimp [m]; omega
  omega

theorem cheap_closed {D V s g k} (state : Holds D V s g k .cheapPairs) : False :=
  (Nat.not_lt_of_ge (pair_bill_global state.1.free state.1.regular state.1.nonempty state.1.order_gap state.2.2)) state.1.price

def Step (D : CH.Digraph) (V : Finset ℕ) (s g k : ℕ) (a b : Node) : Prop :=
  b∈children a ∧ Holds D V s g k a ∧ Holds D V s g k b

/-- The trace certifies a path of legal steps for this same instance. The
rank decreases on each step; both closed leaves are explicitly discharged. -/
theorem trace_to_fan {D V s g k a} (state : Holds D V s g k a) :
    Relation.ReflTransGen (Step D V s g k) a .markedFan ∧ Holds D V s g k .markedFan := by
  by_cases stop : children a=[]
  · cases a with
    | candidate | largeOverlap | hardArc => contradiction
    | lowOverlap => exact (low_closed state).elim
    | cheapPairs => exact (cheap_closed state).elim
    | markedFan => exact ⟨.refl,state⟩
  · obtain ⟨b,edge,live⟩ := covers state stop
    obtain ⟨path,finish⟩ := trace_to_fan live
    exact ⟨path.head (show Step D V s g k a b from ⟨edge,state,live⟩),finish⟩
termination_by rank a
decreasing_by exact rank_drops edge

theorem reaches_fan {D V s g k a} (state : Holds D V s g k a) : Holds D V s g k .markedFan :=
  (trace_to_fan state).2

/-- Each prescribed regular trimming must pass the same graph of classes. -/
theorem trim_frontier {D F : CH.Digraph} {n s k : ℕ} (hn : 0<n) (hs : 0<s)
    (order : n≤3*s) (hl : CH.Loopless D n) (no : ¬CH.HasDirectedCycleAtMost D n 3)
    (sub : ∀ x y,F x y=true → D x y=true) (reg : OutEq s F (Finset.range n))
    (price : (k-2)*(k-3)<2*s*(3*s+1-n)) : Holds F (Finset.range n) s (3*s+1-n) k .markedFan := by
  apply reaches_fan (a:=.candidate)
  refine ⟨?_,trivial⟩
  exact ⟨qfree_sub sub (qfree_of_noShort hl no),reg,⟨0,Finset.mem_range.mpr hn⟩,hs,by omega,
    by rw [Finset.card_range]; omega,price⟩

/-- A surviving literal input admits an exact-degree trimming on its own
vertex labels. Every qualifying threshold works on this same trimming. -/
theorem triangle_frontier {D : CH.Digraph} {n s : ℕ} (hn : 0<n) (hs : 0<s)
    (order : n≤3*s) (hl : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n 3) :
    ∃ F : CH.Digraph,(∀ x y,F x y=true → D x y=true) ∧ OutEq s F (Finset.range n) ∧
      ∀ k,(k-2)*(k-3)<2*s*(3*s+1-n) → Holds F (Finset.range n) s (3*s+1-n) k .markedFan := by
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun x (hx : x∈Finset.range n) => Compose.FloorSix.out_card degree (Finset.mem_range.mp hx))
  exact ⟨F,sub,reg,fun _ price => trim_frontier hn hs order hl no sub reg price⟩

/-- The positive arcs of the marked configuration survive the transfer back
to the input. The displayed common-successor count is in the original graph. -/
def PathInCommonHeads (D : CH.Digraph) (V : Finset ℕ) (k : ℕ) :=
  ∃ u∈V,∃ v∈outN D V u,let T := commonOut D V u v
    ∃ x∈T,∃ y∈outN D T x,∃ z∈outN D T y,k<(commonOut D V x z).card

theorem fan_to_input {D F V s k} (sub : ∀ x y,F x y=true → D x y=true)
    (fan : MarkedFan F V s k) : PathInCommonHeads D V k := by
  obtain ⟨u,hu,v,hv,x,hx,y,hy,size,_,expensive,_⟩ := fan
  let T := commonOut F V u v
  let Z := outN F T y \ outN F T x
  change _<14*Z.card at size
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0<Z.card)
  have lift (a b) : commonOut F V a b⊆commonOut D V a b := by
    intro w hw
    obtain ⟨aw,bw⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨mem_outN.mpr ⟨(mem_outN.mp aw).1,sub _ _ (mem_outN.mp aw).2⟩,
      mem_outN.mpr ⟨(mem_outN.mp bw).1,sub _ _ (mem_outN.mp bw).2⟩⟩
  obtain ⟨vV,uv⟩ := mem_outN.mp (Finset.mem_filter.mp hv).1
  obtain ⟨yT,xy⟩ := mem_outN.mp hy
  obtain ⟨zT,yz⟩ := mem_outN.mp (Finset.mem_sdiff.mp hz).1
  have e := (expensive z hz).2
  have larger := Finset.card_le_card (lift x z)
  exact ⟨u,hu,v,mem_outN.mpr ⟨vV,sub _ _ uv⟩,x,lift u v hx,y,
    mem_outN.mpr ⟨lift u v yT,sub _ _ xy⟩,z,mem_outN.mpr ⟨lift u v zT,sub _ _ yz⟩,by omega⟩

theorem cycle_of_no_path_in_common_heads {D : CH.Digraph} {n s k} (hn : 0<n) (hs : 0<s)
    (order : n≤3*s) (hl : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (price : (k-2)*(k-3)<2*s*(3*s+1-n)) (missing : ¬PathInCommonHeads D (Finset.range n) k) :
    CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  obtain ⟨F,sub,_,reach⟩ := triangle_frontier hn hs order hl degree no
  exact missing (fan_to_input sub (reach k price).2.2)

#print axioms hard_to_fan_on
#print axioms hard_to_fan
#print axioms covers
#print axioms trace_to_fan
#print axioms reaches_fan
#print axioms triangle_frontier
#print axioms cycle_of_no_path_in_common_heads
end LeanCH.BR.ShenTransitions
