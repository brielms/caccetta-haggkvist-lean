import checkpoints.shen_extension.CornerBlockExchange

namespace LeanCH.BR.Closure.CornerBlockSubstitution
open Finset BRq2 BRq3 BR45 BRsub WeightedSD CornerHeadRecurrence

/-- Only arcs with both ends in the puncture module are replaced. -/
def graft (D A : CH.Digraph) (S : Finset ℕ) : CH.Digraph :=
  fun i j=>if i∈S ∧ j∈S then A i j else D i j

private def represents (S : Finset ℕ) (i r : ℕ) : Prop := if i∈S then r∈S else r=i

private theorem project {D A : CH.Digraph} {U S L : Finset ℕ} (block : Block D U S) (ls : L⊆S)
    {i j k} (path : Walk (graft D A S) ((U\S)∪L) i j k) (start : i∈(U\S)∪L) :
    (i∈L ∧ j∈L ∧ Walk A L i j k) ∨
    ∀r t,represents S i r → represents S j t →
      ∃l,l≤k ∧ (0<l ∨ k=0 ∧ i∉S) ∧ Walk D U r t l := by
  classical
  let K := (U\S)∪L
  have ku : K⊆U := union_subset sdiff_subset (ls.trans block.1)
  have label {x} (xk : x∈K) (xs : x∈S) : x∈L :=
    (mem_union.mp xk).resolve_left (fun h=>(mem_sdiff.mp h).2 xs)
  have idRep (x) : represents S x x := by by_cases h : x∈S <;> simp [represents,h]
  induction path with
  | refl i =>
    by_cases si : i∈S
    · exact Or.inl ⟨label start si,label start si,.refl _⟩
    · right
      intro r t rr tt
      simp [represents,si] at rr tt
      exact ⟨0,le_rfl,Or.inr ⟨rfl,si⟩,rr ▸ tt ▸ .refl _⟩
  | @step i c j k ck edge rest ih =>
    have step {r s} (ri : represents S i r) (sc : represents S c s) (cross : ¬(i∈S ∧ c∈S)) : D r s=true := by
      have native : D i c=true := by simpa only [graft,ite_eq_right cross] using edge
      by_cases si : i∈S
      · have co : c∉S := fun cs=>cross ⟨si,cs⟩
        have rs : r∈S := by simpa [represents,si] using ri
        have eq : s=c := by simpa [represents,co] using sc
        rw [eq]; exact (block.2.2.2 r rs i si c (ku ck) co).trans native
      · have eq : r=i := by simpa [represents,si] using ri
        rw [eq]
        by_cases cs : c∈S
        · have ss : s∈S := by simpa [represents,cs] using sc
          exact (block.2.2.1 s ss c cs i (ku start) si).trans native
        · have eq' : s=c := by simpa [represents,cs] using sc
          rwa [eq']
    rcases ih ck with ⟨cl,jl,inside⟩|tail
    · have cs := ls cl
      by_cases si : i∈S
      · left; exact ⟨label start si,jl,.step cl (by simpa [graft,si,cs] using edge) inside⟩
      · right; intro r t ri tj
        have ts : t∈S := by simpa [represents,ls jl] using tj
        have tc : represents S c t := by simpa [represents,cs] using ts
        exact ⟨1,by omega,Or.inl (by decide),.step (block.1 ts) (step ri tc (fun both=>si both.1)) (.refl _)⟩
    · right; intro r t ri tj
      by_cases both : i∈S ∧ c∈S
      · have rs : r∈S := by simpa [represents,both.1] using ri
        have rc : represents S c r := by simpa [represents,both.2] using rs
        obtain ⟨l,bound,positive,p⟩ := tail r t rc tj
        exact ⟨l,by omega,Or.inl (positive.resolve_right (fun h=>h.2 both.2)),p⟩
      · obtain ⟨l,bound,_,p⟩ := tail c t (idRep c) tj
        exact ⟨l+1,by omega,Or.inl (by omega),.step (ku ck) (step ri (idRep c) both) p⟩

/-- An arbitrary new internal graph with arbitrary pivot contacts is safe
    whenever its own extension at the pivot is safe. Exterior contacts of
    the pivot are retained. Every mixed return lifts to the original host. -/
theorem safe {q y : ℕ} {D A : CH.Digraph} {V S L I O : Finset ℕ}
    (free : QFree D V q) (yv : y∈V) (block : Block D (V.erase y) S)
    (parent : ∃t∈S,D t y=true) (head : ∃v∈S,D y v=true)
    (ls : L⊆S) (il : I⊆L) (ol : O⊆L) (inside : QFree A L q)
    (apart : ∀v∈O,∀t∈I,∀k,k≤q-2 → ¬ Walk A L v t k) (hq : 2≤q) :
    let W := (V.erase y)\S
    let K := W∪L
    QFree (coreTwoSidedExtension (graft D A S) K (inN D W y∪I) (outN D W y∪O) y) (insert y K) q := by
  intro W K
  have ku : K⊆V.erase y := union_subset sdiff_subset (ls.trans block.1)
  have off : y∉K := fun h=>notMem_erase y V (ku h)
  have oldFree := free.mono_set (erase_subset y V)
  have innerFree : QFree (graft D A S) K q := by
    intro a l pos bound path
    have ak : a∈K := by
      cases l with
      | zero => omega
      | succ k => exact path.unsnoc.choose_spec.2.1
    rcases project block ls path ak with ⟨_,_,p⟩|lift
    · exact inside a l pos bound p
    · have rr : represents S a a := by by_cases h : a∈S <;> simp [represents,h]
      obtain ⟨m,le,gt,p⟩ := lift a a rr rr
      exact oldFree a m (by rcases gt with h|h <;> omega) (le.trans bound) p
  have ink : inN D W y∪I⊆K := union_subset
    (fun _ h=>mem_union_left _ (mem_inN.mp h).1) (il.trans subset_union_right)
  apply coreTwoSidedExtension_qfree off ink innerFree
  intro v vo t ti k bound path
  have outer {a} (aw : a∈W) : represents S a a := by simp [represents,(mem_sdiff.mp aw).2]
  have new {a r} (al : a∈L) (rs : r∈S) : represents S a r := by simp [represents,ls al,rs]
  have chooseV : ∃r,represents S v r ∧ r∈V ∧ D y r=true := by
    rcases mem_union.mp vo with old|o
    · obtain ⟨vw,edge⟩ := mem_outN.mp old
      exact ⟨v,outer vw,mem_of_mem_erase (mem_sdiff.mp vw).1,edge⟩
    · obtain ⟨r,rs,edge⟩ := head
      exact ⟨r,new (ol o) rs,mem_of_mem_erase (block.1 rs),edge⟩
  have chooseT : ∃s,represents S t s ∧ D s y=true := by
    rcases mem_union.mp ti with old|i
    · obtain ⟨tw,edge⟩ := mem_inN.mp old
      exact ⟨t,outer tw,edge⟩
    · obtain ⟨s,ss,edge⟩ := parent
      exact ⟨s,new (il i) ss,edge⟩
  have vk : v∈K := (mem_union.mp vo).elim (fun h=>mem_union_left _ (mem_outN.mp h).1)
    (fun h=>mem_union_right _ (ol h))
  rcases project block ls path vk with ⟨vl,tl,p⟩|lift
  · have o := (mem_union.mp vo).resolve_left (fun h=>(mem_sdiff.mp (mem_outN.mp h).1).2 (ls vl))
    have i := (mem_union.mp ti).resolve_left (fun h=>(mem_sdiff.mp (mem_inN.mp h).1).2 (ls tl))
    exact apart v o t i k bound p
  · obtain ⟨r,rv,rr,yr⟩ := chooseV
    obtain ⟨s,st,sy⟩ := chooseT
    obtain ⟨m,le,_,p⟩ := lift r s rv st
    exact free y (m+1+1) (by omega) (by omega) (.step rr yr ((p.mono (erase_subset ..)).snoc yv sy))

/-- A smaller graph chosen freely inside the block must lose a pivot contact.
    The replacement uses its own arcs, its own entry/exit sets and its own
    two weights. The exterior and both exterior weights are unchanged. -/
theorem substitute {q y : ℕ} {D A : CH.Digraph} {V S L I O : Finset ℕ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (yv : y∈V) (block : Block D (V.erase y) S)
    (parent : ∃t∈S,D t y=true) (head : ∃v∈S,D y v=true)
    (less : L⊂S) (il : I⊆L) (ol : O⊆L) (inside : QFree A L q)
    (apart : ∀v∈O,∀t∈I,∀k,k≤q-2 → ¬ Walk A L v t k)
    {z p b c : ℕ→ℚ} (pos : ∀i∈V.erase y,0<z i ∧ 0<p i)
    (zm : mass (V.erase y) z=1) (pm : mass (V.erase y) p=1)
    (flat : ∀i∈V.erase y,WeightedSD.row q D (V.erase y) z i=1 ∧ WeightedSD.col q D (V.erase y) p i=1)
    (factor : ∀i∈S,WeightedSD.row q D S z i=mass S z ∧ WeightedSD.col q D S p i=mass S p)
    (newPos : ∀i∈L,0<b i ∧ 0<c i) (bm : mass L b=mass S z) (cm : mass L c=mass S p)
    (newFlat : ∀i∈L,WeightedSD.row q A L b i=mass S z ∧ WeightedSD.col q A L c i=mass S p) :
    let W := (V.erase y)\S
    (q:ℚ)*(outW D W z y+mass O b)<1 ∨ (q:ℚ)*(inW D W p y+mass I c)<1 := by
  classical
  intro W
  let U := V.erase y
  let K := W∪L
  let H := outN D W y∪O
  let P := inN D W y∪I
  let G := graft D A S
  let E := coreTwoSidedExtension G K P H y
  have ku : K⊆U := union_subset sdiff_subset (less.subset.trans block.1)
  have hk : H⊆K := union_subset (fun _ h=>mem_union_left _ (mem_outN.mp h).1) (ol.trans subset_union_right)
  have pk : P⊆K := union_subset (fun _ p=>mem_union_left _ (mem_inN.mp p).1) (il.trans subset_union_right)
  have off : y∉K := fun h=>notMem_erase y V (ku h)
  have ne {i} (ik : i∈K) : i≠y := fun eq=>off (eq ▸ ik)
  have agree (i) (_ : i∈U) (j) (_ : j∈U) (out : i∉S ∨ j∉S) : G i j=D i j :=
    ite_eq_right (fun both=>out.elim (fun h=>h both.1) (fun h=>h both.2))
  have unchanged (i) (ik : i∈K) (j) (jk : j∈K) : E i j=G i j := by
    apply Bool.eq_iff_iff.mpr; simp [E,coreTwoSidedExtension,coreOutgoingExtension,ik,jk,ne ik,ne jk]
  have internal (i) (iu : i∈L) (j) (ju : j∈L) : G i j=A i j :=
    ite_eq_left ⟨less.subset iu,less.subset ju⟩
  have fwd (i) (il' : i∈L) : WeightedSD.row q G L b i=WeightedSD.row q A L b i := by
    unfold WeightedSD.row outW; rw [sum_congr rfl (fun j jl=>by rw [internal i il' j jl])]
  have rev (i) (il' : i∈L) : WeightedSD.col q G L c i=WeightedSD.col q A L c i := by
    unfold WeightedSD.col inW; rw [sum_congr rfl (fun j jl=>by rw [internal j jl i il'])]
  obtain ⟨u,up,um,ur,_,budget⟩ := CornerBlockExchange.replace block less.subset agree
    (fun i iu=>(pos i iu).1) (fun i iu=>(flat i iu).1) (fun i si=>(factor i si).1)
    (fun i il'=>(newPos i il').1) bm (fun i il'=>(fwd i il').trans (newFlat i il').1) zm
  have reverseBlock : Block (fun i j=>D j i) U S := ⟨block.1,block.2.1,block.2.2.2,block.2.2.1⟩
  obtain ⟨v,vp,vm,vc,_,cost⟩ := CornerBlockExchange.replace (G:=fun i j=>G j i) reverseBlock less.subset
    (fun i iu j ju h=>agree j ju i iu h.symm) (fun i iu=>(pos i iu).2) (fun i iu=>(flat i iu).2)
    (fun i si=>(factor i si).2) (fun i il'=>(newPos i il').2) cm (fun i il'=>(rev i il').trans (newFlat i il').2) pm
  have er (i) (ik : i∈K) : WeightedSD.row q E K u i=1 := by
    calc
      _ = WeightedSD.row q G K u i := by
        unfold WeightedSD.row outW; rw [sum_congr rfl (fun j jk=>by rw [unchanged i ik j jk])]
      _ = 1 := ur i ik
  have ec (i) (ik : i∈K) : WeightedSD.col q E K v i=1 := by
    calc
      _ = WeightedSD.col q G K v i := by
        unfold WeightedSD.col inW; rw [sum_congr rfl (fun j jk=>by rw [unchanged j jk i ik])]
      _ = 1 := vc i ik
  have sub : insert y K⊆V := insert_subset_iff.mpr ⟨yv,ku.trans (erase_subset ..)⟩
  have room : (insert y K).card<V.card := by
    apply card_lt_card (ssubset_iff_of_subset sub |>.mpr ?_)
    obtain ⟨i,si,no⟩ := exists_of_ssubset less
    refine ⟨i,mem_of_mem_erase (block.1 si),fun h=>?_⟩
    rcases mem_insert.mp h with eq|ik
    · exact (mem_erase.mp (block.1 si)).1 eq
    · exact (mem_union.mp ik).elim (fun iw=>(mem_sdiff.mp iw).2 si) no
  have freeE : QFree E (insert y K) q := safe free yv block parent head less.subset il ol inside apart hq
  have cut := CornerBlockExchange.light hq freeE small (mem_insert_self y K) off (subset_insert y K) room up um er vp vm ec
  have headEq : outN E K y=H := by
    ext j
    by_cases jk : j∈K
    · simp [outN,E,coreTwoSidedExtension,coreOutgoingExtension,off,jk,ne jk]
    · simp [outN,jk,show j∉H from fun h=>jk (hk h)]
  have parentEq : inN E K y=P := by
    ext j
    by_cases jk : j∈K
    · simp [inN,E,coreTwoSidedExtension,coreOutgoingExtension,off,jk]
    · simp [inN,jk,show j∉P from fun h=>jk (pk h)]
  have o := budget (outN D W y) (filter_subset _ _) O ol
  have i := cost (inN D W y) (filter_subset _ _) I il
  have inMass (F : CH.Digraph) (T : Finset ℕ) (a : ℕ→ℚ) : inW F T a y=mass (inN F T y) a :=
    outW_eq_mass (fun i j=>F j i) T a y
  rw [outW_eq_mass,headEq,inMass,parentEq] at cut
  rw [outW_eq_mass,inMass]
  exact cut.elim (fun h=>Or.inl (o ▸ h)) (fun h=>Or.inr (i ▸ h))

/-- Every smaller two-sided replacement, probed with the same two
    puncture distributions. No original arc inside the block is required. -/
def CannotReplace (q : ℕ) (D : CH.Digraph) (V S : Finset ℕ) (y : ℕ) (z p : ℕ→ℚ) : Prop :=
  ∀(A : CH.Digraph) (L I O : Finset ℕ),L⊂S → I⊆L → O⊆L → QFree A L q →
    (∀v∈O,∀t∈I,∀k,k≤q-2 → ¬ Walk A L v t k) →
    ∀b c : ℕ→ℚ,(∀i∈L,0<b i ∧ 0<c i) → mass L b=mass S z → mass L c=mass S p →
    (∀i∈L,WeightedSD.row q A L b i=mass S z ∧ WeightedSD.col q A L c i=mass S p) →
    let W := (V.erase y)\S
    (q:ℚ)*(outW D W z y+mass O b)<1 ∨ (q:ℚ)*(inW D W p y+mass I c)<1

open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (many : 1<(targets X.D X.V F B).card) {y h : X.V} (fresh : Fresh X F (y,h))
    (stuck : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V)
    {S} (bl : OldBlockAt X.D (graph X.D F) X.V y S) :
    let U := X.V.erase y.val
    ∃z p : ℕ→ℚ,(∀i∈U,0<z i ∧ 0<p i) ∧ mass U z=1 ∧ mass U p=1 ∧
      (∀i∈U,WeightedSD.row q X.D U z i=1 ∧ WeightedSD.col q X.D U p i=1) ∧
      (∀i∈S,WeightedSD.row q X.D S z i=mass S z ∧ WeightedSD.col q X.D S p i=mass S p) ∧
      1<(q:ℚ)*outW X.D U z y ∧ 1<(q:ℚ)*inW X.D U p y ∧ CannotReplace q X.D X.V S y z p := by
  intro U
  obtain ⟨z,p,pos,zm,pm,flat,_,factor,outH,inH,_⟩ :=
    CornerBlockExchange.on_source X hq small rp back step least many fresh stuck bl
  obtain ⟨t,ts,ty⟩ := bl.2.2.1
  obtain ⟨v,vs,yv⟩ := bl.2.2.2.1
  refine ⟨z,p,pos,zm,pm,flat,factor,outH,inH,?_⟩
  intro A L I O less il ol inside apart b c newPos bm cm newFlat
  exact substitute hq X.free small y.property bl.1 ⟨t,ts,(bl.2.1 t ts).1 ▸ ty⟩
    ⟨v,vs,(bl.2.1 v vs).2 ▸ yv⟩ less il ol inside apart pos zm pm flat factor newPos bm cm newFlat

#print axioms safe
#print axioms substitute
#print axioms on_source
end LeanCH.BR.Closure.CornerBlockSubstitution
