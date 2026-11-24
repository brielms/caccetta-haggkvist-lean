import checkpoints.shen_extension.CornerBlockPayment
import checkpoints.shen_extension.FlatChildClosure
import checkpoints.shen_extension.FlatChildExchange
import LeanCH.BR.BRWeightedUnitCoreExtension

namespace LeanCH.BR.Closure.CornerBlockExchange
open Finset BRq2 BRq3 BR45 BRsub WeightedSD CornerHeadRecurrence

/-- The flat puncture factors through any one-sided module. The representative
    row in the contracted host determines the exact internal level. -/
theorem factor {q : ℕ} {D : CH.Digraph} {U S : Finset ℕ} (hq : 2≤q)
    (free : QFree D U q) (small : SmallerSmallRow q U.card)
    (sub : S⊆U) (size : 2≤S.card) (proper : S≠U) (uniform : OutUniform D U S)
    {z : ℕ→ℚ} (pos : ∀i∈U,0<z i) (flat : ∀i∈U,WeightedSD.row q D U z i=mass U z) :
    (∀i∈S,WeightedSD.row q D S z i=mass S z) ∧ (S.card : ZMod q)=1 := by
  obtain ⟨r,rs⟩ := card_pos.mp (show 0<S.card by omega)
  have paid := outContract_feasible sub rs uniform (small.induced free S sub proper) z
    (fun i si=>(pos i (sub si)).le) (mass U z) (fun i iu=>(flat i iu).ge)
  have tight := positive_feasible_rows_tight_of_smallRow hq
    (smaller_outContract_smallRow small free sub rs size uniform) (contractWeight S r z)
    (contractWeight_positive sub rs pos) (fun i iu=>by rw [contractWeight_mass sub rs]; exact paid i iu)
    r (mem_insert_self ..)
  rw [outContract_root_row D rs,contractWeight_mass sub rs] at tight
  have inside (i) (si : i∈S) : WeightedSD.row q D S z i=mass S z := by
    have eq := flat i (sub si)
    rw [outUniform_core_row sub rs uniform si z] at eq
    linarith only [eq,tight]
  exact ⟨inside,tight_rows_card_mod q D S z
    (ne_of_gt (sum_pos (fun i si=>pos i (sub si)) ⟨r,rs⟩)) inside⟩

private def splice (L : Finset ℕ) (z b : ℕ→ℚ) (i : ℕ) := if i∈L then b i else z i

/-- Exchange the whole internal distribution, keeping each exterior weight.
    The last identity is the exact change at an arbitrary probe vertex. -/
theorem replace {q : ℕ} {D G : CH.Digraph} {U S L : Finset ℕ} (block : Block D U S)
    (ls : L⊆S) (agree : ∀i∈U,∀j∈U,(i∉S ∨ j∉S) → G i j=D i j)
    {z b : ℕ→ℚ} (pos : ∀i∈U,0<z i) (flat : ∀i∈U,WeightedSD.row q D U z i=1)
    (inside : ∀i∈S,WeightedSD.row q D S z i=mass S z)
    (bp : ∀i∈L,0<b i) (bm : mass L b=mass S z) (br : ∀i∈L,WeightedSD.row q G L b i=mass S z)
    (zm : mass U z=1) :
    let K := (U\S)∪L
    ∃u : ℕ→ℚ,(∀i∈K,0<u i) ∧ mass K u=1 ∧ (∀i∈K,WeightedSD.row q G K u i=1) ∧
      (∀y,outW D K u y=outW D (U\S) z y+outW D L b y) ∧
      ∀Z⊆U\S,∀O⊆L,mass (Z∪O) u=mass Z z+mass O b := by
  classical
  intro K
  let W := U\S
  let u := splice L z b
  have dis : Disjoint W L := disjoint_left.mpr (fun _ iw il=>(mem_sdiff.mp iw).2 (ls il))
  have outer {i} (iw : i∈W) : u i=z i := ite_eq_right (fun il=>disjoint_left.mp dis iw il)
  have inner {i} (il : i∈L) : u i=b i := ite_eq_left il
  have split (i) : outW D K u i=outW D W z i+outW D L b i := by
    change (∑ j∈W∪L, if D i j=true then u j else 0)=_
    rw [sum_union dis]
    exact congrArg₂ (·+·) (sum_congr rfl fun j jw=>by rw [outer jw])
      (sum_congr rfl fun j jl=>by rw [inner jl])
  have norm : mass K u=1 := by
    change (∑i∈W∪L,u i)=1
    rw [sum_union dis,sum_congr rfl (fun i iw=>outer iw),sum_congr rfl (fun i il=>inner il)]
    change mass W z+mass L b=1
    rw [bm]; exact (sum_sdiff block.1).trans zm
  have ku : K⊆U := union_subset sdiff_subset (ls.trans block.1)
  have newSplit (i) (ik : i∈K) : outW G K u i=outW D W z i+outW G L b i := by
    change (∑j∈W∪L,if G i j=true then u j else 0)=_
    rw [sum_union dis]
    exact congrArg₂ (·+·) (sum_congr rfl fun j jw=>by
      rw [outer jw,agree i (ku ik) j (mem_sdiff.mp jw).1 (Or.inr (mem_sdiff.mp jw).2)])
      (sum_congr rfl fun j jl=>by rw [inner jl])
  refine ⟨u,?_,norm,?_,split,?_⟩
  · intro i ik
    rcases mem_union.mp ik with iw|il
    · rw [outer iw]; exact pos i (mem_sdiff.mp iw).1
    · rw [inner il]; exact bp i il
  · intro i ik
    rcases mem_union.mp ik with iw|il
    · obtain ⟨r,rs⟩ := card_pos.mp (show 0<S.card by have := block.2.1; omega)
      have adj {j} (js : j∈S) := block.2.2.1 j js r rs i (mem_sdiff.mp iw).1 (mem_sdiff.mp iw).2
      have same : outW D L b i=outW D S z i := by
        cases bit : D i r with
        | true =>
          have left : outW D L b i=mass L b := sum_congr rfl (fun j jl=>by simp [(adj (ls jl)).trans bit])
          have right : outW D S z i=mass S z := sum_congr rfl (fun j js=>by simp [(adj js).trans bit])
          exact left.trans (bm.trans right.symm)
        | false =>
          have left : outW D L b i=0 := sum_eq_zero (fun j jl=>by simp [(adj (ls jl)).trans bit])
          have right : outW D S z i=0 := sum_eq_zero (fun j js=>by simp [(adj js).trans bit])
          exact left.trans right.symm
      have old := flat i (mem_sdiff.mp iw).1
      rw [WeightedSD.row,outW_split block.1 z i] at old
      have sameG : outW G L b i=outW D L b i := sum_congr rfl (fun j jl=>by
        rw [agree i (mem_sdiff.mp iw).1 j (block.1 (ls jl)) (Or.inl (mem_sdiff.mp iw).2)])
      rw [WeightedSD.row,newSplit i (mem_union_left _ iw),outer iw,sameG,same,add_comm (outW D W z i)]; exact old
    · have old := flat i (block.1 (ls il))
      rw [outUniform_core_row block.1 (ls il) block.2.2.2 (ls il),inside i (ls il)] at old
      have eq := br i il
      unfold WeightedSD.row at eq
      rw [WeightedSD.row,newSplit i (mem_union_right _ il),inner il,mul_add]
      linarith only [old,eq]
  · intro Z zw O ol
    exact (sum_union (dis.mono zw ol)).trans (congrArg₂ (·+·)
      (sum_congr rfl (fun i zi=>outer (zw zi))) (sum_congr rfl (fun i oi=>inner (ol oi))))

private theorem opposite {q : ℕ} {D : CH.Digraph} {U V : Finset ℕ} (hq : 2≤q)
    (free : QFree D V q) (small : SmallerSmallRow q V.card) (sub : U⊆V) (proper : U≠V)
    {z : ℕ→ℚ} (zp : ∀i∈U,0<z i) (zm : mass U z=1) (zr : ∀i∈U,WeightedSD.row q D U z i=1) :
    ∃p : ℕ→ℚ,(∀i∈U,0<p i) ∧ mass U p=1 ∧ ∀i∈U,WeightedSD.col q D U p i=1 := by
  let a := fun i=>(z i:ℝ)
  have am : realMass U a=1 := by rw [show realMass U a=(mass U z:ℝ) from realMass_rat ..,zm]; norm_num
  have ar (i) (iu : i∈U) : realCol q (fun i j=>D j i) U a i=1 := by
    change realRow q D U (fun j=>(z j:ℝ)) i=1
    rw [realRow_rat,zr i iu]; norm_num
  obtain ⟨b,bm,bf⟩ := FlatChildExchange.opposite_law (E:=fun i j=>D j i) hq free.reverse small sub proper
    am (fun i iu=>by change (0:ℝ)<(z i:ℝ); exact_mod_cast zp i iu) ar
  obtain ⟨p,same,cols⟩ := real_unit_column_rational (D:=D) hq (fun i : U=>b i)
    (funext (fun i=>(realMatrix_col q D U b i).trans (bf i i.property).2))
  refine ⟨extendWeight U p,?_,?_,fun i iu=>(col_extendWeight q D U p ⟨i,iu⟩).trans (congrFun cols ⟨i,iu⟩)⟩
  · intro i iu
    rw [extendWeight_on U p ⟨i,iu⟩]
    have h := (bf i iu).1
    rw [←same ⟨i,iu⟩] at h
    exact_mod_cast h
  · rw [mass_extendWeight]
    have norm : (∑i : U,(p i:ℝ))=1 := by simp_rw [same]; exact (sum_coe_sort U b).trans bm
    exact_mod_cast norm

/-- A flat puncture opposite a strict native orientation must charge the
    missing label above one. This uses the actual strict weighting. -/
private theorem pressure {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {y : ℕ} (_yv : y∈V)
    {z w : ℕ→ℚ} (pos : ∀i∈V.erase y,0<z i) (norm : mass (V.erase y) z=1)
    (flat : ∀i∈V.erase y,WeightedSD.row q D (V.erase y) z i=1)
    (wp : ∀i∈V,0<w i) (high : ∀i∈V,mass V w<WeightedSD.col q D V w i) :
    1<(q:ℚ)*outW D (V.erase y) z y := by
  classical
  let U := V.erase y
  let a := fun i=>if i∈U then z i else 0
  have sub : U⊆V := erase_subset .. 
  have zero (i) (_ : i∈V) (off : i∉U) : a i=0 := ite_eq_right off
  have am : mass V a=1 := by
    rw [←mass_subset_zero sub zero]; exact (sum_congr rfl (fun i iu=>ite_eq_left iu)).trans norm
  have out (i) : outW D V a i=outW D U z i := by
    rw [←outW_subset_zero sub zero]; exact sum_congr rfl (fun j ju=>by rw [show a j=z j from ite_eq_left ju])
  by_contra! low
  have rows (i) (iv : i∈V) : WeightedSD.row q D V a i≤1 := by
    by_cases iy : i=y
    · subst i; rw [WeightedSD.row,out,show a y=0 from ite_eq_right (notMem_erase y V),zero_add]; exact low
    · have iu : i∈U := mem_erase.mpr ⟨iy,iv⟩
      rw [WeightedSD.row,out,show a i=z i from ite_eq_left iu]; exact (flat i iu).le
  have left := sum_le_sum (s:=V) (fun i iv=>mul_le_mul_of_nonneg_left (rows i iv) (wp i iv).le)
  simp only [mul_one] at left
  have live : U.Nonempty := by
    by_contra! empty
    change mass U z=1 at norm
    simp [empty,mass] at norm
  obtain ⟨r,ru⟩ := live
  have nonneg (i) (_ : i∈V) : 0≤a i := by
    dsimp [a]; split <;> first | exact (pos i ‹_›).le | exact le_rfl
  have ap : 0<a r := by rw [show a r=z r from ite_eq_left ru]; exact pos r ru
  have right := sum_lt_sum (s:=V)
    (fun i iv=>mul_le_mul_of_nonneg_left (high i iv).le (nonneg i iv))
    ⟨r,sub ru,mul_lt_mul_of_pos_left (high r (sub ru)) ap⟩
  rw [←sum_mul,show (∑i∈V,a i)=1 from am,one_mul,←rational_cross_rows] at right
  exact right.not_ge left

/-- At a smaller flat puncture the same vertex cannot exceed threshold in
    opposite directions. The exact unit equations also rule out equality. -/
theorem light {q N : ℕ} {D : CH.Digraph} {V K : Finset ℕ} {y : ℕ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q N)
    (yv : y∈V) (off : y∉K) (kv : K⊆V) (room : (insert y K).card<N)
    {z p : ℕ→ℚ} (zp : ∀i∈K,0<z i) (zm : mass K z=1) (zr : ∀i∈K,WeightedSD.row q D K z i=1)
    (pp : ∀i∈K,0<p i) (pm : mass K p=1) (pc : ∀i∈K,WeightedSD.col q D K p i=1) :
    (q:ℚ)*outW D K z y<1 ∨ (q:ℚ)*inW D K p y<1 := by
  by_contra! both
  have o := lt_of_le_of_ne both.1 (unit_core_contact_nontight hq z zr y).1.symm
  have h := lt_of_le_of_ne both.2 (unit_core_contact_nontight (D:=fun i j=>D j i) hq p pc y).1.symm
  let a := fun i=>(z i:ℝ)
  let b := fun i=>(p i:ℝ)
  have norm (f : ℕ→ℚ) (fm : mass K f=1) : realMass K (fun i=>(f i:ℝ))=1 := by
    rw [realMass_rat,fm]; norm_num
  have cols (i) (ik : i∈K) : realCol q D K b i=1 := by
    change realCol q D K (fun j=>(p j:ℝ)) i=1
    rw [realCol_rat,pc i ik]; norm_num
  have rows (i) (ik : i∈K) : realRow q D K a i=1 := by
    change realRow q D K (fun j=>(z j:ℝ)) i=1
    rw [realRow_rat,zr i ik]; norm_num
  have heavyO : 1<(q:ℝ)*realMass (outN D K y) a := by
    rw [realMass_rat,←outW_eq_mass]; exact_mod_cast o
  have heavyI : 1<(q:ℝ)*realMass (inN D K y) b := by
    rw [realMass_rat]
    have eq : mass (inN D K y) p=inW D K p y := (outW_eq_mass (fun i j=>D j i) K p y).symm
    rw [eq]; exact_mod_cast h
  have dual : RealDual q D K 1 b := ⟨fun i ik=>by change (0:ℝ)≤(p i:ℝ); exact_mod_cast (pp i ik).le,
    norm p pm,fun i ik=>(cols i ik).le⟩
  obtain ⟨a',ha,t,ht,k,len,path⟩ := FlatChildClosure.heavy_return hq small (free.mono_set kv) off room
    (filter_subset _ _) (filter_subset _ _) dual cols (norm z zm)
    (fun i ik=>by exact_mod_cast zp i ik) rows heavyO heavyI
  have run : Walk D V y t (k+1) := .step (kv (mem_outN.mp ha).1) (mem_outN.mp ha).2 (path.mono kv)
  exact free y _ (by omega) (by omega) (run.snoc yv (mem_inN.mp ht).2)

/-- The two original pivot contacts are above threshold. Simultaneously
    exchanging a proper subgraph of the block for any pair of flat
    distributions of the same respective masses forces one below threshold. -/
theorem exchange {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (yv : y∈V) (block : Block D (V.erase y) S) (outside : S≠V.erase y)
    {w r z : ℕ→ℚ} (wp : ∀i∈V,0<w i) (wh : ∀i∈V,mass V w<WeightedSD.row q D V w i)
    (rp : ∀i∈V,0<r i) (rh : ∀i∈V,mass V r<WeightedSD.col q D V r i)
    (zp : ∀i∈V.erase y,0<z i) (zm : mass (V.erase y) z=1)
    (zr : ∀i∈V.erase y,WeightedSD.row q D (V.erase y) z i=1) :
    let U := V.erase y
    let W := U\S
    ∃p : ℕ→ℚ,(∀i∈U,0<p i) ∧ mass U p=1 ∧ (∀i∈U,WeightedSD.col q D U p i=1) ∧
      (S.card : ZMod q)=1 ∧ (∀i∈S,WeightedSD.row q D S z i=mass S z ∧ WeightedSD.col q D S p i=mass S p) ∧
      1<(q:ℚ)*outW D U z y ∧ 1<(q:ℚ)*inW D U p y ∧
      ∀ L⊂S,∀ b c : ℕ→ℚ,(∀i∈L,0<b i ∧ 0<c i) → mass L b=mass S z → mass L c=mass S p →
        (∀i∈L,WeightedSD.row q D L b i=mass S z ∧ WeightedSD.col q D L c i=mass S p) →
        (q:ℚ)*(outW D W z y+outW D L b y)<1 ∨ (q:ℚ)*(inW D W p y+inW D L c y)<1 := by
  intro U W
  have uv : U⊆V := erase_subset .. 
  have smaller := card_erase_lt_of_mem yv
  have less : SmallerSmallRow q U.card := fun G K room fr=>small G K (room.trans smaller) fr
  have rev : Block (fun i j=>D j i) U S := ⟨block.1,block.2.1,block.2.2.2,block.2.2.1⟩
  have properU : U≠V := fun eq=>ne_of_lt (show U.card<V.card from smaller) (congrArg card eq)
  obtain ⟨p,pp,pm,pc⟩ := opposite hq free small uv properU zp zm zr
  obtain ⟨inside,modS⟩ := factor hq (free.mono_set uv) less block.1 block.2.1 outside block.2.2.2 zp
    (fun i iu=>(zr i iu).trans zm.symm)
  have pin := (factor hq (free.reverse.mono_set uv) less rev.1 rev.2.1 outside rev.2.2.2 pp
    (fun i iu=>(pc i iu).trans pm.symm)).1
  refine ⟨p,pp,pm,pc,modS,fun i si=>⟨inside i si,pin i si⟩,
    pressure yv zp zm zr rp rh,pressure (D:=fun i j=>D j i) yv pp pm pc wp wh,?_⟩
  intro L proper b c pos bm cm flat
  obtain ⟨a,ap,am,ar,ao,_⟩ := replace block proper.subset (fun _ _ _ _ _=>rfl) zp zr inside (fun i il=>(pos i il).1) bm
    (fun i il=>(flat i il).1) zm
  obtain ⟨e,ep,em,ec,ei,_⟩ := replace rev proper.subset (fun _ _ _ _ _=>rfl) pp pc pin (fun i il=>(pos i il).2) cm
    (fun i il=>(flat i il).2) pm
  let K := W∪L
  have ku : K⊆U := union_subset sdiff_subset (proper.subset.trans block.1)
  have off : y∉K := fun h=>notMem_erase y V (ku h)
  have sub : insert y K⊆V := insert_subset_iff.mpr ⟨yv,ku.trans uv⟩
  have room : (insert y K).card<V.card := by
    apply card_lt_card (ssubset_iff_of_subset sub |>.mpr ?_)
    obtain ⟨i,si,il⟩ := exists_of_ssubset proper
    refine ⟨i,uv (block.1 si),fun hit=>?_⟩
    rcases mem_insert.mp hit with eq|ik
    · exact (mem_erase.mp (block.1 si)).1 eq
    · exact (mem_union.mp ik).elim (fun iw=>(mem_sdiff.mp iw).2 si) il
  have bound := light hq free small yv off (ku.trans uv) room ap am ar ep em ec
  change (q:ℚ)*outW D K a y<1 ∨ (q:ℚ)*outW (fun i j=>D j i) K e y<1 at bound
  rw [ao y,ei y] at bound
  exact bound

private theorem const_out (D : CH.Digraph) (L : Finset ℕ) (m : ℚ) (i : ℕ) :
    outW D L (fun _=>m) i=(outN D L i).card*m := by simp [outW_eq_mass,mass]

private theorem uniform_price {q : ℕ} {D : CH.Digraph} {L : Finset ℕ} (live : L.Nonempty)
    (regular : ∀i∈L,1+q*(outN D L i).card=L.card) (m : ℚ) :
    let c := m/L.card
    mass L (fun _=>c)=m ∧ ∀i∈L,WeightedSD.row q D L (fun _=>c) i=m := by
  intro c
  have nz : (L.card:ℚ)≠0 := by exact_mod_cast (card_pos.mpr live).ne'
  have total : (L.card:ℚ)*c=m := by dsimp [c]; field_simp
  refine ⟨by simpa [mass] using total,?_⟩
  intro i il
  have eq : 1+(q:ℚ)*(outN D L i).card=L.card := by exact_mod_cast regular i il
  rw [WeightedSD.row,const_out,←total,←eq]; ring

open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- In the stopped multi-head case, every proper internally regular
    replacement is tested at the same pivot using the same two laws. In
    particular this tests all proper shortest cycles and singletons. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (many : 1<(targets X.D X.V F B).card) {y h : X.V} (fresh : Fresh X F (y,h))
    (stuck : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V)
    {S} (bl : OldBlockAt X.D (graph X.D F) X.V y S) :
    let U := X.V.erase y.val
    let W := U\S
    ∃z p : ℕ→ℚ,(∀i∈U,0<z i ∧ 0<p i) ∧ mass U z=1 ∧ mass U p=1 ∧
      (∀i∈U,WeightedSD.row q X.D U z i=1 ∧ WeightedSD.col q X.D U p i=1) ∧
      (S.card : ZMod q)=1 ∧ (∀i∈S,WeightedSD.row q X.D S z i=mass S z ∧ WeightedSD.col q X.D S p i=mass S p) ∧
      1<(q:ℚ)*outW X.D U z y ∧ 1<(q:ℚ)*inW X.D U p y ∧
      ∀L⊂S,L.Nonempty → (∀i∈L,1+q*(outN X.D L i).card=L.card ∧ 1+q*(inN X.D L i).card=L.card) →
        (q:ℚ)*(outW X.D W z y+(outN X.D L y).card*(mass S z/L.card))<1 ∨
        (q:ℚ)*(inW X.D W p y+(inN X.D L y).card*(mass S p/L.card))<1 := by
  intro U W
  obtain ⟨_,_,_,z,zp,zm,zr⟩ := (SharedArcPivot.alternatives X hq small step least many fresh).resolve_left stuck
  have off : h.val∉S := fun hs=>Bool.noConfusion (fresh.2.2.2.symm.trans ((bl.2.1 h hs).2.trans fresh.2.2.1))
  have hu : h.val∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) y.property (eq ▸ fresh.2.2.1),h.property⟩
  have high (i) (iv : i∈X.V) : mass X.V r<WeightedSD.col q X.D X.V r i := by
    refine (back i iv).trans_le (add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum ?_) (Nat.cast_nonneg q)))
    intro j jv
    by_cases ed : graph X.D J j i=true
    · have native : X.D j i=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
      simp [ed,native]
    · simp only [ite_eq_right ed]; split <;> first | exact (rp j jv).le | rfl
  let w := fun i=>(X.weights i:ℚ)
  obtain ⟨p,pp,pm,pc,modS,inner,head,parent,cut⟩ := exchange hq X.free small y.property bl.1
    (fun eq=>off (eq ▸ hu)) (w:=w) (fun i iv=>by change (0:ℚ)<(X.weights i:ℚ); exact_mod_cast X.positive i iv)
    X.strict rp high zp zm zr
  refine ⟨z,p,fun i iu=>⟨zp i iu,pp i iu⟩,zm,pm,fun i iu=>⟨zr i iu,pc i iu⟩,modS,inner,head,parent,?_⟩
  intro L proper live reg
  have massPos (a : ℕ→ℚ) (pos : ∀i∈U,0<a i) : 0<mass S a :=
    sum_pos (fun i si=>pos i (bl.1.1 si)) (live.mono proper.subset)
  have den : (0:ℚ)<L.card := by exact_mod_cast card_pos.mpr live
  have fwd := uniform_price live (fun i il=>(reg i il).1) (mass S z)
  have rev := uniform_price (D:=fun i j=>X.D j i) live (fun i il=>(reg i il).2) (mass S p)
  have loss := cut L proper _ _ (fun _ _=>⟨div_pos (massPos z zp) den,div_pos (massPos p pp) den⟩)
    fwd.1 rev.1 (fun i il=>⟨fwd.2 i il,rev.2 i il⟩)
  have incoming : inW X.D L (fun _=>mass S p/L.card) y=(inN X.D L y).card*(mass S p/L.card) :=
    const_out (fun i j=>X.D j i) L _ y
  rwa [const_out,incoming] at loss

#print axioms factor
#print axioms replace
#print axioms exchange
#print axioms on_source
end LeanCH.BR.Closure.CornerBlockExchange
