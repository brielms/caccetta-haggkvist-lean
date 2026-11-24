import checkpoints.shen_extension.ConsecutiveBlockerPool

namespace LeanCH.BR.Closure.RoutedPoolEscape
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open MandatoryTwoStep EqualColumnRepair RootedSplice DeleteRepair BlockerHeadRouting

/-- Any different parent of a head of x has an actual shortest witness
avoiding the entire class that forces x. -/
theorem shared_head_escape {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {x p y}
    (pv : p∈X.V) (yv : y∈X.V) (ne : p≠x)
    (xy : X.D x y=true) (py : X.D p y=true) (forces : ∀z∈K,Forces X.D X.V q z x) :
    ∃C,Cycle X.D (X.V\K) q C ∧ p∈C ∧ y∈C := by
  obtain ⟨C,c,pc,yc⟩ := edge_cycle X hq pv yv py
  have xc : x∉C := fun hit => ne (card_le_one.mp (c.incoming y yc).le
    _ (mem_inN.mpr ⟨pc,py⟩) _ (mem_inN.mpr ⟨hit,xy⟩))
  exact ⟨C,⟨fun z zc => mem_sdiff.mpr ⟨c.sub zc,fun zk => xc (forces z zk C c zc)⟩,
    c.size,c.heads,c.incoming⟩,pc,yc⟩

/-- Delete both class anchors and the marked bank of x-heads. Bypass j on
the surviving labels. If deletion pays the x-parents, an actual row must
collect more than one q-th of the deleted mass from the bank alone. Every
arc it uses there has a shortest-cycle destination in the class complement. -/
theorem bank_escape {q n} (X : Model q n) (hq : 2≤q) {K T : Finset ℕ} {h x j}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card) (xk : x∈K) (jk : j∈K) (xj : x≠j)
    (equal : ∀a∈K,∀b∈K,Forces X.D X.V q a b)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (pool : T⊆outN X.D (X.V\K) x)
    (credit : q*X.weights x≤X.weights x+X.weights j+(∑z∈T,X.weights z)) :
    ∃p∈(X.V\K)\T, X.D p x=false ∧
      score q X.D X.V X.weights p+X.weights x+X.weights j+(∑z∈T,X.weights z)
        ≤ (∑z∈X.V,X.weights z)+q*(∑z∈outN X.D T p,X.weights z) ∧
      ∀y∈outN X.D T p,∃C,Cycle X.D (X.V\K) q C ∧ p∈C ∧ y∈C := by
  classical
  let W := (X.V\T).erase x
  let U := W.erase j
  let H := outN X.D (X.V\K) j
  let E := repair X.D (inN X.D U j) (fun _ => outN X.D U j)
  have member {z} (zt : z∈T) := (mem_outN.mp (pool zt)).1
  have tv : T⊆X.V := fun _ zt => (mem_sdiff.mp (member zt)).1
  have avoid {z} (zk : z∈K) : z∉T := fun zt => (mem_sdiff.mp (member zt)).2 zk
  have xw : x∈X.V\T := mem_sdiff.mpr ⟨sub xk,avoid xk⟩
  have jw : j∈W := mem_erase.mpr ⟨xj.symm,mem_sdiff.mpr ⟨sub jk,avoid jk⟩⟩
  have wv : W⊆X.V := (erase_subset _ _).trans sdiff_subset
  have uv : U⊆X.V := (erase_subset _ _).trans wv
  have uw (p) (pu : p∈U) := mem_erase.mp (mem_of_mem_erase pu : p∈W)
  have missroot : ¬Covered X.D X.V q x j := forces_iff.mp (equal j jk x xk)
  have safe : QFree E U q := PunctureBypass.safe hq (X.free.mono_set wv) jw (by
    rintro ⟨C,c,jc⟩
    exact missroot ⟨C,⟨fun z zc => mem_erase.mpr ⟨(mem_erase.mp (c.sub zc)).1,wv (c.sub zc)⟩,
      c.size,c.heads,c.incoming⟩,jc⟩)
  have hu : H⊆U := by
    intro z zh
    obtain ⟨zw,jz⟩ := mem_outN.mp zh
    obtain ⟨zv,zk⟩ := mem_sdiff.mp zw
    have zt : z∉T := fun hit => xj (ComparableColumnCut.distinct_parents X hq zv (sub xk)
      (mem_outN.mp (pool hit)).2 jz (equal x xk j jk))
    exact mem_erase.mpr ⟨fun e => zk (e ▸ jk),mem_erase.mpr ⟨fun e => zk (e ▸ xk),mem_sdiff.mpr ⟨zv,zt⟩⟩⟩
  obtain ⟨_,pay,_⟩ := class_data X hq sub hk many equal minimum size
  have jpay := pay j jk
  change X.weights j≤∑z∈H,X.weights z at jpay
  have live : U.Nonempty := by
    have hn : H.Nonempty := by
      by_contra empty
      rw [not_nonempty_iff_eq_empty.mp empty,sum_empty] at jpay
      have := X.positive j (sub jk)
      omega
    exact hn.mono hu
  have less : U.card<X.V.card := (card_erase_lt_of_mem jw).trans_le (card_le_card wv)
  have fail : ¬Strict q E U X.weights := fun strict => less.not_ge
    (X.minimal E U X.weights live safe (fun z zu => X.positive z (uv zu))
      ((sum_le_sum_of_subset_of_nonneg uv (by intros; omega)).trans X.bounded) strict)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,pu,low⟩ := fail
  have total (f : ℕ→ℕ) : (∑z∈U,f z)+f j+f x+(∑z∈T,f z)=∑z∈X.V,f z := by
    rw [sum_erase_add W f jw,sum_erase_add _ f xw,sum_sdiff tv]
  have mass := total X.weights
  let O := outN X.D U p
  let G := outN E U p
  let L := ∑z∈outN X.D T p,X.weights z
  have old := total (fun z => if X.D p z=true then X.weights z else 0)
  have split : score q X.D X.V X.weights p=X.weights p+q*((∑z∈O,X.weights z)+
      (if X.D p j=true then X.weights j else 0)+(if X.D p x=true then X.weights x else 0)+L) := by
    simp only [O,L,score,outN,sum_filter]
    rw [old]
  have high := nat_strict.mp X.strict p (uv pu)
  have form : score q E U X.weights p=X.weights p+q*(∑z∈G,X.weights z) := by simp only [score,G,outN,sum_filter]
  rw [form] at low
  have inc : O⊆G := fun z zo => mem_outN.mpr ⟨(mem_outN.mp zo).1,repair_old (mem_outN.mp zo).2⟩
  have grow := sum_le_sum_of_subset_of_nonneg inc (f:=X.weights) (by intros; omega)
  have gain := Nat.mul_le_mul_left q grow
  have px : X.D p x=false := Bool.eq_false_iff.mpr (by
    intro hit
    have nj : X.D p j=false := Bool.eq_false_iff.mpr (fun yes =>
      xj (ComparableColumnCut.distinct_heads X hq (uv pu) (sub xk) hit yes (equal x xk j jk)))
    have none : outN X.D T p=∅ := eq_empty_iff_forall_notMem.mpr (by
      intro z zh
      obtain ⟨zt,pz⟩ := mem_outN.mp zh
      have miss := missing_arc X hq (mem_erase.mpr ⟨xj,sub xk⟩) (uv pu) (tv zt) hit
        (mem_outN.mp (pool zt)).2 (forces_iff.mp (equal x xk j jk))
      rw [miss] at pz
      contradiction)
    have zero : L=0 := by simp [L,none]
    simp [nj,hit,zero,Nat.mul_add] at split
    omega)
  have retained : (∑z∈O,X.weights z)+(if X.D p j=true then X.weights j else 0)≤∑z∈G,X.weights z := by
    by_cases pj : X.D p j=true
    · have more : H⊆G := fun z zh => mem_outN.mpr ⟨hu zh,repair_new (mem_inN.mpr ⟨pu,pj⟩)
        (mem_outN.mpr ⟨hu zh,(mem_outN.mp zh).2⟩)⟩
      have sep : Disjoint O H := disjoint_left.mpr (fun z zo zh => by
        have hit := (mem_outN.mp zo).2
        rw [missing_arc X hq (mem_erase.mpr ⟨xj.symm,sub jk⟩) (uv pu) (uv (hu zh)) pj
          (mem_outN.mp zh).2 missroot] at hit
        contradiction)
      have both := sum_le_sum_of_subset_of_nonneg (union_subset inc more) (f:=X.weights) (by intros; omega)
      rw [sum_union sep] at both
      simpa only [pj,ite_true] using (Nat.add_le_add_left jpay (∑z∈O,X.weights z)).trans both
    · simpa [pj] using grow
  simp [px,Nat.mul_add] at split
  have g := Nat.mul_le_mul_left q retained
  rw [Nat.mul_add] at g
  have bounds : score q X.D X.V X.weights p+X.weights x+X.weights j+(∑z∈T,X.weights z)≤
      (∑z∈X.V,X.weights z)+q*L := by
    by_cases pj : X.D p j=true <;> simp [pj] at g split <;> omega
  have reached : (outN X.D T p).Nonempty := by
    by_contra no
    have zero : L=0 := by simp [L,not_nonempty_iff_eq_empty.mp no]
    rw [zero,Nat.mul_zero] at bounds
    omega
  obtain ⟨y,hit⟩ := reached
  have pne := (uw p pu).1
  have pk : p∉K := fun inK => pne (ComparableColumnCut.distinct_parents X hq (tv (mem_outN.mp hit).1)
    (uv pu) (mem_outN.mp hit).2 (mem_outN.mp (pool (mem_outN.mp hit).1)).2 (equal p inK x xk))
  refine ⟨p,mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨uv pu,pk⟩,(mem_sdiff.mp (uw p pu).2).2⟩,px,bounds,?_⟩
  intro z zh
  obtain ⟨zt,pz⟩ := mem_outN.mp zh
  exact shared_head_escape X hq (uv pu) (tv zt) pne (mem_outN.mp (pool zt)).2 pz (fun v vk => equal v vk x xk)

/-- Feed the forced bank at the next class member into a second deletion.
The exceptional alternative includes a bound on normalized order; it is
impossible when the sending anchor has minimum weight. -/
theorem class_escape {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ} {h}
    (sub : K⊆X.V) (hk : h∈K) (many : 2≤K.card)
    (equal : ∀a∈K,∀b∈K,Forces X.D X.V q a b)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card) :
    ∃p x j T,Blocks X K p x ∧ j∈K ∧ j≠x ∧ T.Nonempty ∧
      (∀y∈T,∃r k,Blocks X K r j ∧ Walk X.D (X.V\K) y r k ∧
        k+2=MandatoryExcursion.span X.D X.V q x j) ∧
      ((X.weights h<X.weights x ∧ X.V.card≤q*(q*(q-1)) ∧
        X.weights j+(∑z∈outN X.D X.V x,X.weights z)<q*X.weights x) ∨
       ∃v∈(X.V\K)\T,X.D v x=false ∧
        score q X.D X.V X.weights v+X.weights x+X.weights j+(∑z∈T,X.weights z)
           ≤ (∑z∈X.V,X.weights z)+q*(∑z∈outN X.D T v,X.weights z) ∧
        (outN X.D T v).Nonempty ∧
        ∀y∈outN X.D T v,∃C,Cycle X.D (X.V\K) q C ∧ v∈C ∧ y∈C) := by
  classical
  obtain ⟨p,x,j,b,jk,jx,_,thin,_,live,route⟩ := ConsecutiveBlockerPool.consecutive_pool X hq sub hk many equal minimum size
  let O := outN X.D (X.V\K) x
  let S := spareHeads X K x
  let T := O\S
  have xk := b.2.1
  obtain ⟨light,heads⟩ := class_profile X hq sub hk equal minimum size
  have part := sum_sdiff (show S⊆O from filter_subset _ _) (f:=X.weights)
  change (∑z∈T,X.weights z)+(∑z∈S,X.weights z)=∑z∈O,X.weights z at part
  change (∑z∈S,X.weights z)<X.weights x at thin
  have eq : O=outN X.D X.V x := heads x xk
  rw [eq] at part
  refine ⟨p,x,j,T,b,jk,jx,live,route,?_⟩
  by_cases credit : q*X.weights x≤X.weights x+X.weights j+(∑z∈T,X.weights z)
  · obtain ⟨v,vt,vx,cost,cycles⟩ := bank_escape X hq sub hk many xk jk jx.symm equal minimum size
      (T:=T) sdiff_subset credit
    have high := nat_strict.mp X.strict v (mem_sdiff.mp (mem_sdiff.mp vt).1).1
    have nonempty : (outN X.D T v).Nonempty := by
      by_contra no
      rw [not_nonempty_iff_eq_empty.mp no,sum_empty,Nat.mul_zero] at cost
      omega
    exact Or.inr ⟨v,vt,vx,cost,nonempty,cycles⟩
  · have loss : X.weights j+(∑z∈outN X.D X.V x,X.weights z)<q*X.weights x := by omega
    have floor := PunctureWeightCoverage.flow_floor X (sub xk) minimum size
    have high : X.weights h<X.weights x := by
      by_contra! small
      have lt := Nat.mul_le_mul_left q small
      have jm := minimum j (sub jk)
      have decomp : (q-1)*X.weights h+X.weights h=q*X.weights h := by
        rw [←Nat.succ_mul]; congr 1; omega
      omega
    have limited : X.V.card≤q*(q*(q-1)) := by
      by_contra! big
      have floor' := PunctureWeightCoverage.flow_floor X (sub xk) minimum (k:=q*(q-1)) (by omega)
      have cap := Nat.mul_le_mul_left q (light x xk)
      rw [Nat.mul_assoc] at floor'
      omega
    exact Or.inl ⟨high,limited,loss⟩

#print axioms class_escape
#print axioms bank_escape
end LeanCH.BR.Closure.RoutedPoolEscape
