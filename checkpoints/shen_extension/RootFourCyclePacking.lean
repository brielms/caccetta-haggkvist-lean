import checkpoints.shen_extension.PaidLayerDescent

namespace LeanCH.BR.Closure.RootFourCyclePacking
open BRq2 BRq3 BR45 Finset DeficitLevels PaidLayerDescent

/-- A set hitting every original four-cycle through h, at a vertex other than h.
The order around the cycle is h,a,z,b. -/
def CutsFour (D : CH.Digraph) (V : Finset ℕ) (h : ℕ) (M : Finset ℕ) : Prop :=
  ∀ a ∈ outN D V h \ M, ∀ z ∈ V \ M, ∀ b ∈ inN D V h \ M,
    D a z=true → D z b≠true

/-- Any small transversal of the four-cycles at h obeys this inequality on a
least source, using only minimum outdegree and the lower-degree order laws. -/
theorem native_cut {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) {M : Finset ℕ} (small : M.card<s) (cut : CutsFour S.G S.V h M) :
    15*s+9*(inN S.G S.V h).card+4*(outN S.G S.V h).card+14 ≤
      9*S.V.card+10*M.card := by
  classical
  let O := outN S.G S.V h
  let I := inN S.G S.V h
  let K := S.V \ insert h (O∪I)
  let A := O\M
  let X := (K\M).filter (fun z => ∃ a∈A, S.G a z=true)
  let Y := (K\M)\X
  let T := A∪X
  let MO := O∩M
  let MK := K∩M
  have ov : O ⊆ S.V := outN_subset
  have iv : I ⊆ S.V := filter_subset _ _
  have kv : K ⊆ S.V := sdiff_subset
  have ao : A ⊆ O := sdiff_subset
  have xk : X ⊆ K\M := filter_subset _ _
  have xv : X ⊆ S.V := xk.trans (sdiff_subset.trans kv)
  have tv : T ⊆ S.V := union_subset (ao.trans ov) xv
  have oh : h∉O := fun hit => loopfree S.free (by decide) hv (mem_outN.mp hit).2
  have ih : h∉I := fun hit => loopfree S.free (by decide) hv (mem_inN.mp hit).2
  have oi : Disjoint O I := disjoint_left.mpr (by
    intro x xo xi
    exact digonfree S.free (by decide) hv (ov xo) (mem_outN.mp xo).2 (mem_inN.mp xi).2)
  have noI {a b} (aO : a∈O) (bI : b∈I) : S.G a b≠true := fun ab =>
    S.free h 3 (by decide) (by decide) (.step (ov aO) (mem_outN.mp aO).2
      (.step (iv bI) ab (.step hv (mem_inN.mp bI).2 (.refl _))))
  have noH {a} (aA : a∈A) : S.G a h≠true :=
    digonfree S.free (by decide) hv (ov (ao aA)) (mem_outN.mp (ao aA)).2
  have inK {z} (zv : z∈S.V) (zh : z≠h) (zo : z∉O) (zi : z∉I) : z∈K :=
    mem_sdiff.mpr ⟨zv,by simp [zh,zo,zi]⟩
  have outK {z} (zk : z∈K) : z≠h ∧ z∉O ∧ z∉I := by
    simpa only [mem_insert,mem_union,not_or] using (mem_sdiff.mp zk).2
  have cO : A.card+MO.card=O.card := by simpa only [A,MO,inter_comm] using card_sdiff_add_card_inter O M
  have cK : (K\M).card+MK.card=K.card := by simpa only [MK,inter_comm] using card_sdiff_add_card_inter K M
  have cY : Y.card+X.card=(K\M).card := card_sdiff_add_card_eq_card xk
  have cT : T.card=A.card+X.card := card_union_of_disjoint (disjoint_left.mpr (fun z za zx =>
    (outK (mem_sdiff.mp (xk zx)).1).2.1 (ao za)))
  have hmiss : h∉O∪I := by simp [oh,ih]
  have cV : K.card+(O.card+I.card+1)=S.V.card := by
    have eq := card_sdiff_add_card_eq_card (insert_subset hv (union_subset ov iv))
    rwa [card_insert_of_notMem hmiss,card_union_of_disjoint oi] at eq
  have mO : MO.card≤M.card := card_le_card inter_subset_right
  have hA : h∉A := fun hA => oh (ao hA)
  have hT : h∉T := by
    intro hit
    rcases mem_union.mp hit with za|zx
    · exact hA za
    · exact (outK (mem_sdiff.mp (xk zx)).1).1 rfl
  have liveA : A.Nonempty := by
    have deg : s≤O.card := S.deg h hv
    exact card_pos.mp (by omega)
  have proper {Z : Finset ℕ} (zv : Z⊆S.V) (hm : h∉Z) : Z.card<S.V.card :=
    card_lt_card ⟨zv,fun rev => hm (rev hv)⟩
  have outsideA {a} (ha : a∈A) : outN S.G S.V a ⊆ outN S.G A a ∪ (X∪(MO∪MK)) := by
    intro z hit
    obtain ⟨zv,az⟩ := mem_outN.mp hit
    by_cases zo : z∈O
    · by_cases zm : z∈M
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (mem_inter.mpr ⟨zo,zm⟩)))
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨zo,zm⟩,az⟩)
    · have zk := inK zv (fun e => noH ha (e ▸ az)) zo (fun zi => noI (ao ha) zi az)
      by_cases zm : z∈M
      · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨zk,zm⟩)))
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨zk,zm⟩,a,ha,az⟩))
  have outsideT {t} (ht : t∈T) : outN S.G S.V t ⊆ outN S.G T t ∪ (M∪Y) := by
    intro z hit
    obtain ⟨zv,tz⟩ := mem_outN.mp hit
    by_cases zm : z∈M
    · exact mem_union_right _ (mem_union_left _ zm)
    by_cases zt : z∈T
    · exact mem_union_left _ (mem_outN.mpr ⟨zt,tz⟩)
    have zo : z∉O := fun zo => zt (mem_union_left _ (mem_sdiff.mpr ⟨zo,zm⟩))
    have zx : z∉X := fun zx => zt (mem_union_right _ zx)
    have avoid : z≠h ∧ z∉I := by
      rcases mem_union.mp ht with ta|tx
      · exact ⟨fun e => noH ta (e ▸ tz),fun zi => noI (ao ta) zi tz⟩
      · obtain ⟨tkm,a,ha,at'⟩ := mem_filter.mp tx
        have tk := (mem_sdiff.mp tkm).1
        have tm := (mem_sdiff.mp tkm).2
        exact ⟨fun e => (outK tk).2.2 (mem_inN.mpr ⟨kv tk,e ▸ tz⟩),
          fun zi => cut a ha t (mem_sdiff.mpr ⟨kv tk,tm⟩) z (mem_sdiff.mpr ⟨zi,zm⟩) at' tz⟩
    exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨mem_sdiff.mpr
      ⟨inK zv avoid.1 zo avoid.2,zm⟩,zx⟩))
  obtain ⟨a,ha,lowA⟩ := light S laws (ao.trans ov) (proper (ao.trans ov) hA) liveA
  obtain ⟨t,ht,lowT⟩ := light S laws tv (proper tv hT) (liveA.mono subset_union_left)
  have dA := S.deg a (ov (ao ha))
  have dT := S.deg t (tv ht)
  have leA := card_le_card (outsideA ha)
  have leT := card_le_card (outsideT ht)
  have a1 := card_union_le (outN S.G A a) (X∪(MO∪MK))
  have a2 := card_union_le X (MO∪MK)
  have a3 := card_union_le MO MK
  have t1 := card_union_le (outN S.G T t) (M∪Y)
  have t2 := card_union_le M Y
  change 15*s+9*I.card+4*O.card+14 ≤ 9*S.V.card+10*M.card
  omega

/-- The two first layers give the sharper bound if the parents of h have a
known indegree floor t. The rest of the graph can have smaller indegrees. -/
theorem parent_cut {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) {M : Finset ℕ} (small : M.card<s)
    (cut : CutsFour S.G S.V h M) (parent_left : (inN S.G S.V h \ M).Nonempty)
    {t : ℕ} (floorIn : ∀ b∈inN S.G S.V h, t≤(inN S.G S.V b).card) :
    s+t+(outN S.G S.V h).card+(inN S.G S.V h).card+1 ≤ S.V.card+M.card+
      ((outN S.G S.V h).card-1)/3+((inN S.G S.V h).card-1)/3 := by
  classical
  let O := outN S.G S.V h
  let I := inN S.G S.V h
  let K := S.V \ insert h (O∪I)
  let A := O\M
  let B := I\M
  have ov : O⊆S.V := outN_subset
  have iv : I⊆S.V := filter_subset _ _
  have av : A⊆S.V := sdiff_subset.trans ov
  have bv : B⊆S.V := sdiff_subset.trans iv
  have oh : h∉O := fun e => loopfree S.free (by decide) hv (mem_outN.mp e).2
  have ih : h∉I := fun e => loopfree S.free (by decide) hv (mem_inN.mp e).2
  have apart : Disjoint O I := disjoint_left.mpr (by
    intro z zo zi
    exact digonfree S.free (by decide) hv (ov zo) (mem_outN.mp zo).2 (mem_inN.mp zi).2)
  have no {x z} (xo : x∈O) (zi : z∈I) : S.G x z≠true := fun edge =>
    S.free h 3 (by decide) (by decide) (.step (ov xo) (mem_outN.mp xo).2
      (.step (iv zi) edge (.step hv (mem_inN.mp zi).2 (.refl _))))
  have hmiss : h∉O∪I := by simp [oh,ih]
  have total : K.card+(O.card+I.card+1)=S.V.card := by
    have eq := card_sdiff_add_card_eq_card (insert_subset hv (union_subset ov iv))
    rwa [card_insert_of_notMem hmiss,card_union_of_disjoint apart] at eq
  have properA : A.card<S.V.card := card_lt_card ⟨av,fun sub => oh (mem_sdiff.mp (sub hv)).1⟩
  have properB : B.card<S.V.card := card_lt_card ⟨bv,fun sub => ih (mem_sdiff.mp (sub hv)).1⟩
  have liveA : A.Nonempty := by
    have size : s≤O.card := S.deg h hv
    have count := card_sdiff_add_card_inter O M
    have atMost : (O∩M).card≤M.card := card_le_card inter_subset_right
    exact card_pos.mp (show 0<(O\M).card by omega)
  obtain ⟨a,ha,lowA⟩ := light S laws av properA liveA
  obtain ⟨b,hb,minB⟩ := B.exists_min_image (fun x => (inN S.G B x).card) parent_left
  let R : CH.Digraph := fun x y => S.G y x
  have reverseSafe : QFree R B 3 := S.free.reverse.mono_set bv
  have floorB : ∀ v∈B, (inN S.G B b).card≤(outN R B v).card := minB
  have low : (inN S.G B b).card<s := by
    by_contra! high
    exact properB.not_ge (S.least R B reverseSafe (fun v h => high.trans (floorB v h)) parent_left)
  have lowB := laws _ low R B reverseSafe floorB parent_left
  let P := outN S.G S.V a \ A
  let Q := inN S.G S.V b \ B
  have az := (mem_sdiff.mp ha).1
  have bi := (mem_sdiff.mp hb).1
  have sideP {z} (hz : z∈P) : z∈S.V ∧ z≠h ∧ z∉I := by
    have e := (mem_outN.mp (mem_sdiff.mp hz).1).2
    exact ⟨outN_subset (mem_sdiff.mp hz).1,fun eq =>
      digonfree S.free (by decide) hv (ov az) (mem_outN.mp az).2 (eq ▸ e),fun zi => no az zi e⟩
  have sideQ {z} (hz : z∈Q) : z∈S.V ∧ z≠h ∧ z∉O := by
    have e := (mem_inN.mp (mem_sdiff.mp hz).1).2
    exact ⟨(mem_inN.mp (mem_sdiff.mp hz).1).1,fun eq =>
      digonfree S.free (by decide) (iv bi) hv (mem_inN.mp bi).2 (eq ▸ e),fun zo => no zo bi e⟩
  have united : P∪Q ⊆ K∪M := by
    intro z hz
    by_cases zm : z∈M
    · exact mem_union_right _ zm
    apply mem_union_left
    rcases mem_union.mp hz with zp|zq
    · obtain ⟨zv,zh,zi⟩ := sideP zp
      have zo : z∉O := fun zo => (mem_sdiff.mp zp).2 (mem_sdiff.mpr ⟨zo,zm⟩)
      exact mem_sdiff.mpr ⟨zv,by simp [zh,zo,zi]⟩
    · obtain ⟨zv,zh,zo⟩ := sideQ zq
      have zi : z∉I := fun zi => (mem_sdiff.mp zq).2 (mem_sdiff.mpr ⟨zi,zm⟩)
      exact mem_sdiff.mpr ⟨zv,by simp [zh,zo,zi]⟩
  have both : P∩Q ⊆ K∩M := by
    intro z hz
    obtain ⟨zp,zq⟩ := mem_inter.mp hz
    obtain ⟨zv,zh,zi⟩ := sideP zp
    have zo := (sideQ zq).2.2
    refine mem_inter.mpr ⟨mem_sdiff.mpr ⟨zv,by simp [zh,zo,zi]⟩,?_⟩
    by_contra zm
    exact cut a ha z (mem_sdiff.mpr ⟨zv,zm⟩) b hb (mem_outN.mp (mem_sdiff.mp zp).1).2
      (mem_inN.mp (mem_sdiff.mp zq).1).2
  have bound := Nat.add_le_add (card_le_card united) (card_le_card both)
  rw [card_union_add_card_inter,card_union_add_card_inter] at bound
  have coverP : outN S.G S.V a ⊆ outN S.G A a ∪ P := by
    intro z hz; by_cases za : z∈A
    · exact mem_union_left _ (mem_outN.mpr ⟨za,(mem_outN.mp hz).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,za⟩)
  have coverQ : inN S.G S.V b ⊆ inN S.G B b ∪ Q := by
    intro z hz; by_cases zb : z∈B
    · exact mem_union_left _ (mem_inN.mpr ⟨zb,(mem_inN.mp hz).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,zb⟩)
  have pa := (S.deg a (av ha)).trans ((card_le_card coverP).trans (card_union_le _ _))
  have qb := (floorIn b bi).trans ((card_le_card coverQ).trans (card_union_le _ _))
  have aSmall : A.card≤O.card := card_le_card sdiff_subset
  have bSmall : B.card≤I.card := card_le_card sdiff_subset
  change s+t+O.card+I.card+1 ≤ S.V.card+M.card+(O.card-1)/3+(I.card-1)/3
  omega

/-- The native floor at any root of indegree at least s. -/
theorem high_indegree_cut {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) (high : s≤(inN S.G S.V h).card)
    {M : Finset ℕ} (small : M.card<s) (cut : CutsFour S.G S.V h M) : s+14≤10*M.card := by
  have bound := native_cut S laws hv small cut
  have := S.deg h hv
  have := S.order
  omega

/-- At a high-indegree root, a local indegree floor only on its parents
gives the stronger, rounded four-cycle transversal bound. -/
theorem high_parent_cut {s} (S : Origin 3 s) (laws : ∀ j<s, OrderLaw 3 j (3*j+1))
    {h : ℕ} (hv : h∈S.V) (high : s≤(inN S.G S.V h).card)
    {M : Finset ℕ} (small : M.card<s) (cut : CutsFour S.G S.V h M)
    (parents : ∀ b∈inN S.G S.V h, s≤(inN S.G S.V b).card) :
    s+1 ≤ M.card+2*((s-1)/3) := by
  have remain : (inN S.G S.V h \ M).Nonempty := by
    have total := card_sdiff_add_card_inter (inN S.G S.V h) M
    have sub : (inN S.G S.V h ∩ M).card≤M.card := card_le_card inter_subset_right
    apply card_pos.mp
    omega
  have bound := parent_cut S laws hv small cut remain parents
  have := S.deg h hv
  have := S.order
  omega

#print axioms high_indegree_cut
#print axioms high_parent_cut
#print axioms parent_cut

#print axioms native_cut
end LeanCH.BR.Closure.RootFourCyclePacking
