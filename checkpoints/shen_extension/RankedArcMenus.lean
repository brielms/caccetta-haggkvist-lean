import checkpoints.shen_extension.RankedHeadChoices

namespace LeanCH.BR.RankedArcMenus
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure RankedHeadChoices

private theorem allowed_of_le {q D E U w i j} (hq : 1≤q)
    (rowLe : ∀v∈U,row q E U w v ≤ row q D U w v)
    (le : row q E U w i ≤ row q D U w j) (ok : Allowed q E U w i) :
    Allowed q D U w j := by
  have nn : (0:ℚ)≤q-1 := sub_nonneg.mpr (by exact_mod_cast hq)
  exact ⟨ok.1.trans_le le,fun e eu=>(ok.2 e eu).trans (add_le_add
    (mul_le_mul_of_nonneg_left (sub_le_sub_right le _) nn) (rowLe e eu))⟩

private theorem row_mono {q : ℕ} {D E U w} (sub : ∀i j,E i j=true → D i j=true)
    (nn : ∀v∈U,0≤w v) (i : ℕ) : row q E U w i ≤ row q D U w i := by
  unfold WeightedSD.row
  rw [outW_eq_mass,outW_eq_mass]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (α:=ℚ) q)
  apply mass_mono _ (fun j jj=>nn j (outN_subset jj))
  exact fun j jj=>mem_outN.mpr ⟨outN_subset jj,sub i j (mem_outN.mp jj).2⟩

/-- Any row passing both tests must lose strictly less than the price of
    the tail of the erased arc. Test the entire out-neighbourhood of the
    head: its mass is strictly sufficient, and its ball never hits a parent
    of the head. This step needs no saturation or separation. -/
theorem score_above_tail {q D V w c a d} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0<w i) (high : mass V w<c)
    (flat : ∀i∈V,row q D V w i=c) (dv : d∈V) (ah : a∈outN D V d) :
    ∀ E : CH.Digraph, (∀i j,E i j=true → D i j=true) →
    ∀i∈V\{a,d},Allowed q E (V\{a,d}) w i → c-(q:ℚ)*w d < row q E (V\{a,d}) w i := by
  let U := V\{a,d}
  let H := outN D V a
  have av := outN_subset ah
  have da := (mem_outN.mp ah).2
  have ad : a≠d := fun eq=>loopfree free (by omega) dv (eq ▸ da)
  have sub := insert_subset av (singleton_subset_iff.mpr dv)
  have us : U⊆V := sdiff_subset
  have hs : H⊆U := by
    intro h hh
    have hit := (mem_outN.mp hh).2
    refine mem_sdiff.mpr ⟨outN_subset hh,fun hw=>?_⟩
    rcases mem_insert.mp hw with eq|s
    · exact loopfree free (by omega) av (eq ▸ hit)
    · exact digonfree free (by omega) dv av da (mem_singleton.mp s ▸ hit)
  have count := card_sdiff_add_card_eq_card sub
  rw [card_pair ad] at count
  have room : U.card+1<V.card := by dsimp [U]; omega
  have split : mass U w+(w a+w d)=mass V w := by
    simpa [U,mass,sum_pair ad] using sum_sdiff sub (f:=w)
  have root := flat a av
  rw [WeightedSD.row,outW_eq_mass] at root
  have heavy : mass U w < q*mass H w := by dsimp only [H]; linarith only [root,split,high,pos d dv]
  have live : H.Nonempty := by
    by_contra! empty
    rw [empty] at heavy
    simp [mass] at heavy
    exact heavy.not_ge (mass_nonneg fun i iu=>(pos i (us iu)).le)
  obtain ⟨j,jb,_,bad⟩ := RankedMerge.pair_obstruction hq (free.mono_set us) small room hs live w
    (fun i iu=>pos i (us iu)) heavy
  obtain ⟨h,hh,jh⟩ := mem_ballSet.mp jb
  obtain ⟨ju,l,short,p⟩ := mem_ball.mp jh
  have off : D j a ≠ true := fun ja=>free a (l+1+1) (by omega) (by omega)
    (.step (outN_subset hh) (mem_outN.mp hh).2 ((p.mono us).snoc av ja))
  have cap : outW D {a,d} w j ≤ w d := by
    cases ed : D j d <;> simp [outW,sum_pair ad,off,ed,(pos d dv).le]
  intro E subE i _ paid
  by_contra! le
  have leRows : row q E U w i ≤ row q D U w j := by
    rw [FreshMenuExitRules.restricted_row sub (flat j (us ju))]
    exact le.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg q)) _)
  have ok := allowed_of_le (by omega : 1≤q)
    (fun v _=>row_mono subE (fun z zu=>(pos z (us zu)).le) v) leRows paid
  rcases bad with low|⟨e,ee,low⟩
  · exact ok.1.not_ge low
  · exact low.not_ge (ok.2 e (mem_sdiff.mp ee).1)

theorem less_than_tail {q D V w c a d} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0<w i) (high : mass V w<c)
    (flat : ∀i∈V,row q D V w i=c) (dv : d∈V) (ah : a∈outN D V d)
    (i) (iu : i∈V\{a,d}) (paid : Allowed q D (V\{a,d}) w i) : outW D {a,d} w i < w d := by
  have sc := score_above_tail hq free small pos high flat dv ah D (fun _ _ hit=>hit) i iu paid
  rw [FreshMenuExitRules.restricted_row (insert_subset (outN_subset ah) (singleton_subset_iff.mpr dv))
    (flat i (mem_sdiff.mp iu).1)] at sc
  exact (mul_lt_mul_iff_right₀ (show (0:ℚ)<q by exact_mod_cast (show 0<q by omega))).mp (by linarith only [sc])

/-- The arithmetic test for a row losing only the head a of d→a. Its
    second inequality tests every retained row at exactly the same prices. -/
def Single (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) (a d : ℕ) : Prop :=
  let U := V\{a,d}
  (q:ℚ)*w a < c-mass U w ∧ ∀e∈U,((q:ℚ)-1)*w a + outW D {a,d} w e ≤ c-mass U w

private theorem rows {q D V w c a d} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0<w i) (high : mass V w<c)
    (flat : ∀i∈V,row q D V w i=c) (dv : d∈V) (ah : a∈outN D V d)
    {i} (iu : i∈V\{a,d}) :
    Allowed q D (V\{a,d}) w i ↔ D i d≠true ∧ (D i a≠true ∨ Single q D V w c a d) := by
  have av := outN_subset ah
  have ad : a≠d := fun eq=>loopfree free (by omega) dv (eq ▸ (mem_outN.mp ah).2)
  have sub := insert_subset av (singleton_subset_iff.mpr dv)
  have test (e) (eu : e∈V\{a,d}) := FreshMenuExitRules.ranked_costs (by omega : 0<q) sub
    (flat i (mem_sdiff.mp iu).1) (flat e (mem_sdiff.mp eu).1)
  have noD (ok : Allowed q D (V\{a,d}) w i) : D i d≠true := by
    intro ed
    have lower := less_than_tail hq free small pos high flat dv ah i iu ok
    cases ea : D i a <;> simp [outW,sum_pair ad,ed,ea] at lower
    linarith only [lower,pos a av]
  constructor
  · intro ok
    have nd := noD ok
    refine ⟨nd,or_iff_not_imp_left.mpr (fun yes=>?_)⟩
    have ia : D i a=true := by simpa using yes
    have loss : outW D {a,d} w i=w a := by simp [outW,sum_pair ad,nd,ia]
    exact ⟨loss ▸ (test i iu).1.mp ok.1,fun e eu=>loss ▸ (test e eu).2.mp (ok.2 e eu)⟩
  · rintro ⟨nd,cond⟩
    by_cases ia : D i a=true
    · have one := cond.resolve_left (not_not.mpr ia)
      have loss : outW D {a,d} w i=w a := by simp [outW,sum_pair ad,ia,nd]
      exact ⟨(test i iu).1.mpr (loss.symm ▸ one.1),
        fun e eu=>(test e eu).2.mpr (loss.symm ▸ one.2 e eu)⟩
    · have zero : outW D {a,d} w i=0 := by simp [outW,sum_pair ad,ia,nd]
      have split : mass (V\{a,d}) w+mass {a,d} w=mass V w := sum_sdiff sub
      have nn := mass_nonneg (V:={a,d}) (fun j jw=>(pos j (sub jw)).le)
      apply And.intro ((test i iu).1.mpr (by rw [zero,mul_zero]; linarith only [split,high,nn]))
      intro e eu
      apply (test e eu).2.mpr
      rw [zero,mul_zero,zero_add,outW_eq_mass]
      have cap := mass_mono (outN_subset (D:=D) (W:={a,d}) (y:=e)) (fun j jw=>(pos j (sub jw)).le)
      linarith only [cap,split,high]

/-- Short walks ending at d cannot pass its head a. Thus in V minus a,d,
    detecting parents of d gives precisely the native heads of d. -/
private theorem tail_geometry {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q) {a d h}
    (dv : d∈X.V) (ah : a∈outN X.D X.V d) (hu : h∈X.V\{a,d}) :
    (∀i∈ball X.D (X.V\{a,d}) h (q-2),X.D i d≠true) ↔ X.D d h=true := by
  have av := outN_subset ah
  have old := (mem_sdiff.mp hu).1
  constructor
  · intro no
    by_contra off
    obtain ⟨_,m,short,p⟩ := mem_ball.mp
      ((DepositTrace.returns_iff_not_head X (by omega) dv old).mpr off)
    have cut := DeleteRepair.head_avoided X.free av (mem_outN.mp ah).2 p (by omega)
    have gone : d∉X.V\{a,d} := fun du=>(mem_sdiff.mp du).2 (mem_insert_of_mem (mem_singleton_self _))
    obtain ⟨l,i,b,bound,iu,bu,walk,hit⟩ := first_exit_of_walk cut hu gone
    have bv := mem_sdiff.mp (mem_sdiff.mp bu).1
    have bd : b=d := by
      by_contra ne
      exact (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨bv.1,fun bw=>by
        rcases mem_insert.mp bw with ba|one
        · exact bv.2 (mem_singleton.mpr ba)
        · exact ne (mem_singleton.mp one)⟩)
    exact no i (mem_ball.mpr ⟨iu,l,by omega,walk⟩) (bd ▸ hit)
  · intro dh i ib id
    obtain ⟨_,l,short,p⟩ := mem_ball.mp ib
    exact X.free d (l+1+1) (by omega) (by omega)
      (.step old dh ((p.mono sdiff_subset).snoc dv id))

/-- Split a labelled native walk at its first physically missing arc. -/
private theorem first_gap {D E : CH.Digraph} {U : Finset ℕ} {h i k}
    (p : Walk D U h i k) (hu : h∈U) :
    Walk E U h i k ∨ ∃l x y m, l+1+m=k ∧ x∈U ∧ Walk E U h x l ∧ y∈U ∧
      D x y=true ∧ E x y=false ∧ Walk D U y i m := by
  induction p with
  | refl => exact Or.inl (.refl _)
  | @step a b i n bu ab path ih =>
    by_cases e : E a b=true
    · rcases ih bu with yes|⟨l,x,y,m,eq,xu,pathToCut,yu,xy,off,pathAfterCut⟩
      · exact Or.inl (.step bu e yes)
      · exact Or.inr ⟨l+1,x,y,m,by omega,xu,.step bu e pathToCut,yu,xy,off,pathAfterCut⟩
    · exact Or.inr ⟨0,a,b,n,by omega,hu,.refl _,bu,ab,Bool.eq_false_iff.mpr e,path⟩

structure ArcMenus (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) (a d : ℕ) : Prop where
  exact_heads :
    let U := V\{a,d}
    let K := heads q D U w (q-2)
    (Single q D V w c a d → K = (outN D V d ∩ U)) ∧
    (¬Single q D V w c a d → K = (outN D V d ∩ outN D V a))
  deficit : ∀H⊆V\{a,d},RowBills q D (V\{a,d}) H w (q-2) →
    mass (V\{a,d}) w - q*mass H w =
      ((q:ℚ)-1)*w a-(c-mass V w)+q*mass (outN D V d \ insert a H) w ∧
    (q:ℚ)*mass H w < mass (V\{a,d}) w
  cuts : ∀E : CH.Digraph,(∀i j,E i j=true → D i j=true) →
    let U := V\{a,d}
    let K := heads q E U w (q-2)
    let T := outN D V d
    (∀h∈K\T,∃i∈U,D i d=true ∧ i∉ballSet E U K (q-2) ∧
      ∃l x y m,l+1+m≤q-2 ∧ x∈U ∧ Walk E U h x l ∧ y∈U ∧
        D x y=true ∧ E x y=false ∧ w y<w d ∧ Walk D U y i m) ∧
    (mass U w < q*mass K w ↔ ((q:ℚ)-1)*w a-(c-mass V w)+
      q*mass (T \ insert a K) w < q*mass (K\T) w)

theorem on_arc {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) {w c} (pos : ∀i∈X.V,0<w i)
    (high : mass X.V w<c) (flat : ∀i∈X.V,row q X.D X.V w i=c)
    {a d} (dv : d∈X.V) (ah : a∈outN X.D X.V d) : ArcMenus q X.D X.V w c a d := by
  classical
  let U := X.V\{a,d}
  let K := heads q X.D U w (q-2)
  have av := outN_subset ah
  have da := (mem_outN.mp ah).2
  have ad : a≠d := fun eq=>loopfree X.free (by omega) dv (eq ▸ da)
  have sub := insert_subset av (singleton_subset_iff.mpr dv)
  have ok {i} (iu : i∈U) := rows hq X.free small pos high flat dv ah iu
  have tail : K⊆outN X.D X.V d := by
    intro h hk
    obtain ⟨hu,all⟩ := mem_filter.mp hk
    exact mem_outN.mpr ⟨(mem_sdiff.mp hu).1,(tail_geometry X hq dv ah hu).mp (fun i ib=>
      ((ok (ball_subset ib)).mp (all i ib)).1)⟩
  constructor
  · change (Single q X.D X.V w c a d → K=_) ∧ (¬Single q X.D X.V w c a d → K=_)
    constructor
    · intro one
      apply Subset.antisymm (subset_inter tail (filter_subset _ _))
      intro h hh
      obtain ⟨dh,hu⟩ := mem_inter.mp hh
      have no := (tail_geometry X hq dv ah hu).mpr (mem_outN.mp dh).2
      exact mem_filter.mpr ⟨hu,fun i ib=>(ok (ball_subset ib)).mpr ⟨no i ib,Or.inr one⟩⟩
    · intro one
      ext h
      constructor
      · intro hk
        obtain ⟨hu,all⟩ := mem_filter.mp hk
        have inside := (avoid_iff (k:=q-2) sub hu).mp (by
          intro i ib j jw
          have z := (ok (ball_subset ib)).mp (all i ib)
          rcases mem_insert.mp jw with rfl|s
          · exact z.2.resolve_right one
          · exact mem_singleton.mp s ▸ z.1)
        rw [show q-2+1=q-1 by omega] at inside
        refine mem_inter.mpr ⟨tail hk,mem_outN.mpr ⟨(mem_sdiff.mp hu).1,?_⟩⟩
        by_contra off
        have back := (DepositTrace.returns_iff_not_head X (by omega) av (mem_sdiff.mp hu).1).mpr off
        exact (mem_sdiff.mp (inside back)).2 (mem_insert_self ..)
      · intro both
        obtain ⟨dh,ahh⟩ := mem_inter.mp both
        have hv := outN_subset dh
        have au := (mem_outN.mp ahh).2
        have du := (mem_outN.mp dh).2
        have hu : h∈U := mem_sdiff.mpr ⟨hv,fun hw=>by
          rcases mem_insert.mp hw with eq|s
          · exact loopfree X.free (by omega) av (eq ▸ au)
          · exact loopfree X.free (by omega) dv (mem_singleton.mp s ▸ du)⟩
        apply mem_filter.mpr
        refine ⟨hu,fun i ib=>(ok (ball_subset ib)).mpr ⟨(tail_geometry X hq dv ah hu).mpr du i ib,Or.inl ?_⟩⟩
        obtain ⟨_,l,short,path⟩ := mem_ball.mp ib
        exact fun ia=>X.free a (l+1+1) (by omega) (by omega)
          (.step hv au ((path.mono sdiff_subset).snoc av ia))
  · intro H hs bills
    have ht := ((row_bills_iff (by omega : 1≤q) hs).mp bills).trans tail
    have apart : Disjoint ({a}:Finset ℕ) H := disjoint_left.mpr (fun i ia ih=>
      (mem_sdiff.mp (hs ih)).2 ((mem_singleton.mp ia) ▸ mem_insert_self ..))
    have identity := FreshMenuExitRules.star_deficit (d:=d) (W:={a}) (S:=H)
      (insert_subset dv (singleton_subset_iff.mpr av)) (by simpa using ad.symm)
      (singleton_subset_iff.mpr ah) ht apart (flat d dv)
    have eq : mass U w-q*mass H w =
        ((q:ℚ)-1)*w a-(c-mass X.V w)+q*mass (outN X.D X.V d\insert a H) w := by
      simpa only [U,Finset.pair_comm d a,mass,sum_singleton,singleton_union] using identity
    have floor := strict_atom_floor_of_proper hq X.free (small.induced X.free) w
      (fun i iv=>(pos i iv).le) c high (fun i iv=>(flat i iv).ge) a av
    have rem := mass_nonneg (fun i (ii : i∈outN X.D X.V d\insert a H)=>(pos i (outN_subset (mem_sdiff.mp ii).1)).le)
    exact ⟨eq,by linarith only [eq,floor,mul_nonneg (Nat.cast_nonneg (α:=ℚ) q) rem]⟩
  · intro E subE U' K' T
    have ks : K'⊆U' := filter_subset _ _
    have us : U'⊆X.V := sdiff_subset
    have rowLe (j) (_ : j∈U') := row_mono (q:=q) subE (fun i (iu : i∈U')=>(pos i (us iu)).le) j
    constructor
    · intro h hh
      obtain ⟨hk,miss⟩ := mem_sdiff.mp hh
      have hu := ks hk
      have fail : ¬∀i∈ball X.D U' h (q-2),X.D i d≠true :=
        fun no=>miss (mem_outN.mpr ⟨us hu,(tail_geometry X hq dv ah hu).mp no⟩)
      push Not at fail
      obtain ⟨i,ib,id⟩ := fail
      have iu := ball_subset ib
      have unseen : i∉ballSet E U' K' (q-2) := by
        intro seen
        obtain ⟨k,kk,ik⟩ := mem_ballSet.mp seen
        have original := allowed_of_le (by omega : 1≤q) rowLe (rowLe i iu) ((mem_filter.mp kk).2 i ik)
        exact ((ok iu).mp original).1 id
      obtain ⟨_,b,short,p⟩ := mem_ball.mp ib
      rcases first_gap (E:=E) p hu with back|⟨l,x,y,m,len,xu,pathToCut,yu,xy,off,pathAfterCut⟩
      · exact False.elim (unseen (mem_ballSet.mpr ⟨h,hk,mem_ball.mpr ⟨iu,b,short,back⟩⟩))
      have allowed := (mem_filter.mp hk).2 x (mem_ball.mpr ⟨xu,l,by omega,pathToCut⟩)
      have score := score_above_tail hq X.free small pos high flat dv ah E subE x xu allowed
      have newHead : y∉outN E U' x := fun yy=>Bool.noConfusion (off.symm.trans (mem_outN.mp yy).2)
      have ss : insert y (outN E U' x) ⊆ outN X.D X.V x := insert_subset
        (mem_outN.mpr ⟨us yu,xy⟩) (fun v vv=>mem_outN.mpr ⟨us (outN_subset vv),subE x v (mem_outN.mp vv).2⟩)
      have cost := mass_mono ss (fun v vv=>(pos v (outN_subset vv)).le)
      have cost' : w y+mass (outN E U' x) w ≤ mass (outN X.D X.V x) w := by
        simpa only [mass,sum_insert newHead] using cost
      have fx := flat x (us xu)
      rw [WeightedSD.row,outW_eq_mass] at score fx
      have cheaper : w y<w d := (mul_lt_mul_iff_right₀
        (show (0:ℚ)<q by exact_mod_cast (show 0<q by omega))).mp (by
          linarith only [score,fx,mul_le_mul_of_nonneg_left cost' (Nat.cast_nonneg (α:=ℚ) q)])
      exact ⟨i,iu,id,unseen,l,x,y,m,by omega,xu,pathToCut,yu,xy,off,cheaper,pathAfterCut⟩
    · have sep : Disjoint ({a}:Finset ℕ) (K'∩T) := disjoint_left.mpr (fun j ja jk=>
        (mem_sdiff.mp (ks (mem_inter.mp jk).1)).2 ((mem_singleton.mp ja) ▸ mem_insert_self ..))
      have identity := FreshMenuExitRules.star_deficit (d:=d) (W:={a}) (S:=K'∩T)
        (insert_subset dv (singleton_subset_iff.mpr av)) (by simpa using ad.symm)
        (singleton_subset_iff.mpr ah) inter_subset_right sep (flat d dv)
      have rem : T \ insert a (K'∩T) = T \ insert a K' := by
        ext j
        simp only [mem_sdiff,mem_insert,mem_inter]
        tauto
      change mass (X.V\{d,a}) w-q*mass (K'∩T) w =
        ((q:ℚ)-1)*mass {a} w-(c-mass X.V w)+q*mass (T\({a}∪(K'∩T))) w at identity
      rw [Finset.pair_comm d a,singleton_union,rem] at identity
      simp only [mass,sum_singleton] at identity
      have split : mass (K'∩T) w + mass (K'\T) w = mass K' w := sum_inter_add_sum_sdiff K' T w
      change mass U' w-q*mass (K'∩T) w = ((q:ℚ)-1)*w a-(c-mass X.V w)+q*mass (T\insert a K') w at identity
      constructor <;> intro bill <;> linarith only [identity,bill,congrArg (fun s:ℚ=>(q:ℚ)*s) split]

/-- Replay on every native source; a second registration instantiates the
    universal statement at the physical labels already present in a family. -/
structure OnSource {q n} (X : ShortestCycleWeights.Model q n) (w : ℕ→ℚ) (c : ℚ) : Prop where
  arcs : ∀d∈X.V,∀a∈outN X.D X.V d,ArcMenus q X.D X.V w c a d

@[aesop safe forward (immediate := [hq,small,pos,unit,high,flat]) (rule_sets := [CHGraphFamilies])]
theorem source_rule {q n w c} {X : ShortestCycleWeights.Model q n} (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (pos : ∀i∈X.V,0<w i) (unit : mass X.V w=1)
    (high : 1<c) (flat : ∀i∈X.V,row q X.D X.V w i=c) : OnSource X w c :=
  ⟨fun _ dv _ ah=>on_arc X hq small pos (unit ▸ high) flat dv ah⟩

@[aesop safe forward (immediate := [source,side]) (rule_sets := [CHGraphFamilies])]
theorem marked_arc {q n w c a keep d} {X : ShortestCycleWeights.Model q n}
    (source : OnSource X w c) (side : FreshMenuExitRules.PricedParents X w a keep d) :
    ArcMenus q X.D X.V w c a d :=
  source.arcs d (mem_inN.mp side.second).1 a (mem_outN.mpr ⟨side.root,(mem_inN.mp side.second).2⟩)

#print axioms less_than_tail
/-- Keeping arcs into cheaper vertices protects the native deficit on every
    head bank at these weights. This condition is automatic at a minimum-price
    tail. Both the original and pruned graphs use the same physical carrier. -/
theorem protected_cuts {q D V w c a d} (arc : ArcMenus q D V w c a d)
    (nn : ∀v∈V,0≤w v) (floor : c-mass V w<((q:ℚ)-1)*w a)
    {E : CH.Digraph} (sub : ∀i j,E i j=true → D i j=true)
    (keep : ∀x∈V\{a,d},∀y∈V\{a,d},w y<w d → D x y=true → E x y=true) :
    let U := V\{a,d}
    let K := heads q E U w (q-2)
    K⊆outN D V d ∧ (q:ℚ)*mass K w ≤ mass U w := by
  intro U K
  obtain ⟨paths,bill⟩ := arc.cuts E sub
  have inside : K⊆outN D V d := by
    intro h hk
    by_contra miss
    obtain ⟨_,_,_,_,_,x,y,_,_,xu,_,yu,xy,off,cheap,_⟩ := paths h (mem_sdiff.mpr ⟨hk,miss⟩)
    exact Bool.noConfusion (off.symm.trans (keep x xu y yu cheap xy))
  refine ⟨inside,le_of_not_gt (fun heavy=>?_)⟩
  have needed := bill.mp heavy
  change ((q:ℚ)-1)*w a-(c-mass V w)+q*mass (outN D V d \ insert a K) w < q*mass (K\outN D V d) w at needed
  have empty : K\outN D V d = ∅ := eq_empty_iff_forall_notMem.mpr
    (fun _ hm=>(mem_sdiff.mp hm).2 (inside (mem_sdiff.mp hm).1))
  rw [empty] at needed
  have rem := mass_nonneg (fun j (jj : j∈outN D V d \ insert a K)=>nn j (outN_subset (mem_sdiff.mp jj).1))
  rw [show mass ∅ w=0 by simp [mass],mul_zero] at needed
  linarith only [needed,floor,mul_nonneg (Nat.cast_nonneg (α:=ℚ) q) rem]

theorem minimum_tail {q D V w c a d} (arc : ArcMenus q D V w c a d)
    (nn : ∀v∈V,0≤w v) (floor : c-mass V w<((q:ℚ)-1)*w a)
    (minimum : ∀y∈V\{a,d},w d≤w y) (E : CH.Digraph) (sub : ∀i j,E i j=true → D i j=true) :
    let U := V\{a,d}
    (q:ℚ)*mass (heads q E U w (q-2)) w ≤ mass U w :=
  (protected_cuts arc nn floor sub (fun _ _ y yu cheap _=>False.elim ((minimum y yu).not_gt cheap))).2

#print axioms protected_cuts
#print axioms minimum_tail
#print axioms score_above_tail
#print axioms on_arc
#print axioms source_rule
#print axioms marked_arc
end LeanCH.BR.RankedArcMenus
