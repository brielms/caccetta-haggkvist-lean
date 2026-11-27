import checkpoints.shen_extension.FourTargetPayment

namespace LeanCH.BR.FourTargetChoice
open Finset BRq2 BRq3 BR45 JointFreeTargets TripleBank TwoRowShared FourTargetPayment
open FourTargetPayment.Role

/-- Any five eligible targets contain disjoint pairs, with no arc from
the second pair to the first. -/
theorem split_of_five {D : CH.Digraph} {V W : Finset ℕ} (free : QFree D V 3)
    (wv : W⊆V) (big : 5≤W.card) :
    ∃ P⊆W, ∃ L⊆W, P.card=2 ∧ L.card=2 ∧ Disjoint P L ∧ ∀ l∈L, ∀ h∈P, D l h≠true := by
  classical
  obtain ⟨Q,qw,qc⟩ := exists_subset_card_eq big
  have qv := qw.trans wv
  obtain ⟨w,wq,small⟩ : ∃ w∈Q, (outN D Q w).card≤1 := by
    by_contra! fail
    have lim := corB (by decide : 1≤3) (free.mono_set qv)
      (fun i hi => fail i hi) (card_pos.mp (by omega))
    omega
  let N := Q.erase w \ outN D Q w
  have bound := card_le_card_sdiff_add_card (s:=Q.erase w) (t:=outN D Q w)
  rw [card_erase_of_mem wq] at bound
  obtain ⟨T,tn,tc⟩ := exists_subset_card_eq (show 3≤N.card by dsimp [N]; omega)
  have tq : T⊆Q := fun _ h => mem_of_mem_erase (mem_sdiff.mp (tn h)).1
  obtain ⟨f,ft,sink⟩ := exists_sink (free.mono_set (tq.trans qv)) (card_pos.mp (by omega)) tc.le
  have nw {h} (ht : h∈T) : h≠w := (mem_erase.mp (mem_sdiff.mp (tn ht)).1).1
  have wh {h} (ht : h∈T) : D w h≠true := fun ed => (mem_sdiff.mp (tn ht)).2 (mem_outN.mpr ⟨tq ht,ed⟩)
  refine ⟨T.erase f,(erase_subset ..).trans (tq.trans qw),{w,f},
    insert_subset (qw wq) (singleton_subset_iff.mpr (qw (tq ft))),?_,card_pair (nw ft).symm,?_,?_⟩
  · rw [card_erase_of_mem ft,tc]
  · apply disjoint_left.mpr
    intro h hp hl
    rcases mem_insert.mp hl with rfl | hf
    · exact nw (mem_of_mem_erase hp) rfl
    · exact (mem_erase.mp hp).1 (mem_singleton.mp hf)
  · intro l hl h hp
    rcases mem_insert.mp hl with rfl | hl
    · exact wh (mem_of_mem_erase hp)
    · exact mem_singleton.mp hl ▸ sink h (mem_of_mem_erase hp)


/-- Four vertices with no split must contain a directed four-cycle. -/
theorem four_split_or_cycle {D : CH.Digraph} {V W : Finset ℕ} (free : QFree D V 3)
    (wv : W⊆V) (four : W.card=4) :
    (∃ P⊆W, ∃ L⊆W, P.card=2 ∧ L.card=2 ∧ Disjoint P L ∧ ∀ l∈L, ∀ h∈P, D l h≠true) ∨
    ∃ i, Walk D W i i 4 := by
  classical
  by_cases cycle : ∃ i, Walk D W i i 4
  · exact Or.inr cycle
  left
  have safe4 : QFree D W 4 := by
    intro i k pos room path
    by_cases eq : k=4
    · exact cycle ⟨i,eq ▸ path⟩
    · exact (free.mono_set wv) i k pos (by omega) path
  obtain ⟨w,ww,sw⟩ := exists_sink safe4 (card_pos.mp (by omega)) four.le
  let T := W.erase w
  have tc : T.card=3 := by simp [T,card_erase_of_mem ww,four]
  have tw : T⊆W := erase_subset ..
  obtain ⟨f,ft,sf⟩ := exists_sink (free.mono_set (tw.trans wv)) (card_pos.mp (by omega)) tc.le
  have nw {k} (kt : k∈T) : k≠w := (mem_erase.mp kt).1
  have ne : f≠w := nw ft
  refine ⟨T.erase f,(erase_subset ..).trans tw,{w,f},insert_subset ww (singleton_subset_iff.mpr (tw ft)),
    ?_,card_pair ne.symm,?_,?_⟩
  · rw [card_erase_of_mem ft,tc]
  · apply disjoint_left.mpr
    intro h hp hl
    rcases mem_insert.mp hl with rfl | hf
    · exact nw (mem_of_mem_erase hp) rfl
    · exact (mem_erase.mp hp).1 (mem_singleton.mp hf)
  · intro l hl h hp
    rcases mem_insert.mp hl with rfl | lf
    · exact sw h (tw (mem_of_mem_erase hp))
    · exact mem_singleton.mp lf ▸ sf h (mem_of_mem_erase hp)

private def rename (v : Role ↪ ℕ) (g : Role → ℕ)
    (inj : ∀ i∈targets, ∀ k∈targets, g i=g k → i=k)
    (away : ∀ i∈targets, ∀ k∉targets, g i≠v k) : Role ↪ ℕ where
  toFun i := if i∈targets then g i else v i
  inj' := by
    intro i k eq
    by_cases it : i∈targets <;> by_cases kt : k∈targets <;> simp [it,kt] at eq
    · exact inj i it k kt eq
    · exact False.elim (away i it k kt eq)
    · exact False.elim (away k kt i it eq.symm)
    · exact eq

/-- A return through a neutral exterior vertex different from the
designated payer. The same exterior vertex also hits a short row. -/
def alternativeReturn (D : CH.Digraph) (V : Finset ℕ) (p y : ℕ) (v : Role ↪ ℕ) (h : ℕ) : Prop :=
  ∃ e∈V, (∀ i∉targets, e≠v i) ∧ FourLayerReversal.neutral D p y e ∧
    D h e=true ∧ D e (v x)=true ∧ ∃ r∈shortRows, D e (v r)=true

open scoped Classical

/-- A split quartet forces another payer on a specified old reversal. -/
theorem split_forces_another {D : CH.Digraph} {V W : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i∉targets, v i∈V) (pv : p∈V) (yv : y∈V) (py : p≠y)
    (wv : W⊆V) (choice : ∃ P⊆W, ∃ L⊆W, P.card=2 ∧ L.card=2 ∧ Disjoint P L ∧ ∀ l∈L, ∀ h∈P, D l h≠true)
    (hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true)
    (heads : ∀ h∈W, D p h=true ∧ D y h=true)
    (back : ∀ h∈W, ∀ i∈middles, D h (v i)=true)
    (legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true)
    (orderX : D (v j) (v x)≠true)
    (neu : FourLayerReversal.neutral D p y (v payer)) (kept : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y)
    (one : ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s) :
    ∃ v' : Role ↪ ℕ, (∀ i∉targets, v' i=v i) ∧ (∀ h∈targets, v' h∈W) ∧
      (∀ l∈lower, ∀ h∈upper, D (v' l) (v' h)≠true) ∧
      (∃ l∈lower, alternativeReturn D V p y v (v' l)) ∧
      ∃ e∈V, e≠v payer ∧ (∀ i, e≠v' i) ∧ FourLayerReversal.neutral D p y e ∧
      ∃ l, ∃ hl : l∈lower, ∃ r, ∃ hr : r∈shortRows,
        2≤(FourLayerReversal.charges D (reversalLabels v' l r hl hr) e).card := by
  classical
  obtain ⟨P,pw,L,lw,pc,lc,dis,split⟩ := choice
  obtain ⟨h₁,h₂,hh,hp⟩ := card_eq_two.mp pc
  obtain ⟨l₁,l₂,ll,lp⟩ := card_eq_two.mp lc
  let g : Role → ℕ := fun i => match i with
    | .u => h₁ | .z => h₂ | .w => l₁ | .f₄ => l₂ | _ => v i
  have high {i} (hi : i∈upper) : g i∈P := by
    rcases (show ∀ i∈upper, i=u ∨ i=z by decide) i hi with rfl | rfl <;> simp [g,hp]
  have low {i} (hi : i∈lower) : g i∈L := by
    rcases (show ∀ i∈lower, i=w ∨ i=f₄ by decide) i hi with rfl | rfl <;> simp [g,lp]
  have part : ∀ i∈targets, i∈upper ∨ i∈lower := by decide
  have pool {i} (it : i∈targets) : g i∈W := (part i it).elim (fun z => pw (high z)) (fun z => lw (low z))
  have inj (i) (it : i∈targets) (k) (kt : k∈targets) (eq : g i=g k) : i=k := by
    rcases part i it with ih | il <;> rcases part k kt with kh | kl
    · rcases (show ∀ h∈upper, h=u ∨ h=z by decide) i ih with rfl | rfl <;>
        rcases (show ∀ h∈upper, h=u ∨ h=z by decide) k kh with rfl | rfl <;> simp_all [g,Ne.symm]
    · exact False.elim ((disjoint_left.mp dis) (high ih) (eq ▸ low kl))
    · exact False.elim ((disjoint_left.mp dis) (high kh) (eq ▸ low il))
    · rcases (show ∀ h∈lower, h=w ∨ h=f₄ by decide) i il with rfl | rfl <;>
        rcases (show ∀ h∈lower, h=w ∨ h=f₄ by decide) k kl with rfl | rfl <;> simp_all [g,Ne.symm]
  have away (i) (it : i∈targets) (k) (kt : k∉targets) (eq : g i=v k) : False := by
    have wk : v k∈W := eq ▸ pool it
    rcases (show ∀ k∉targets, k∈shortRows ∨ k∈middles ∨ k=payer by decide) k kt with rs | mi | rfl
    · exact digonfree free (by decide) pv (wv wk) (heads _ wk).1 (hit k rs).1
    · exact loopfree free (by decide) (wv wk) (back _ wk k mi)
    · exact neu.2.1 (heads _ wk).1
  let v' := rename v g inj away
  have old {i} (ni : i∉targets) : v' i=v i := ite_eq_right ni
  have new' {i} (it : i∈targets) : v' i=g i := ite_eq_left it
  have htgt {i} (it : i∈targets) : v' i∈W := new' it ▸ pool it
  have rs : ∀ i∈shortRows, i∉targets := by decide
  have md : ∀ i∈middles, i∉targets := by decide
  have split' (l) (hl : l∈lower) (h) (hh : h∈upper) : D (v' l) (v' h)≠true := by
    rw [new' ((show lower⊆targets by decide) hl),new' ((show upper⊆targets by decide) hh)]
    exact split _ (low hl) _ (high hh)
  have same : shortRows.map v'=shortRows.map v := by
    ext n
    constructor <;> intro hn
    · obtain ⟨i,ir,rfl⟩ := mem_map.mp hn
      exact mem_map.mpr ⟨i,ir,(old (rs i ir)).symm⟩
    · obtain ⟨i,ir,rfl⟩ := mem_map.mp hn
      exact mem_map.mpr ⟨i,ir,old (rs i ir)⟩
  have ox : v' x=v x := old (by decide)
  have oj : v' j=v j := old (by decide)
  have op : v' payer=v payer := old (by decide)
  have ob : v' b=v b := old (by decide)
  have oc : v' c=v c := old (by decide)
  obtain ⟨e,ev,off,en,two⟩ := different_payer v' free reg ht order no
    (fun i => by by_cases it : i∈targets
                 · exact wv (htgt it)
                 · rw [old it]; exact live i it)
    pv yv py (fun i ir => by rw [old (rs i ir)]; exact hit i ir)
    (fun h hh => heads _ (htgt hh))
    (fun h hh k km => by rw [old (md k km)]; exact back _ (htgt hh) k km)
    (fun i im k kr => by rw [old (md i im),old (rs k kr)]; exact legs i im k kr)
    (by rwa [oj,ox]) split' (by rwa [op]) (by rwa [op]) (by rwa [op,ob,oc])
    (fun r rh off => others r rh (same ▸ off))
  have coreOff (i) (ni : i∉targets) : e≠v i := old ni ▸ off i
  have atMost : ∀ r∈shortRows, ∀ s∈shortRows, D e (v' r)=true → D e (v' s)=true → r=s := by
    intro r hr s hs er es
    apply one e ev coreOff en r hr s hs
    · rwa [old (rs r hr)] at er
    · rwa [old (rs s hs)] at es
  obtain ⟨r,hr,rc,xc⟩ := cross_charge v' two atMost
  obtain ⟨_,ex,l,hl,le⟩ := mem_filter.mp xc
  have er := (mem_filter.mp rc).2.1
  rw [ox] at ex
  rw [old (rs r hr)] at er
  exact ⟨v',fun _ ni => old ni,fun _ it => htgt it,split',
    ⟨l,by simpa only [gains,lower] using hl,e,ev,coreOff,en,le,ex,r,hr,er⟩,
    e,ev,op ▸ off payer,off,en,paid_twice_in_reversal v' two atMost⟩

/-- For an arbitrary pool of five or more targets, a nominated payer
cannot account for every reversal on the pool. The output carries the
original row labels, the chosen quartet, and a genuinely different payer. -/
theorem five_force_another {D : CH.Digraph} {V W : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i∉targets, v i∈V) (pv : p∈V) (yv : y∈V) (py : p≠y)
    (wv : W⊆V) (big : 5≤W.card)
    (hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true)
    (heads : ∀ h∈W, D p h=true ∧ D y h=true)
    (back : ∀ h∈W, ∀ i∈middles, D h (v i)=true)
    (legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true)
    (orderX : D (v j) (v x)≠true)
    (neu : FourLayerReversal.neutral D p y (v payer)) (kept : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y)
    (one : ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s) :
    ∃ v' : Role ↪ ℕ, (∀ i∉targets, v' i=v i) ∧ (∀ h∈targets, v' h∈W) ∧
      (∀ l∈lower, ∀ h∈upper, D (v' l) (v' h)≠true) ∧
      (∃ l∈lower, alternativeReturn D V p y v (v' l)) ∧
      ∃ e∈V, e≠v payer ∧ (∀ i, e≠v' i) ∧ FourLayerReversal.neutral D p y e ∧
      ∃ l, ∃ hl : l∈lower, ∃ r, ∃ hr : r∈shortRows,
        2≤(FourLayerReversal.charges D (reversalLabels v' l r hl hr) e).card :=
  split_forces_another v free reg ht order no live pv yv py wv (split_of_five free wv big)
    hit heads back legs orderX neu kept payerRows others one

/-- All but at most four targets have a two-step return into x through
an exterior vertex other than the specified payer. -/
theorem at_most_four_without_another {D : CH.Digraph} {V W : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i∉targets, v i∈V) (pv : p∈V) (yv : y∈V) (py : p≠y)
    (wv : W⊆V)
    (hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true)
    (heads : ∀ h∈W, D p h=true ∧ D y h=true)
    (back : ∀ h∈W, ∀ i∈middles, D h (v i)=true)
    (legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true)
    (orderX : D (v j) (v x)≠true)
    (neu : FourLayerReversal.neutral D p y (v payer)) (kept : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y)
    (one : ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s) :
    (W.filter (fun h => ¬alternativeReturn D V p y v h)).card≤4 := by
  classical
  let B := W.filter (fun h => ¬alternativeReturn D V p y v h)
  change B.card≤4
  by_contra! many
  have bw : B⊆W := filter_subset _ _
  obtain ⟨v',_,selected,_,⟨l,hl,ret⟩,_⟩ := five_force_another v free reg ht order no live pv yv py
    (bw.trans wv) (show 5≤B.card by omega) hit (fun h hb => heads h (bw hb))
    (fun h hb => back h (bw hb)) legs orderX neu kept payerRows others one
  have lb := selected l ((show lower⊆targets by decide) hl)
  exact (mem_filter.mp lb).2 ret

/-- If four targets have no return via another payer, those four labels
carry a length-four closed walk, necessarily a directed four-cycle. -/
theorem four_without_another_cycle {D : CH.Digraph} {V W : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card=3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i∉targets, v i∈V) (pv : p∈V) (yv : y∈V) (py : p≠y)
    (wv : W⊆V)
    (hit : ∀ i∈shortRows, D (v i) p=true ∧ D (v i) y=true)
    (heads : ∀ h∈W, D p h=true ∧ D y h=true)
    (back : ∀ h∈W, ∀ i∈middles, D h (v i)=true)
    (legs : ∀ i∈middles, ∀ k∈shortRows, D (v i) (v k)=true)
    (orderX : D (v j) (v x)≠true)
    (neu : FourLayerReversal.neutral D p y (v payer)) (kept : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r∈inN D V p ∩ inN D V y, r∉shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l∉inN D V p ∩ inN D V y)
    (one : ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s)
    {B : Finset ℕ} (bw : B⊆W) (four : B.card=4)
    (alone : ∀ h∈B, ¬alternativeReturn D V p y v h) :
    ∃ i, Walk D B i i 4 := by
  rcases four_split_or_cycle free (bw.trans wv) four with split | cycle
  · obtain ⟨v',_,selected,_,⟨l,hl,ret⟩,_⟩ := split_forces_another v free reg ht order no live pv yv py
      (bw.trans wv) split hit (fun h hb => heads h (bw hb))
      (fun h hb => back h (bw hb)) legs orderX neu kept payerRows others one
    exact False.elim (alone _ (selected _ ((show lower⊆targets by decide) hl)) ret)
  · exact cycle

/-- The no-swap condition and the original two common parents supply
the one-row premise for every eligible exterior vertex. -/
theorem one_row_of_no_swap {D : CH.Digraph} {V : Finset ℕ} {p y : ℕ} (v : Role ↪ ℕ)
    (exactS : inN D V (v a) ∩ inN D V (v b)={v x,v j})
    (noSwap : ¬∃ e∈V, (∀ i∉targets, e≠v i) ∧ FourLayerReversal.neutral D p y e ∧
      D e (v c)=true ∧ (D e (v a)=true ∨ D e (v b)=true)) :
    ∀ e∈V, (∀ i∉targets, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s := by
  intro e ev off en
  have ab : ¬(D e (v a)=true ∧ D e (v b)=true) := by
    rintro ⟨ea,eb⟩
    have ep : e ∈ inN D V (v a) ∩ inN D V (v b) :=
      mem_inter.mpr ⟨mem_inN.mpr ⟨ev,ea⟩,mem_inN.mpr ⟨ev,eb⟩⟩
    rw [exactS] at ep
    simp [off x (by decide : x∉targets),off j (by decide : j∉targets)] at ep
  have ca : ¬(D e (v c)=true ∧ (D e (v a)=true ∨ D e (v b)=true)) :=
    fun ⟨ec,er⟩ => noSwap ⟨e,ev,off,en,ec,er⟩
  intro r hr s hs er es
  have part : ∀ r∈shortRows, r=a ∨ r=b ∨ r=c := by decide
  rcases part _ hr with rfl | rfl | rfl <;> rcases part _ hs with rfl | rfl | rfl <;> tauto

/-- A payer common to the original triple's reversal assignments forces a
new return from the fourth target that the original sink does not have. -/
theorem fourth_distinguishes {D : CH.Digraph} {V : Finset ℕ} {t p y : ℕ} (v : Role ↪ ℕ)
    (free : QFree D V 3) (reg : OutEq (t+1) D V) (ht : 1 ≤ t)
    (order : V.card = 3*t+2) (no : BypassRepair.NoHost 3 t)
    (live : ∀ i, v i ∈ V) (pv : p ∈ V) (yv : y ∈ V) (py : p ≠ y)
    (hit : ∀ i ∈ shortRows, D (v i) p = true ∧ D (v i) y = true)
    (heads : ∀ k ∈ targets, D p (v k) = true ∧ D y (v k) = true)
    (back : ∀ k ∈ targets, ∀ i ∈ middles, D (v k) (v i) = true)
    (legs : ∀ i ∈ middles, ∀ k ∈ shortRows, D (v i) (v k) = true)
    (orderX : D (v j) (v x) ≠ true) (split : ∀ i∈lower, ∀ k∈upper, D (v i) (v k) ≠ true)
    (payerNeutral : FourLayerReversal.neutral D p y (v payer))
    (retained : v payer≠p ∧ v payer≠y)
    (payerRows : D (v payer) (v b)≠true ∧ D (v payer) (v c)≠true)
    (others : ∀ r ∈ inN D V p ∩ inN D V y, r ∉ shortRows.map v →
      ∃ l, FreeTarget D V r l ∧ l ∉ inN D V p ∩ inN D V y)
    (one : ∀ e∈V, (∀ i, e≠v i) → FourLayerReversal.neutral D p y e →
      ∀ r∈shortRows, ∀ s∈shortRows, D e (v r)=true → D e (v s)=true → r=s)
    (oldOnly : ∀ r, ∀ hr : r∈shortRows, ∀ e∈V, (∀ i, e≠v i) →
      FourLayerReversal.neutral D p y e →
      2≤(FourLayerReversal.charges D (reversalLabels v w r (by decide) hr) e).card → e=v payer) :
    ∃ e∈V, (∀ i, e≠v i) ∧ FourLayerReversal.neutral D p y e ∧
      D (v f₄) e=true ∧ D (v w) e≠true ∧ D e (v x)=true ∧
      ∃ r, ∃ hr : r∈shortRows, D e (v r)=true ∧ (∃ h∈gains r, D (v h) e=true) ∧
        2≤(FourLayerReversal.charges D (reversalLabels v f₄ r (by decide) hr) e).card := by
  obtain ⟨e,ev,off,en,two⟩ := different_payer v free reg ht order no live pv yv py hit heads
    back legs orderX split payerNeutral retained payerRows others
  obtain ⟨r,hr,rc,xc⟩ := cross_charge v two (one e ev off en)
  obtain ⟨_,er,h,hg,he⟩ := mem_filter.mp rc
  obtain ⟨_,ex,l,hl,le⟩ := mem_filter.mp xc
  have charge (k) (hk : k∈lower) (ke : D (v k) e=true) :
      2≤(FourLayerReversal.charges D (reversalLabels v k r hk hr) e).card := by
    have hEq := (show ∀ r∈shortRows, ∀ h∈gains r, ∀ k, h=layout k r .u by decide) r hr h hg k
    refine one_lt_card.mpr ⟨.a,?_,.x,?_,by decide⟩
    · exact mem_filter.mpr ⟨mem_univ _,er,.u,by decide,by change D (v (layout k r .u)) e=true; rwa [←hEq]⟩
    · exact mem_filter.mpr ⟨mem_univ _,ex,.w,by decide,ke⟩
  have missed : D (v w) e≠true := fun we =>
    off payer (oldOnly r hr e ev off en (charge w (by decide) we))
  have fe : D (v f₄) e=true := by
    rcases (show ∀ l∈gains x, l=w ∨ l=f₄ by decide) l hl with rfl | rfl
    · exact False.elim (missed le)
    · exact le
  exact ⟨e,ev,off,en,fe,missed,ex,r,hr,er,⟨h,hg,he⟩,charge f₄ (by decide) fe⟩

#print axioms fourth_distinguishes
#print axioms four_without_another_cycle
#print axioms split_forces_another
#print axioms four_split_or_cycle
#print axioms one_row_of_no_swap
#print axioms at_most_four_without_another
#print axioms split_of_five
#print axioms five_force_another
end LeanCH.BR.FourTargetChoice
