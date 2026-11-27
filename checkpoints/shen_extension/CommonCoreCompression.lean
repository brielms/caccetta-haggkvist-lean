import checkpoints.shen_extension.BypassRepair

/-! Compress a set of rows with a common outgoing core at the two-label order. -/
namespace LeanCH.BR.CommonCoreCompression
open Finset BRq2 BRq3 BypassRepair
open scoped Classical

/-- Keep just the common heads on the inside. Any outside row that used
the block may enter at any of its surviving labels. -/
noncomputable def pack (D : CH.Digraph) (T P : Finset ℕ) : CH.Digraph := fun x y =>
  if x∈T then decide (y∈P) else if y∈T then decide ((outN D T x).Nonempty) else D x y

private def same (T : Finset ℕ) (u v : ℕ) := if u∈T then v∈T else v=u

private theorem lift_walk {D V T P} (tv : T⊆V) (apart : Disjoint T P)
    (core : ∀ a∈T, ∀ b∈P, D a b=true) {u v k} (w : Walk (pack D T P) V u v k) :
    ∀ a, same T u a → ∃ b, same T v b ∧ Walk D V a b k := by
  induction w with
  | refl u => intro a ha; exact ⟨a,ha,.refl _⟩
  | @step u v z k vv edge _ ih =>
    intro a au
    have next : ∃ b∈V, same T v b ∧ D a b=true := by
      by_cases ut : u∈T
      · have at' : a∈T := by simpa [same,ut] using au
        have vp : v∈P := by simpa [pack,ut] using edge
        have vt : v∉T := fun vt => disjoint_left.mp apart vt vp
        exact ⟨v,vv,by simp [same,vt],core _ at' _ vp⟩
      · have eq : a=u := by simpa [same,ut] using au
        subst a
        by_cases vt : v∈T
        · have live : (outN D T u).Nonempty := by simpa [pack,ut,vt] using edge
          obtain ⟨b,bt,ub⟩ := live.imp (fun _ => mem_outN.mp)
          exact ⟨b,tv bt,by simpa [same,vt] using bt,ub⟩
        · exact ⟨v,vv,by simp [same,vt],by simpa [pack,ut,vt] using edge⟩
    obtain ⟨b,bv,brel,ab⟩ := next
    obtain ⟨c,crel,tail⟩ := ih b brel
    exact ⟨c,crel,.step bv ab tail⟩

theorem pack_free {D V T P q} (free : QFree D V q) (tv : T⊆V)
    (apart : Disjoint T P) (core : ∀ a∈T, ∀ b∈P, D a b=true) :
    QFree (pack D T P) V q := by
  intro a k hk kq w
  have away {v j} (vt : v∉T) (pos : 1≤j) (jlim : j≤q) (walk : Walk (pack D T P) V v v j) : False := by
    obtain ⟨b,rel,old⟩ := lift_walk tv apart core walk v (by simp [same,vt])
    have eq : b=v := by simpa [same,vt] using rel
    exact free v j pos jlim (eq ▸ old)
  by_cases at' : a∈T
  · cases w with
    | refl => omega
    | step bv ed tail =>
      have bp := of_decide_eq_true (by simpa [pack,at'] using ed)
      exact away (fun bt => disjoint_left.mp apart bt bp) hk kq (tail.snoc bv ed)
  · exact away at' hk kq w

/-- At the native two-label order, every outside vertex can be hit
together with every row of the block by a single original predecessor,
provided the common core survives its deletion. -/
theorem common_parent {D V T P q t z} (free : QFree D V q) (hq : 1≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (pv : P⊆V) (live : T.Nonempty) (size : t≤P.card)
    (core : ∀ a∈T,∀ b∈P,D a b=true) (zv : z∈V) (zt : z∉T) (zp : z∉P) :
    ∃ x∈V, D x z=true ∧ ∀ a∈T,D x a=true := by
  classical
  by_contra! fail
  obtain ⟨b,bt⟩ := live
  have apart : Disjoint T P := disjoint_left.mpr (fun _ xT xP =>
    loopfree free hq (tv xT) (core _ xT _ xP))
  let U := (V.erase z).erase b
  have bz : b≠z := fun e => zt (e ▸ bt)
  have bev := mem_erase.mpr ⟨bz,tv bt⟩
  have un : U.card=q*t := by simp only [U,card_erase_of_mem bev,card_erase_of_mem zv,order]; omega
  have uv : U⊆V := (erase_subset ..).trans (erase_subset ..)
  apply none (pack D T P) U (card_pos.mp (by rw [un]; exact Nat.mul_pos (by omega) (by omega))) un.le
    ((pack_free free tv apart core).mono_set uv)
  intro x xu
  by_cases xt : x∈T
  · apply size.trans (card_le_card ?_)
    intro y yp
    have yb : y≠b := fun e => disjoint_left.mp apart bt (e ▸ yp)
    have yz : y≠z := fun e => zp (e ▸ yp)
    exact mem_outN.mpr ⟨mem_erase.mpr ⟨yb,mem_erase.mpr ⟨yz,pv yp⟩⟩,by simp [pack,xt,yp]⟩
  let A := outN D V x
  have ca : A.card=t+1 := reg x (uv xu)
  by_cases hit : (outN D T x).Nonempty
  · have span : ((A.erase z) \ T) ∪ T.erase b ⊆ outN (pack D T P) U x := by
      intro y ym
      rcases mem_union.mp ym with ym|ym
      · obtain ⟨ya,yt⟩ := mem_sdiff.mp ym
        obtain ⟨yz,ya⟩ := mem_erase.mp ya
        obtain ⟨yv,xy⟩ := mem_outN.mp ya
        exact mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => yt (e ▸ bt),mem_erase.mpr ⟨yz,yv⟩⟩,
          by simpa [pack,xt,yt] using xy⟩
      · obtain ⟨yb,yt⟩ := mem_erase.mp ym
        exact mem_outN.mpr ⟨mem_erase.mpr ⟨yb,mem_erase.mpr ⟨fun e => zt (e ▸ yt),tv yt⟩⟩,
          by simp [pack,xt,yt,hit]⟩
    have dis : Disjoint ((A.erase z) \ T) (T.erase b) :=
      disjoint_left.mpr (fun _ h1 h2 => (mem_sdiff.mp h1).2 (mem_erase.mp h2).2)
    have bound := card_le_card span
    rw [card_union_of_disjoint dis,card_erase_of_mem bt] at bound
    have eq := card_sdiff_add_card_inter (A.erase z) T
    have pos := card_pos.mpr (show T.Nonempty from ⟨b,bt⟩)
    by_cases za : z∈A
    · obtain ⟨a,at',miss⟩ := fail x (uv xu) (mem_outN.mp za).2
      have strict : A.erase z ∩ T ⊂ T := Finset.ssubset_iff_of_subset inter_subset_right |>.mpr
        ⟨a,at',fun hm => miss (mem_outN.mp (mem_erase.mp (mem_inter.mp hm).1).2).2⟩
      have small := card_lt_card strict
      rw [card_erase_of_mem za] at eq
      omega
    · rw [erase_eq_of_notMem za] at eq bound
      have small : (A ∩ T).card≤T.card := card_le_card inter_subset_right
      omega
  · have bzA : b∉A := fun h => hit ⟨b,mem_outN.mpr ⟨bt,(mem_outN.mp h).2⟩⟩
    have sub : A.erase z ⊆ outN (pack D T P) U x := by
      intro y ym
      obtain ⟨yz,ya⟩ := mem_erase.mp ym
      obtain ⟨yv,xy⟩ := mem_outN.mp ya
      have yt : y∉T := fun h => hit ⟨y,mem_outN.mpr ⟨h,xy⟩⟩
      exact mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => bzA (e ▸ ya),mem_erase.mpr ⟨yz,yv⟩⟩,
        by simpa [pack,xt,yt] using xy⟩
    have bound := card_le_card sub
    by_cases za : z∈A
    · rw [card_erase_of_mem za] at bound; omega
    · rw [erase_eq_of_notMem za] at bound; omega

#print axioms pack_free
#print axioms common_parent
/-- Original rows that point to the entire block. -/
noncomputable def parents (D : CH.Digraph) (V T : Finset ℕ) : Finset ℕ :=
  V.filter (fun x => T ⊆ outN D V x)

/-- Every label outside the rectangle is covered by the remaining heads of
its common parents. The right side charges each such row only its actual
capacity after paying for all of T. -/
theorem capacity {D V T P q t} (free : QFree D V q) (hq : 1≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (pv : P⊆V) (live : T.Nonempty) (size : t≤P.card)
    (core : ∀ a∈T,∀ b∈P,D a b=true) :
    (V \ (T ∪ P)).card ≤ (parents D V T).card * (t+1-T.card) := by
  classical
  let Z := V \ (T ∪ P)
  let H := parents D V T
  have cover : Z ⊆ H.biUnion (fun x => outN D Z x) := by
    intro z zm
    obtain ⟨zv,off⟩ := mem_sdiff.mp zm
    obtain ⟨x,xv,xz,all⟩ := common_parent free hq ht reg order none tv pv live size core zv
      (fun h => off (mem_union_left _ h)) (fun h => off (mem_union_right _ h))
    exact mem_biUnion.mpr ⟨x,mem_filter.mpr ⟨xv,fun a at' => mem_outN.mpr ⟨tv at',all a at'⟩⟩,
      mem_outN.mpr ⟨zm,xz⟩⟩
  have per (x) (xh : x∈H) : (outN D Z x).card≤t+1-T.card := by
    obtain ⟨xv,tall⟩ := mem_filter.mp xh
    have inc : outN D Z x ⊆ outN D V x \ T := by
      intro y ym
      obtain ⟨yz,xy⟩ := mem_outN.mp ym
      obtain ⟨yv,off⟩ := mem_sdiff.mp yz
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨yv,xy⟩,fun h => off (mem_union_left _ h)⟩
    simpa [card_sdiff_of_subset tall,reg _ xv] using card_le_card inc
  calc
    Z.card ≤ (H.biUnion (fun x => outN D Z x)).card := card_le_card cover
    _ ≤ ∑ x∈H, (outN D Z x).card := card_biUnion_le
    _ ≤ ∑ _x∈H,(t+1-T.card) := sum_le_sum per
    _ = _ := by simp [H]

/-- A complete directed rectangle with both sides of size t cannot occur
at the two-label order. This uses only the preceding degree induction. -/
theorem no_large_rectangle {D V T P q t} (free : QFree D V q) (hq : 3≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (pv : P⊆V) (large : t≤T.card) (size : t≤P.card)
    (core : ∀ a∈T,∀ b∈P,D a b=true) : False := by
  classical
  obtain ⟨B,sub,sz⟩ := exists_subset_card_eq size
  have bv := sub.trans pv
  have live : T.Nonempty := card_pos.mp (by omega)
  obtain ⟨a,at'⟩ := live
  obtain ⟨p,pb⟩ := card_pos.mp (show 0<B.card by omega)
  let H := parents D V T
  let Z := V \ (T ∪ B)
  have inc : H ⊆ Z := by
    intro y yh
    obtain ⟨yv,all⟩ := mem_filter.mp yh
    have ya : D y a=true := (mem_outN.mp (all at')).2
    apply mem_sdiff.mpr
    refine ⟨yv,fun h => ?_⟩
    rcases mem_union.mp h with yt|yb
    · exact loopfree free (by omega) yv (mem_outN.mp (all yt)).2
    · exact digonfree free (by omega) yv (tv at') ya (core a at' y (sub yb))
  have far : ∃ e∈outN D V p,e∉B := by
    by_contra! all
    have bound := card_le_card (show outN D V p ⊆ B from all)
    rw [reg p (bv pb),sz] at bound
    omega
  obtain ⟨e,em,eb⟩ := far
  obtain ⟨ev,pe⟩ := mem_outN.mp em
  have et : e∉T := fun h => digonfree free (by omega) (bv pb) ev pe (core e h p (sub pb))
  have ez : e∈Z := mem_sdiff.mpr ⟨ev,fun h => (mem_union.mp h).elim et eb⟩
  have eh : e∉H := by
    intro h
    have ea := (mem_outN.mp ((mem_filter.mp h).2 at')).2
    exact free a 3 (by omega) hq (.step (bv pb) (core a at' p (sub pb)) (.step ev pe (.step (tv at') ea (.refl _))))
  have strict := card_lt_card (Finset.ssubset_iff_of_subset inc |>.mpr ⟨e,ez,eh⟩)
  have budget := capacity free (by omega) ht reg order none tv bv ⟨a,at'⟩ sz.ge
    (fun x xt y yb => core x xt y (sub yb))
  change Z.card≤H.card*(t+1-T.card) at budget
  have room : t+1-T.card ≤ 1 := by omega
  have cap := Nat.mul_le_mul_left H.card room
  rw [Nat.mul_one] at cap
  omega

#print axioms capacity
#print axioms no_large_rectangle
end LeanCH.BR.CommonCoreCompression
