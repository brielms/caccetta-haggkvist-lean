import checkpoints.shen_extension.BypassRepair

namespace LeanCH.BR.ReplacementRowTypes
open Finset BRq2 BRq3 BypassRepair
open scoped Classical

/-- Every possible continuation through v already has a two-arc route
from x through the old block. The old middle may depend on the head. -/
def CanEnter (D : CH.Digraph) (T : Finset ℕ) (C : ℕ → Finset ℕ) (x v : ℕ) : Prop :=
  ∀ h∈C v, ∃ u∈T,D x u=true ∧ D u h=true

noncomputable def edit (D : CH.Digraph) (T : Finset ℕ) (C : ℕ → Finset ℕ) : CH.Digraph :=
  fun x y => if x∈T then decide (y∈C x)
    else if y∈T then decide (CanEnter D T C x y) else D x y

/-- Lift each excursion between two exterior vertices, preserving its
length. Different visits may use different old middle vertices. -/
theorem edit_free {D V T C q} (free : QFree D V q) (tv : T⊆V)
    (ext : ∀ x∈T,Disjoint T (C x)) : QFree (edit D T C) V q := by
  classical
  have lift (k) : ∀ {a b},a∉T → b∉T → Walk (edit D T C) V a b k → Walk D V a b k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b at' bt w
      cases w with
      | refl => exact .refl _
      | @step a m b j mv am tail =>
        by_cases mt : m∈T
        · have enter : CanEnter D T C a m := by simpa [edit,at',mt] using am
          cases tail with
          | refl => exact False.elim (bt mt)
          | @step m y b l yv my rest =>
            have ym : y∈C m := by simpa [edit,mt] using my
            have yt : y∉T := fun h => disjoint_left.mp (ext m mt) h ym
            obtain ⟨u,ut,au,uy⟩ := enter y ym
            exact .step (tv ut) au (.step yv uy (ih l (by omega) yt bt rest))
        · have old : D a m=true := by simpa [edit,at',mt] using am
          exact .step mv old (ih j (by omega) mt bt tail)
  intro a k pos bound w
  by_cases at' : a∈T
  · cases w with
    | refl => omega
    | step mv am tail =>
      have cm := of_decide_eq_true (by simpa [edit,at'] using am)
      have off := fun mt => disjoint_left.mp (ext _ at') mt cm
      exact free _ _ pos bound (lift _ off off (tail.snoc mv am))
  · exact free _ _ pos bound (lift _ at' at' w)

/-- A real common predecessor of the two deletions has no fresh compatible
receiver. This holds for different prescribed outgoing sets on block rows. -/
theorem locked_parent {D V T C q t b z} (free : QFree D V q) (hq : 1≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (bt : b∈T) (zv : z∈V) (zt : z∉T)
    (cores : ∀ v∈T,C v⊆outN D V v) (ext : ∀ v∈T,Disjoint T (C v))
    (avoid : ∀ v∈T,z∉C v) (quota : ∀ v∈T,v≠b → t≤(C v).card) :
    ∃ x∈V, x∉T ∧ D x b=true ∧ D x z=true ∧
      ∀ v∈T, D x v≠true → ¬ CanEnter D T C x v := by
  classical
  by_contra! fail
  let U := (V.erase z).erase b
  have bz : b≠z := fun eq => zt (eq ▸ bt)
  have bev := mem_erase.mpr ⟨bz,tv bt⟩
  have cardU : U.card=q*t := by simp only [U,card_erase_of_mem bev,card_erase_of_mem zv,order]; omega
  have uv : U⊆V := (erase_subset ..).trans (erase_subset ..)
  apply none (edit D T C) U (card_pos.mp (by rw [cardU]; exact Nat.mul_pos (by omega) (by omega))) cardU.le
    ((edit_free free tv ext).mono_set uv)
  intro x xu
  by_cases xt : x∈T
  · apply (quota x xt (mem_erase.mp xu).1).trans (card_le_card ?_)
    intro y ym
    have yv := outN_subset (cores x xt ym)
    have yb : y≠b := fun eq => disjoint_left.mp (ext x xt) bt (eq ▸ ym)
    have yz : y≠z := fun eq => avoid x xt (eq ▸ ym)
    exact mem_outN.mpr ⟨mem_erase.mpr ⟨yb,mem_erase.mpr ⟨yz,yv⟩⟩,by simp [edit,xt,ym]⟩
  let A := outN D V x
  have size : A.card=t+1 := reg x (uv xu)
  let L := (A.erase z).erase b
  have sub : L⊆outN (edit D T C) U x := by
    intro y ym
    obtain ⟨yb,ym⟩ := mem_erase.mp ym
    obtain ⟨yz,ym⟩ := mem_erase.mp ym
    obtain ⟨yv,xy⟩ := mem_outN.mp ym
    refine mem_outN.mpr ⟨mem_erase.mpr ⟨yb,mem_erase.mpr ⟨yz,yv⟩⟩,?_⟩
    by_cases yt : y∈T
    · have enter : CanEnter D T C x y := fun h hc => ⟨y,yt,xy,(mem_outN.mp (cores y yt hc)).2⟩
      simp [edit,xt,yt,enter]
    · simpa [edit,xt,yt] using xy
  have base := card_le_card sub
  by_cases za : z∈A
  · by_cases ba : b∈A
    · obtain ⟨v,vt,fresh,enter⟩ := fail x (uv xu) xt (mem_outN.mp ba).2 (mem_outN.mp za).2
      have vu : v∈U := mem_erase.mpr ⟨fun eq => fresh (eq ▸ (mem_outN.mp ba).2),
        mem_erase.mpr ⟨fun eq => zt (eq ▸ vt),tv vt⟩⟩
      have good : v∈outN (edit D T C) U x := mem_outN.mpr ⟨vu,by simp [edit,xt,vt,enter]⟩
      have gap : v∉L := fun vm => fresh (mem_outN.mp (mem_erase.mp (mem_erase.mp vm).2).2).2
      have bigger := card_le_card (insert_subset good sub)
      have keep : b∈A.erase z := mem_erase.mpr ⟨bz,ba⟩
      rw [card_insert_of_notMem gap] at bigger
      simp only [L,card_erase_of_mem keep,card_erase_of_mem za,size] at bigger
      omega
    · have off : b∉A.erase z := fun h => ba (mem_erase.mp h).2
      simp only [L,erase_eq_of_notMem off,card_erase_of_mem za,size] at base
      omega
  · simp only [L,erase_eq_of_notMem za] at base
    by_cases ba : b∈A
    · rw [card_erase_of_mem ba,size] at base; omega
    · rw [erase_eq_of_notMem ba,size] at base; omega

#print axioms edit_free
#print axioms locked_parent
/-- A row that can enter a dedicated receiver through a single old middle
is enough to propagate forced incidence along any rooted tree of receivers. -/
theorem tree_parent {D V T q t b z} {C : ℕ → Finset ℕ} (free : QFree D V q) (hq : 1≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (bt : b∈T) (zv : z∈V) (zt : z∉T)
    (cores : ∀ v∈T,C v⊆outN D V v) (ext : ∀ v∈T,Disjoint T (C v))
    (avoid : ∀ v∈T,z∉C v) (quota : ∀ v∈T,v≠b → t≤(C v).card)
    (reach : ∀ v∈T, Relation.ReflTransGen
      (fun u v => u∈T ∧ v∈T ∧ C v⊆outN D V u) b v) :
    ∃ x∈V,D x z=true ∧ ∀ v∈T,D x v=true := by
  obtain ⟨x,xv,_,xb,xz,locked⟩ := locked_parent free hq ht reg order none tv bt zv zt cores ext avoid quota
  refine ⟨x,xv,xz,?_⟩
  intro v vt
  induction reach v vt with
  | refl => exact xb
  | tail _ step ih =>
    obtain ⟨um,vm,seen⟩ := step
    by_contra miss
    exact locked _ vm miss (fun h hm => ⟨_,um,ih um,(mem_outN.mp (seen hm)).2⟩)

/-- A rooted tree of overlapping rows of size at least t is impossible
as soon as its block and chosen head sets leave one exterior label.
There is no requirement for one fixed common head set across the tree. -/
theorem no_large_tree {D V T q t b} {C : ℕ → Finset ℕ} (free : QFree D V q) (hq : 3≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t)
    (tv : T⊆V) (bt : b∈T) (large : t≤T.card)
    (cores : ∀ v∈T,C v⊆outN D V v) (ext : ∀ v∈T,Disjoint T (C v))
    (quota : ∀ v∈T,v≠b → t≤(C v).card)
    (reach : ∀ v∈T, Relation.ReflTransGen
      (fun u v => u∈T ∧ v∈T ∧ C v⊆outN D V u) b v)
    (outside : (V \ (T ∪ T.biUnion C)).Nonempty) : False := by
  classical
  let W := T.biUnion C
  let Z := V \ (T ∪ W)
  let H := V.filter (fun x => T⊆outN D V x)
  have inc : H⊆Z := by
    intro x xm
    obtain ⟨xv,all⟩ := mem_filter.mp xm
    apply mem_sdiff.mpr
    refine ⟨xv,fun h => ?_⟩
    rcases mem_union.mp h with xt|xw
    · exact loopfree free (by omega) xv (mem_outN.mp (all xt)).2
    · obtain ⟨v,vt,vx⟩ := mem_biUnion.mp xw
      exact digonfree free (by omega) xv (tv vt) (mem_outN.mp (all vt)).2 (mem_outN.mp (cores v vt vx)).2
  have provider (z) (zm : z∈Z) : ∃ x∈H,D x z=true := by
    obtain ⟨zv,off⟩ := mem_sdiff.mp zm
    obtain ⟨x,xv,xz,all⟩ := tree_parent free (by omega) ht reg order none tv bt zv
      (fun zt => off (mem_union_left _ zt)) cores ext
      (fun v vt hz => off (mem_union_right _ (mem_biUnion.mpr ⟨v,vt,hz⟩))) quota reach
    exact ⟨x,mem_filter.mpr ⟨xv,fun v vt => mem_outN.mpr ⟨tv vt,all v vt⟩⟩,xz⟩
  have zcovered : Z⊆H.biUnion (fun x => outN D Z x) := by
    intro z zm
    obtain ⟨x,xh,xz⟩ := provider z zm
    exact mem_biUnion.mpr ⟨x,xh,mem_outN.mpr ⟨zm,xz⟩⟩
  have small (x) (xh : x∈H) : (outN D Z x).card≤1 := by
    obtain ⟨xv,all⟩ := mem_filter.mp xh
    have sub : outN D Z x ⊆ outN D V x \ T := by
      intro v vm
      obtain ⟨vz,xv'⟩ := mem_outN.mp vm
      obtain ⟨vv,off⟩ := mem_sdiff.mp vz
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨vv,xv'⟩,fun vt => off (mem_union_left _ vt)⟩
    have cnt := card_le_card sub
    rw [card_sdiff_of_subset all,reg x xv] at cnt
    omega
  have eq : H=Z := eq_of_subset_of_card_le inc (calc
    Z.card ≤ _ := card_le_card zcovered
    _ ≤ ∑ x∈H,(outN D Z x).card := card_biUnion_le
    _ ≤ ∑ _x∈H, 1 := sum_le_sum small
    _ = H.card := by simp)
  obtain ⟨z,zm⟩ := outside
  obtain ⟨x,xh,xz⟩ := provider z zm
  have zh : z∈H := eq.symm ▸ zm
  have diff : x≠z := fun e => loopfree free (by omega) (mem_filter.mp zh).1 (e ▸ xz)
  have two : 1<H.card := one_lt_card.mpr ⟨x,xh,z,zh,diff⟩
  let U := V \ H
  have inward (v) (vm : v∈U) (y) (yh : y∈H) : D v y≠true := by
    intro ed
    obtain ⟨vv,vh⟩ := mem_sdiff.mp vm
    have vtz : v∈T ∪ W := by
      by_contra off
      exact vh (eq.symm ▸ (show v∈Z from mem_sdiff.mpr ⟨vv,off⟩))
    obtain ⟨yv,all⟩ := mem_filter.mp yh
    rcases mem_union.mp vtz with vt|vw
    · exact digonfree free (by omega) vv yv ed (mem_outN.mp (all vt)).2
    · obtain ⟨a,at',av⟩ := mem_biUnion.mp vw
      have arc := (mem_outN.mp (cores a at' av)).2
      exact free a 3 (by omega) hq (.step vv arc (.step yv ed (.step (tv at') (mem_outN.mp (all at')).2 (.refl _))))
  have hu : b∈U := mem_sdiff.mpr ⟨tv bt,fun hb => (mem_sdiff.mp (inc hb)).2 (mem_union_left _ bt)⟩
  apply none D U ⟨b,hu⟩ (by
    change (V \ H).card≤q*t
    have hv : H⊆V := filter_subset _ _
    rw [card_sdiff_of_subset hv,order]; omega) (free.mono_set sdiff_subset)
  intro v vm
  have sub : outN D V v⊆outN D U v := by
    intro y ym
    obtain ⟨yv,vy⟩ := mem_outN.mp ym
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨yv,fun yh => inward v vm y yh vy⟩,vy⟩
  have cnt := card_le_card sub
  rw [reg v (mem_sdiff.mp vm).1] at cnt
  omega

#print axioms tree_parent
#print axioms no_large_tree
/-- Count all nearby outside rows at once, including rows that miss different
heads of the reference row. The reference itself belongs to this set. -/
noncomputable def nearby (D : CH.Digraph) (V : Finset ℕ) (t b : ℕ) :=
  (V \ outN D V b).filter (fun u => t≤(outN D V b ∩ outN D V u).card)

theorem nearby_bound {D V q t b} (free : QFree D V q) (hq : 3≤q) (ht : 1≤t)
    (reg : OutEq (t+1) D V) (order : V.card=q*t+2) (none : NoHost q t) (bv : b∈V) :
    (nearby D V t b).card < t := by
  classical
  let P := outN D V b
  let N := nearby D V t b
  have pv : P⊆V := outN_subset
  have ps : P.card=t+1 := reg b bv
  have bn : b∈N := by
    apply mem_filter.mpr
    refine ⟨mem_sdiff.mpr ⟨bv,fun h => loopfree free (by omega) bv (mem_outN.mp h).2⟩,?_⟩
    simp [reg b bv]
  by_contra! big
  change t≤N.card at big
  have count : t-1≤(N.erase b).card := by rw [card_erase_of_mem bn]; omega
  obtain ⟨F,fin,fsize⟩ := exists_subset_card_eq count
  let T := insert b F
  have ts : T.card=t := by
    rw [show T=insert b F from rfl,card_insert_of_notMem (fun bf => (mem_erase.mp (fin bf)).1 rfl),fsize]
    omega
  have tn : T⊆N := insert_subset bn (fin.trans (erase_subset ..))
  have off (u) (ut : u∈T) : u∈V ∧ u∉P := mem_sdiff.mp (mem_filter.mp (tn ut)).1
  have tv : T⊆V := fun u ut => (off u ut).1
  have bt : b∈T := mem_insert_self ..
  let C (u) := P ∩ outN D V u
  have cv (u) (_ : u∈T) : C u ⊆ outN D V u := inter_subset_right
  have cp (u) : C u⊆P := inter_subset_left
  have outer : (V \ (T ∪ T.biUnion C)).Nonempty := by
    have sub : T ∪ T.biUnion C ⊆ V := union_subset tv
      (biUnion_subset.mpr (fun u _ => (cp u).trans pv))
    have sz := (card_union_le T (T.biUnion C)).trans (Nat.add_le_add_left
      (card_le_card (biUnion_subset.mpr (fun u (_ : u∈T) => cp u))) T.card)
    have qt : 3*t≤q*t := Nat.mul_le_mul_right t hq
    apply card_pos.mp
    rw [card_sdiff_of_subset sub]
    omega
  apply no_large_tree free hq ht reg order none tv bt ts.ge cv
    (fun u _ => disjoint_left.mpr (fun y yt yc => (off y yt).2 (cp u yc)))
    (fun u ut _ => (mem_filter.mp (tn ut)).2) ?_ outer
  intro v vt
  exact Relation.ReflTransGen.single ⟨bt,vt,cp v⟩

#print axioms nearby_bound
end LeanCH.BR.ReplacementRowTypes
