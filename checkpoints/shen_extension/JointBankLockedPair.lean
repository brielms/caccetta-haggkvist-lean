import checkpoints.shen_extension.JointBankFreeTargets
import Mathlib.Combinatorics.Configuration

/-! Unique pair coverage by the out-neighbourhoods of an oriented graph
forces the projective-plane order. Apply this to the heads shared with
all free targets to force a bank with two locked rows. -/
namespace LeanCH.BR.JointLockedPair
open Finset BRq2 BRq3 BR45 JointFreeTargets

/-- An oriented incidence relation on a single label set, with a unique
row through each distinct pair of columns, has order k(k-1)+1. -/
theorem unique_pair_order {V : Finset ℕ} (K : ℕ → Finset ℕ)
    (live : V.Nonempty) (sub : ∀ c ∈ V, K c ⊆ V)
    (loop : ∀ c ∈ V, c ∉ K c)
    (digon : ∀ a ∈ V, ∀ b ∈ V, b ∈ K a → a ∉ K b)
    (cover : ∀ p ∈ V, ∀ h ∈ V, p ≠ h → ∃ c ∈ V, p ∈ K c ∧ h ∈ K c)
    (unique : ∀ p ∈ V, ∀ h ∈ V, p ≠ h → ∀ a ∈ V, ∀ b ∈ V,
      p ∈ K a → h ∈ K a → p ∈ K b → h ∈ K b → a = b) :
    ∃ k, V.card = k*(k-1)+1 := by
  classical
  let _ : Membership (↥V) (↥V) := ⟨fun l p => p.val ∈ K l.val⟩
  have through {p h : ↥V} (ne : p ≠ h) : ∃ l : ↥V, p ∈ l ∧ h ∈ l := by
    obtain ⟨c,cv,cp,ch⟩ := cover p p.property h h.property (fun eq => ne (Subtype.ext eq))
    exact ⟨⟨c,cv⟩,cp,ch⟩
  let _ : Configuration.HasLines (↥V) (↥V) := {
    exists_point := fun l => ⟨l,loop l l.property⟩
    exists_line := fun p => ⟨p,loop p p.property⟩
    eq_or_eq := by
      intro p h a b ap ah bp bh
      by_cases same : p = h
      · exact Or.inl same
      · exact Or.inr (Subtype.ext (unique p p.property h h.property
          (fun eq => same (Subtype.ext eq)) a a.property b b.property ap ah bp bh))
    mkLine := fun ne => (through ne).choose
    mkLine_ax := fun ne => (through ne).choose_spec }
  have size (l : ↥V) : Configuration.pointCount (↥V) l = (K l.val).card := by
    let e : {p : ↥V // p ∈ l} ≃ ↥(K l.val) :=
      { toFun := fun p => ⟨p.val.val,p.property⟩
        invFun := fun p => ⟨⟨p.val,sub l l.property p.property⟩,p.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Configuration.pointCount,Nat.card_eq_fintype_card,Fintype.card_coe] using
      Nat.card_congr e
  have miss {p l : ↥V} (off : p ∉ l) : Configuration.lineCount (↥V) p = (K l.val).card :=
    (Configuration.HasLines.lineCount_eq_pointCount rfl off).trans (size l)
  have common (a b : ↥V) : (K a.val).card = (K b.val).card := by
    by_cases ba : b ∈ a
    · exact (miss (p := a) (l := a) (loop a a.property)).symm.trans
        (miss (p := a) (l := b) (digon a a.property b b.property ba))
    · exact (miss (p := b) (l := a) ba).symm.trans (miss (p := b) (l := b) (loop b b.property))
  obtain ⟨root,rootV⟩ := live
  let k := (K root).card
  have uniform (a) (av : a ∈ V) : (K a).card = k := common ⟨a,av⟩ ⟨root,rootV⟩
  have allPairs : V.biUnion (fun c => (K c).offDiag) = V.offDiag := by
    ext ⟨p,h⟩
    constructor
    · intro hit
      obtain ⟨c,cv,edges⟩ := mem_biUnion.mp hit
      obtain ⟨cp,ch,ph⟩ := mem_offDiag.mp edges
      exact mem_offDiag.mpr ⟨sub c cv cp,sub c cv ch,ph⟩
    · intro hit
      obtain ⟨pv,hv,ph⟩ := mem_offDiag.mp hit
      obtain ⟨c,cv,cp,ch⟩ := cover p pv h hv ph
      exact mem_biUnion.mpr ⟨c,cv,mem_offDiag.mpr ⟨cp,ch,ph⟩⟩
  have disj : (V : Set ℕ).PairwiseDisjoint (fun c => (K c).offDiag) := by
    intro a av b bv ab
    apply disjoint_left.mpr
    rintro ⟨p,h⟩ ea eb
    obtain ⟨ap,ah,ph⟩ := mem_offDiag.mp ea
    obtain ⟨bp,bh,_⟩ := mem_offDiag.mp eb
    exact ab (unique p (sub a av ap) h (sub a av ah) ph a av b bv ap ah bp bh)
  have counts : V.card * (V.card-1) = V.card * (k*(k-1)) := by
    calc V.card * (V.card-1) = V.offDiag.card := by simp [offDiag_card,Nat.mul_sub]
         _ = ∑ c ∈ V, (K c).offDiag.card := allPairs ▸ card_biUnion disj
         _ = ∑ _c ∈ V, k*(k-1) := sum_congr rfl (fun c cv => by
           simp [offDiag_card,uniform c cv,Nat.mul_sub])
         _ = _ := by simp
  have pos : 0 < V.card := card_pos.mpr ⟨root,rootV⟩
  have eq := Nat.eq_of_mul_eq_mul_left pos counts
  exact ⟨k,by omega⟩

/-- At the triangle boundary at least one pair is contained in two distinct
shared-head sets, so both rows are locked for the same deletion. -/
theorem exists_two_locked {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*(s-1)+2) (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ p ∈ V, ∃ h ∈ V, p ≠ h ∧
      2 ≤ (lockedRows D V (inN D V p ∩ inN D V h)).card := by
  classical
  let K := sharedHeads D V
  have subEdge {c p} (cp : p ∈ K c) : p ∈ outN D V c := (mem_filter.mp cp).1
  have locked {p h a} (av : a ∈ V) (ap : p ∈ K a) (ah : h ∈ K a) :
      a ∈ lockedRows D V (inN D V p ∩ inN D V h) := by
    have cp := (mem_filter.mp ap).2
    have ch := (mem_filter.mp ah).2
    refine mem_filter.mpr ⟨mem_inter.mpr ⟨mem_inN.mpr ⟨av,(mem_outN.mp (subEdge ap)).2⟩,
      mem_inN.mpr ⟨av,(mem_outN.mp (subEdge ah)).2⟩⟩,?_⟩
    intro v fv
    exact mem_inter.mpr ⟨mem_inN.mpr ⟨fv.1,cp v fv⟩,mem_inN.mpr ⟨fv.1,ch v fv⟩⟩
  by_contra absent
  obtain ⟨k,size⟩ := unique_pair_order K (card_pos.mp (by omega))
    (fun _ _ _ cp => (mem_outN.mp (subEdge cp)).1)
    (fun c cv cc => loopfree free (by decide) cv (mem_outN.mp (subEdge cc)).2)
    (fun a av b bv ab ba => digonfree free (by decide) av bv
      (mem_outN.mp (subEdge ab)).2 (mem_outN.mp (subEdge ba)).2)
    (fun _ pv _ hv ph => pair_covered free reg hs pv hv ph room none)
    (fun p pv h hv ph a av b bv ap ah bp bh => by
      by_contra ab
      exact absent ⟨p,pv,h,hv,ph,one_lt_card.mpr ⟨a,locked av ap ah,b,locked bv bp bh,ab⟩⟩)
  have rem : k*(k-1) % 3 = 1 := by omega
  rw [Nat.mul_mod] at rem
  rcases (show k%3=0 ∨ k%3=1 ∨ k%3=2 by omega) with h | h | h
  · simp [h] at rem
  · have hk : (k-1)%3 = 0 := by omega
    simp [hk] at rem
  · have hk : (k-1)%3 = 1 := by omega
    simp [h,hk] at rem

/-- The two locked rows can be kept on one actual marked deletion. The
fresh marked target is chosen from the successors of the first deleted label. -/
theorem exists_marked_locked_pair {s : ℕ} (X : ShenMinimumOrder.Source 3 s)
    (reg : OutEq s X.D X.V) (hs : 2 ≤ s) (room : X.V.card = 3*(s-1)+2)
    (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ m : BypassBankReplay.Cell, BypassBankReplay.Marked X m ∧ BypassBankReplay.JointShort X m ∧
      ∃ h ∈ X.V, m.parent ≠ h ∧ m.bank = {m.parent,h} ∧
        let L := lockedRows X.D X.V (inN X.D X.V m.parent ∩ inN X.D X.V h)
        m.x ∈ L ∧ ∃ j ∈ L, j ≠ m.x := by
  classical
  obtain ⟨p,pv,h,hv,ph,two⟩ := exists_two_locked X.free reg hs room none
  obtain ⟨x,xL,j,jL,xj⟩ := one_lt_card.mp two
  let B : Finset ℕ := {p,h}
  let U := X.V \ B
  let S := inN X.D X.V p ∩ inN X.D X.V h
  have xS : x ∈ S := (mem_filter.mp xL).1
  have jS : j ∈ S := (mem_filter.mp jL).1
  obtain ⟨xv,xp⟩ := mem_inN.mp (mem_inter.mp xS).1
  have xh := (mem_inN.mp (mem_inter.mp xS).2).2
  obtain ⟨z,zm,pz,xz⟩ := BypassRepair.candidate_exists (B := ∅) X.free (by decide) pv xp
    ((reg x xv).trans (reg p pv).symm).le (by simp)
  have zv := (mem_sdiff.mp zm).1
  have zp : z ≠ p := fun eq => loopfree X.free (by decide) pv (eq ▸ pz)
  have zh : z ≠ h := fun eq => xz (eq ▸ xh)
  have short (a) (as : a ∈ S) : a ∈ U ∧ (outN X.D U a).card < s-1 := by
    have eq := BypassBankReplay.short_rows_eq_jointParents X.free (by decide) reg pv hv ph hs
    obtain ⟨ap,ah⟩ := mem_inter.mp as
    have hit : a ∈ BypassBankReplay.jointParents X.D X.V p h :=
      mem_inN.mpr ⟨ap,(mem_inN.mp ah).2⟩
    rw [← eq] at hit
    exact mem_filter.mp hit
  have bc : B.card = 2 := card_pair ph
  have deficit : (outN X.D U x).card + 1 = s-1 := by
    have both : B ⊆ outN X.D X.V x := insert_subset_iff.mpr
      ⟨mem_outN.mpr ⟨pv,xp⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,xh⟩)⟩
    have eq : outN X.D U x = outN X.D X.V x \ B := by
      ext w; simp only [U,mem_sdiff,mem_outN]; tauto
    have count := card_sdiff_add_card_inter (outN X.D X.V x) B
    rw [inter_eq_right.mpr both,bc,reg x xv] at count
    rw [eq]
    omega
  let m : BypassBankReplay.Cell := ⟨B,x,p,z⟩
  have marked : BypassBankReplay.Marked X m :=
    ⟨insert_subset pv (singleton_subset_iff.mpr hv),by change B.card = _; omega,
      (short x xS).1,by simp [m,B],mem_sdiff.mpr ⟨zv,by simp [m,B,zp,zh]⟩,
      xp,pz,xz,deficit,BypassBankReplay.chain_through_arc X (by decide) (by omega)
        reg (by omega) xv pv zv xp pz⟩
  exact ⟨m,marked,⟨j,(short j jS).1,xj.symm,(short j jS).2⟩,h,hv,ph,rfl,xL,j,jL,xj.symm⟩

#print axioms exists_marked_locked_pair
#print axioms unique_pair_order
#print axioms exists_two_locked

end LeanCH.BR.JointLockedPair

