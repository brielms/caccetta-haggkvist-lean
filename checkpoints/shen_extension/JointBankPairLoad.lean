import checkpoints.shen_extension.JointBankBinaryReturn

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

/-- The actual rows heading both designated labels. -/
abbrev jointParents (D : CH.Digraph) (V : Finset ℕ) (p h : ℕ) := inN D (inN D V p) h

private theorem large_indegree {D V s} (live : V.Nonempty) (reg : OutEq s D V) :
    ∃ p∈V,s ≤ (inN D V p).card := by
  classical
  by_contra! low
  have bound : (∑ p∈V,(inN D V p).card) < ∑ _p∈V,s :=
    sum_lt_sum_of_nonempty live (fun p pv => low p pv)
  have count : (∑ v∈V,(outN D V v).card) = ∑ v∈V,(inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  rw [← count,sum_congr rfl (fun u uv => reg u uv)] at bound
  exact lt_irrefl _ bound

/-- Double-counting all other heads of the predecessors of one label forces
a heavily shared pair in the two-label band. Choose a global maximum. -/
theorem max_pair_at_two {D V q s} (live : V.Nonempty) (reg : OutEq s D V)
    (hq : 2 ≤ q) (hs : 3 ≤ s) (order : V.card=q*(s-1)+2) :
    ∃ p∈V,∃ h∈V,p ≠ h ∧ s ≤ q*(jointParents D V p h).card ∧
      ∀ a∈V,∀ b∈V,a ≠ b → (jointParents D V a b).card ≤ (jointParents D V p h).card := by
  classical
  obtain ⟨a,av,high⟩ := large_indegree live reg
  let P := inN D V a
  let H := V.erase a
  have Hcard : H.card=q*(s-1)+1 := by rw [show H=V.erase a from rfl,card_erase_of_mem av,order]; omega
  have has : H.Nonempty := card_pos.mp (by omega)
  obtain ⟨b,bH,top⟩ := H.exists_max_image (fun h => (jointParents D V a h).card) has
  have count : (∑ h∈H, (jointParents D V a h).card) = ∑ x∈P, (outN D H x).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun h x => D x h=true)
  have row (x) (xp : x∈P) : (outN D H x).card=s-1 := by
    have e : outN D H x=(outN D V x).erase a := by ext z; simp only [H,mem_erase,mem_outN]; tauto
    rw [e,card_erase_of_mem (mem_outN.mpr ⟨av,(mem_inN.mp xp).2⟩),reg x (mem_inN.mp xp).1]
  rw [sum_congr rfl row,sum_const,smul_eq_mul] at count
  let L := (jointParents D V a b).card
  have upper : (∑ h∈H,(jointParents D V a h).card) ≤ ∑ _h∈H,L := sum_le_sum top
  rw [count,sum_const,smul_eq_mul,Hcard] at upper
  have low : s ≤ q*L := by
    by_contra! below
    have q2 := Nat.mul_le_mul_right L hq
    have lts : L < s-1 := by omega
    have eql : s-1+1=s := by omega
    have db := Nat.mul_le_mul_right (s-1) high
    change s*(s-1) ≤ P.card*(s-1) at db
    have tight := Nat.mul_le_mul_right (s-1) (show q*L ≤ s-1 by omega)
    nlinarith only [upper,db,tight,lts,eql]
  have ab : (a,b)∈V.offDiag := mem_offDiag.mpr ⟨av,(mem_erase.mp bH).2,(mem_erase.mp bH).1.symm⟩
  obtain ⟨⟨p,h⟩,ph,best⟩ := V.offDiag.exists_max_image (fun t => (jointParents D V t.1 t.2).card) ⟨_,ab⟩
  have ids := mem_offDiag.mp ph
  have more := best (a,b) ab
  exact ⟨p,ids.1,h,ids.2.1,ids.2.2,low.trans (Nat.mul_le_mul_left q more),
    fun i iv j jv ne => best (i,j) (mem_offDiag.mpr ⟨iv,jv,ne⟩)⟩

/-- In an exact-degree graph, deleting two labels makes precisely their
common predecessors short. Looplessness keeps all those predecessors. -/
theorem short_rows_eq_jointParents {D V q s p h} (free : QFree D V q) (hq : 1 ≤ q)
    (reg : OutEq s D V) (pv : p∈V) (hv : h∈V) (ph : p ≠ h) (hs : 2 ≤ s) :
    let U := V \ {p,h}
    U.filter (fun u => (outN D U u).card<s-1) = jointParents D V p h := by
  intro U
  ext u
  let B : Finset ℕ := {p,h}
  have count (uv : u∈V) : (outN D U u).card + (outN D V u ∩ B).card=s := by
    have eq : outN D U u = outN D V u \ B := by ext z; simp only [U,B,mem_sdiff,mem_outN]; tauto
    rw [eq,card_sdiff_add_card_inter,reg u uv]
  have bc : B.card=2 := card_pair ph
  constructor
  · intro sh
    obtain ⟨um,short⟩ := mem_filter.mp sh
    have uv := (mem_sdiff.mp um).1
    have cnt := count uv
    have incl : outN D V u ∩ B ⊆ B := inter_subset_right
    have eq := eq_of_subset_of_card_le incl (by omega)
    have both : B ⊆ outN D V u := inter_eq_right.mp eq
    exact mem_inN.mpr ⟨mem_inN.mpr ⟨uv,(mem_outN.mp (both (by simp [B]))).2⟩,
      (mem_outN.mp (both (by simp [B] : h∈B))).2⟩
  · intro row
    obtain ⟨up,uh⟩ := mem_inN.mp row
    obtain ⟨uv,up⟩ := mem_inN.mp up
    have unp : u≠p := fun eq => loopfree free hq pv (eq ▸ up)
    have unh : u≠h := fun eq => loopfree free hq hv (eq ▸ uh)
    have both : B ⊆ outN D V u := insert_subset_iff.mpr
      ⟨mem_outN.mpr ⟨pv,up⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,uh⟩)⟩
    have cnt := count uv
    rw [inter_eq_right.mpr both,bc] at cnt
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨uv,by simp [unp,unh]⟩,by omega⟩

private theorem three_or_power {q s} (hq : 3 ≤ q) (hs : 8 ≤ s) (wide : 2^(q-1) < s) :
    2*q<s := by
  by_cases small : q=3
  · omega
  have pow (k : ℕ) : 2*(k+4) ≤ 2^(k+3) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+3 = (k+3)+1 by omega,pow_succ]
      omega
  have eq : q=q-4+4 := by omega
  have z := pow (q-4)
  have ex : q-4+3=q-1 := by omega
  rw [← eq,ex] at z
  omega

/-- A maximum-load marked pair in the two-label bank band. The number of
short rows is at least the regular outdegree divided by the cutoff, rounded up,
and at least three across the capstone's surviving degree range. -/
theorem exists_loaded_joint_mark {q s} (X : ShenMinimumOrder.Source q s) (reg : OutEq s X.D X.V)
    (hq : 3 ≤ q) (hs : 8 ≤ s) (order : X.V.card=q*(s-1)+2) (none : NoHost q (s-1)) :
    ∃ m, Marked X m ∧ JointShort X m ∧ ∃ h∈X.V, m.parent ≠ h ∧ m.bank={m.parent,h} ∧
      let U := X.V \ m.bank
      let S := U.filter (fun u => (outN X.D U u).card<s-1)
      S = jointParents X.D X.V m.parent h ∧ s ≤ q*S.card ∧ 3 ≤ S.card ∧
      ∀ a∈X.V,∀ b∈X.V,a ≠ b → (jointParents X.D X.V a b).card ≤ S.card := by
  classical
  obtain ⟨p,pv,h,hv,ph,paid,best⟩ := max_pair_at_two X.nonempty reg (by omega) (by omega) order
  let P := jointParents X.D X.V p h
  have wide := three_or_power hq hs (exponential_at_two X reg (by omega) (by omega) order none).2
  have many : 3 ≤ P.card := by
    by_contra! few
    have ub := Nat.mul_le_mul_left q (show P.card ≤ 2 by omega)
    change s ≤ q*P.card at paid
    omega
  obtain ⟨x,xp,j,jp,xj⟩ := one_lt_card.mp (by omega : 1<P.card)
  obtain ⟨xpre,xh⟩ := mem_inN.mp xp
  obtain ⟨xv,axp⟩ := mem_inN.mp xpre
  obtain ⟨z,zm,pz,xz⟩ := candidate_exists (B:=∅) X.free (by omega) pv axp
    ((reg x xv).trans (reg p pv).symm).le (by simp)
  let B : Finset ℕ := {p,h}
  let U := X.V \ B
  have sr : U.filter (fun u => (outN X.D U u).card<s-1) = P :=
    short_rows_eq_jointParents X.free (by omega) reg pv hv ph (by omega)
  have jshort := mem_filter.mp (sr.symm ▸ (show j∈P from jp) : j∈U.filter (fun u => (outN X.D U u).card<s-1))
  have xshort := mem_filter.mp (sr.symm ▸ (show x∈P from xp) : x∈U.filter (fun u => (outN X.D U u).card<s-1))
  have subset : B ⊆ X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have bc : B.card=2 := card_pair ph
  have defx : (outN X.D U x).card+1=s-1 := by
    have both : B ⊆ outN X.D X.V x := insert_subset_iff.mpr
      ⟨mem_outN.mpr ⟨pv,axp⟩,singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,xh⟩)⟩
    have eq : outN X.D U x = outN X.D X.V x \ B := by ext w; simp only [U,mem_sdiff,mem_outN]; tauto
    rw [eq]
    have cnt := card_sdiff_add_card_inter (outN X.D X.V x) B
    rw [inter_eq_right.mpr both,bc,reg x xv] at cnt
    omega
  have zv := (mem_sdiff.mp zm).1
  have znp : z≠p := fun e => loopfree X.free (by omega) pv (e ▸ pz)
  have znh : z≠h := fun e => xz (e ▸ xh)
  have room : X.V.card ≤ q*s := by
    have e : s-1+1=s := by omega
    have prod := (Nat.mul_add q (s-1) 1)
    rw [e,Nat.mul_one] at prod
    omega
  let m : Cell := ⟨B,x,p,z⟩
  have marked : Marked X m :=
    ⟨subset,by change B.card=_; omega,xshort.1,by simp [m,B],
      mem_sdiff.mpr ⟨zv,by simp [m,B,znp,znh]⟩,axp,pz,xz,defx,
      chain_through_arc X (by omega) (by omega) reg room xv pv zv axp pz⟩
  refine ⟨m,marked,⟨j,jshort.1,xj.symm,jshort.2⟩,h,hv,ph,rfl,sr,?_,?_,?_⟩
  · change s ≤ q*(U.filter (fun u => (outN X.D U u).card<s-1)).card
    rwa [sr]
  · change 3 ≤ (U.filter (fun u => (outN X.D U u).card<s-1)).card
    rwa [sr]
  · intro a av b bv ne
    change _ ≤ (U.filter (fun u => (outN X.D U u).card<s-1)).card
    rw [sr]; exact best a av b bv ne

#print axioms exists_loaded_joint_mark
end LeanCH.BR.BypassBankReplay

