import checkpoints.shen_extension.TwoPathReturnBudget
import checkpoints.shen_extension.JointBankFreeTargets

namespace LeanCH.BR.WalkReturn
open Finset BRq2 BRq3 BR45
open scoped BigOperators

private abbrev one (a : Bool) : ℕ := if a then 1 else 0

/-- Contribution determined by how many of the four corners send to a label. -/
def occupancyCharge (a b c d : Bool) : ℕ :=
  match one a + one b + one c + one d with
  | 0 => 4
  | 3 => 2
  | 4 => 4
  | _ => 0

/-- A label reached by the first corner and missed by the two opposite
return-forbidding corners could supply a return. Count it here if it does not. -/
private abbrev unused (a c d intoC : Bool) := one (a && !c && !d && !intoC)

private abbrev twist (a b c intoB : Bool) := one (a && c && !b && !intoB)

private def labelCharge (a b c d j k l m : Bool) : ℕ :=
  occupancyCharge a b c d + unused a c d l + unused b d a m +
    unused c a b j + unused d b c k

set_option maxHeartbeats 2000000 in
private theorem four_table : ∀ a b c d j k l m : Bool,
    (j=true → a=false ∧ b=false) → (k=true → b=false ∧ c=false) →
    (l=true → c=false ∧ d=false) → (m=true → d=false ∧ a=false) →
    3*(one a+one b+one c+one d) +
      (one (a && l)+one (b && m)+one (c && j)+one (d && k)) + labelCharge a b c d j k l m =
    4 + 3*(one (a && b)+one (b && c)+one (c && d)+one (d && a)) +
      (twist a b c k+twist b c d l+twist c d a m+twist d a b j) := by
  intro a b c d j k l m
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases j <;> cases k <;> cases l <;> cases m <;>
    simp +decide

def cycleCharge (D : CH.Digraph) (V : Finset ℕ) (a b c d : ℕ) :=
  ∑ z∈V, labelCharge (D a z) (D b z) (D c z) (D d z) (D z a) (D z b) (D z c) (D z d)

private theorem guard {D : CH.Digraph} {V : Finset ℕ} {u v z : ℕ} (safe : QFree D V 3)
    (uu : u∈V) (vu : v∈V) (zu : z∈V) (uv : D u v=true) (zu' : D z u=true) :
    D u z=false ∧ D v z=false :=
  ⟨Bool.eq_false_iff.mpr (digonfree safe (by decide) zu uu zu'),
   Bool.eq_false_iff.mpr (fun vz => safe z 3 (by decide) (by decide)
    (.step uu zu' (.step vu uv (.step zu vz (.refl _)))))⟩

private theorem sum_bits (D : CH.Digraph) (V : Finset ℕ) (a : ℕ) :
    (∑ z∈V, one (D a z))=(outN D V a).card := by
  simp only [one,Finset.sum_boole,Nat.cast_id]
  congr 1

/-- An exact version of the closed-walk inequality on four corners.
Each label's charge is its occupancy charge plus its unrealised eligible returns. -/
theorem four_cycle_exact {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (safe : QFree D V 3) (av : a∈V) (bv : b∈V) (cv : c∈V) (dv : d∈V)
    (ab : D a b=true) (bc : D b c=true) (cd : D c d=true) (da : D d a=true) :
    3*((outN D V a).card+(outN D V b).card+(outN D V c).card+(outN D V d).card) +
      (middles D V a c+middles D V b d+middles D V c a+middles D V d b) + cycleCharge D V a b c d =
    4*V.card + 3*(overlap D V a b+overlap D V b c+overlap D V c d+overlap D V d a) +
      (witnesses D V a b c+witnesses D V b c d+witnesses D V c d a+witnesses D V d a b) := by
  classical
  have point (z) (zv : z∈V) := four_table _ _ _ _ _ _ _ _
    (guard safe av bv zv ab) (guard safe bv cv zv bc)
    (guard safe cv dv zv cd) (guard safe dv av zv da)
  have h := sum_congr rfl point
  unfold cycleCharge middles overlap witnesses
  simp only [sum_add_distrib,←mul_sum,sum_const,smul_eq_mul,sum_bits] at h
  rw [Nat.mul_comm 4 V.card]
  exact h

/-- Common predecessors of either diagonal force a charge of four per
distinct label, even if the two diagonal pairs have the same predecessor. -/
theorem common_predecessor_charge {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (safe : QFree D V 3) (av : a∈V) (bv : b∈V) (cv : c∈V) (dv : d∈V)
    (ab : D a b=true) (bc : D b c=true) (cd : D c d=true) (da : D d a=true) :
    4*((inN D V a ∩ inN D V c) ∪ (inN D V b ∩ inN D V d)).card≤cycleCharge D V a b c d := by
  classical
  let P := (inN D V a ∩ inN D V c) ∪ (inN D V b ∩ inN D V d)
  have sub : P⊆V := by
    intro z zp
    obtain ac | bd := mem_union.mp zp
    · exact (mem_inN.mp (mem_inter.mp ac).1).1
    · exact (mem_inN.mp (mem_inter.mp bd).1).1
  have charge (z) (zp : z∈P) :
      labelCharge (D a z) (D b z) (D c z) (D d z) (D z a) (D z b) (D z c) (D z d)=4 := by
    obtain ac | bd := mem_union.mp zp
    · obtain ⟨za,zc⟩ := mem_inter.mp ac
      obtain ⟨a',b'⟩ := guard safe av bv (sub zp) ab (mem_inN.mp za).2
      obtain ⟨c',d'⟩ := guard safe cv dv (sub zp) cd (mem_inN.mp zc).2
      simp [a',b',c',d',labelCharge,occupancyCharge,unused,one]
    · obtain ⟨zb,zd⟩ := mem_inter.mp bd
      obtain ⟨b',c'⟩ := guard safe bv cv (sub zp) bc (mem_inN.mp zb).2
      obtain ⟨d',a'⟩ := guard safe dv av (sub zp) da (mem_inN.mp zd).2
      simp [a',b',c',d',labelCharge,occupancyCharge,unused,one]
  unfold cycleCharge
  calc
    4*P.card = ∑ _z∈P, 4 := by simp [Nat.mul_comm]
    _ = _ := sum_congr rfl (fun z zp => (charge z zp).symm)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (by intros; omega)

/-- Pair coverage produces three distinct vertices missed by the four
corner rows. In the coincident case the diagonal witness points to
all four corners, and its predecessors are missed as well. -/
theorem three_missed_corners {D : CH.Digraph} {V : Finset ℕ} {a b c d : ℕ}
    (safe : QFree D V 3) (av : a∈V) (bv : b∈V) (cv : c∈V) (dv : d∈V)
    (ab : D a b=true) (bc : D b c=true) (cd : D c d=true) (da : D d a=true)
    (pair : ∀ u∈V, ∀ v∈V, u≠v → ∃ r∈V, D r u=true ∧ D r v=true) :
    3≤(V.filter (fun z => D a z=false ∧ D b z=false ∧ D c z=false ∧ D d z=false)).card := by
  classical
  let Z := V.filter (fun z => D a z=false ∧ D b z=false ∧ D c z=false ∧ D d z=false)
  have neq {u v} (uv : u∈V) (arc : D u v=true) : u≠v :=
    fun e => loopfree safe (by decide) uv (e ▸ arc)
  have block {u v h} (uu : u∈V) (vu : v∈V) (hu : h∈V) (uv : D u v=true) (vh : D v h=true) :
      D h u=false := (guard safe vu hu uu vh uv).2
  have three {r f g} (rz : r∈Z) (fz : f∈Z) (gz : g∈Z) (rf : r≠f) (gr : g≠r) (gf : g≠f) : 3≤Z.card := by
    have inc : ({g,r,f} : Finset ℕ)⊆Z := insert_subset gz (insert_subset rz (singleton_subset_iff.mpr fz))
    have count := card_le_card inc
    simpa [gr,gf,rf] using count
  obtain ⟨r,rv,ra,rc⟩ := pair a av c cv (fun e => digonfree safe (by decide) av bv ab (e ▸ bc))
  obtain ⟨f,fv,fb,fd⟩ := pair b bv d dv (fun e => digonfree safe (by decide) bv cv bc (e ▸ cd))
  obtain ⟨ar,br⟩ := guard safe av bv rv ab ra
  obtain ⟨cr,dr⟩ := guard safe cv dv rv cd rc
  have rz : r∈Z := mem_filter.mpr ⟨rv,ar,br,cr,dr⟩
  by_cases rf : r=f
  · subst f
    have behind {h} (hv : h∈V) (hr : D h r=true) : h∈Z :=
      mem_filter.mpr ⟨hv,block hv rv av hr ra,block hv rv bv hr fb,block hv rv cv hr rc,block hv rv dv hr fd⟩
    obtain ⟨u,uv,ur,_⟩ := pair r rv a av (neq rv ra)
    obtain ⟨g,gv,gr,gu⟩ := pair r rv u uv (neq uv ur).symm
    exact three rz (behind uv ur) (behind gv gr) (neq uv ur).symm (neq gv gr) (neq gv gu)
  · obtain ⟨bf,cf⟩ := guard safe bv cv fv bc fb
    obtain ⟨df,af⟩ := guard safe dv av fv da fd
    have fz : f∈Z := mem_filter.mpr ⟨fv,af,bf,cf,df⟩
    obtain ⟨g,gv,gr,gf⟩ := pair r rv f fv rf
    have gz : g∈Z := mem_filter.mpr
      ⟨gv,block gv rv av gr ra,block gv fv bv gf fb,block gv rv cv gr rc,block gv fv dv gf fd⟩
    exact three rz fz gz rf (neq gv gr) (neq gv gf)

/-- For two-label source order the constant sixteen consists of four
from the order and twelve from three labels missed by all four rows. -/
theorem pair_square_budget {D : CH.Digraph} {V : Finset ℕ} {s a b c d : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (order : V.card+1=3*s)
    (av : a∈V) (bv : b∈V) (cv : c∈V) (dv : d∈V)
    (ab : D a b=true) (bc : D b c=true) (cd : D c d=true) (da : D d a=true)
    (pair : ∀ u∈V, ∀ v∈V, u≠v → ∃ r∈V, D r u=true ∧ D r v=true) :
    16+(middles D V a c+middles D V b d+middles D V c a+middles D V d b) ≤
      3*(overlap D V a b+overlap D V b c+overlap D V c d+overlap D V d a) +
      (witnesses D V a b c+witnesses D V b c d+witnesses D V c d a+witnesses D V d a b) := by
  classical
  let Z := V.filter (fun z => D a z=false ∧ D b z=false ∧ D c z=false ∧ D d z=false)
  have size : 3≤Z.card := three_missed_corners safe av bv cv dv ab bc cd da pair
  have lower : 4*Z.card≤cycleCharge D V a b c d := by
    unfold cycleCharge
    calc
      4*Z.card = ∑ _z∈Z, 4 := by simp [Nat.mul_comm]
      _ = _ := sum_congr rfl (fun z hz => by
        obtain ⟨_,az,bz,cz,dz⟩ := mem_filter.mp hz
        simp [az,bz,cz,dz,labelCharge,occupancyCharge,unused,one])
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
  have ident := four_cycle_exact safe av bv cv dv ab bc cd da
  rw [reg a av,reg b bv,reg c cv,reg d dv] at ident
  omega

theorem middles_eq_card (D : CH.Digraph) (V : Finset ℕ) (a c : ℕ) :
    middles D V a c=(outN D V a ∩ inN D V c).card := by
  change (∑ z∈V, one (D a z && D z c))=_
  simp only [one,Finset.sum_boole,Nat.cast_id]
  congr 1
  ext z
  simp only [mem_inter,mem_filter,mem_outN,mem_inN,Bool.and_eq_true]
  tauto

/-- The pair-order source supplies pair coverage by the bank induction.
Both directions across the chosen diagonal have been retained. -/
theorem two_label_diagonal_budget {D : CH.Digraph} {V : Finset ℕ} {s a b c d : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 2≤s)
    (order : V.card=3*(s-1)+2) (no : BypassRepair.NoHost 3 (s-1))
    (av : a∈V) (bv : b∈V) (cv : c∈V) (dv : d∈V)
    (ab : D a b=true) (bc : D b c=true) (cd : D c d=true) (da : D d a=true) :
    18+middles D V a c+middles D V c a ≤
      3*(overlap D V a b+overlap D V b c+overlap D V c d+overlap D V d a) +
      (witnesses D V a b c+witnesses D V b c d+witnesses D V c d a+witnesses D V d a b) := by
  classical
  have cover (u) (uv : u∈V) (v) (vv : v∈V) (neq : u≠v) :
      ∃ r∈V, D r u=true ∧ D r v=true := by
    obtain ⟨r,rv,ru,rv'⟩ := JointFreeTargets.pair_covered safe reg hs uv vv neq order no
    exact ⟨r,rv,(mem_outN.mp (mem_filter.mp ru).1).2,(mem_outN.mp (mem_filter.mp rv').1).2⟩
  have mid {u v h} (hv : h∈V) (uh : D u h=true) (hw : D h v=true) : 1≤middles D V u v := by
    rw [middles_eq_card]
    exact card_pos.mpr ⟨h,mem_inter.mpr ⟨mem_outN.mpr ⟨hv,uh⟩,mem_inN.mpr ⟨hv,hw⟩⟩⟩
  have sum := pair_square_budget safe reg (by omega) av bv cv dv ab bc cd da cover
  have left := mid cv bc cd
  have right := mid av da ab
  omega

#print axioms two_label_diagonal_budget
#print axioms three_missed_corners
#print axioms pair_square_budget
#print axioms four_cycle_exact
#print axioms common_predecessor_charge
end LeanCH.BR.WalkReturn
