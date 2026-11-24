import checkpoints.shen_extension.SecondaryCycleCohort
import checkpoints.shen_extension.PhysicalCycleStockClassLedger

namespace LeanCH.BR.MixedBankPayments
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock ShellCycleSupply

/-- A bank is identified by its actual vertices. Its origin records whether it
is a first or second layer, so the two types can share a bank without sharing
their missing-pair charges. -/
noncomputable def origin (D : CH.Digraph) (V : Finset ℕ) (first : ℕ→Bool) (u : ℕ) :
    Finset ℕ × Bool := (if first u then outN D V u else N2 D V u, first u)

theorem common_shell {D V q first u v} (free : QFree D V q) (time : 2≤q)
    (uv : u∈V) (vv : v∈V) (key : origin D V first u=origin D V first v) :
    N2 D V u=N2 D V v := by
  have roles := congrArg Prod.snd key
  have banks := congrArg Prod.fst key
  cases hu : first u <;> cases hv : first v <;> simp [origin,hu,hv] at roles banks
  · exact banks
  · exact (head_exterior free time uv).symm.trans ((congrArg (exterior D V) banks).trans (head_exterior free time vv))

/-- One physical bank is credited once even if both origin types use it.
Within one origin type, ordered pairs of distinct claimants are proved
unreachable on the actual graph and cannot be charged to any other class. -/
theorem balance {D V q r i j base} (free : QFree D V q) (hq : 2≤q) (time : i+j≤q)
    (degree : OutEq r D V) (room : V.card+1≤base) (first : ℕ→Bool)
    (score : ℕ→ℕ) (actual : ∀u∈V,score u=(ball D V u i).card+(ball D V u j).card)
    (S : Finset ℕ) (sv : S⊆V) (ordinary : ∀u∈V\S,base≤score u)
    (F : Finset (Finset ℕ)) (belongs : ∀u∈S,(origin D V first u).1 ∈ F)
    (cycles : ∀C∈F,∀v∈C,Rooted D V v C) (sub : ∀C∈F,C⊆V)
    (strictly_paid :
      let keys := S.image (origin D V first)
      let classOf := fun k=>S.filter (fun u=>origin D V first u=k)
      let debt := fun k=>(∑u∈classOf k,(base-score u))-(classOf k).offDiag.card
      let remaining := fun C=>∑k∈keys.filter (fun k=>k.1=C),(debt k:ℚ)
      let stock := fun C=>∑v∈C,share D V F r (fun v=>(score v-base:ℕ)) C v
      (∀C∈F,remaining C≤stock C) ∧ (∃C∈F,remaining C<stock C)) : False := by
  classical
  let key := origin D V first
  let keys := S.image key
  let group := fun k=>S.filter (fun u=>key u=k)
  let debt := fun k=>(∑u∈group k,(base-score u))-(group k).offDiag.card
  let holes := keys.biUnion (fun k=>(group k).offDiag)
  have separate : (keys : Set (Finset ℕ × Bool)).PairwiseDisjoint (fun k=>(group k).offDiag) := by
    intro a _ b _ ne
    refine disjoint_left.mpr (fun e ea eb=>ne ?_)
    exact ((mem_filter.mp (mem_offDiag.mp ea).1).2).symm.trans ((mem_filter.mp (mem_offDiag.mp eb).1).2)
  have genuine : holes⊆DotClonePairCompletion.orderedIncomparable D V q := by
    intro e em
    obtain ⟨k,_,pair⟩ := mem_biUnion.mp em
    have gv : group k⊆V := (filter_subset _ _).trans sv
    apply PhysicalCycleStock.class_pairs free hq le_rfl degree gv ?_ pair
    intro u um v vm
    exact common_shell free hq (gv um) (gv vm) (((mem_filter.mp um).2).trans (mem_filter.mp vm).2.symm)
  have bill : (∑u∈V,(base-score u)) ≤ holes.card+∑k∈keys,debt k := by
    have zero : (∑u∈V\S,(base-score u))=0 := sum_eq_zero (fun u hu=>Nat.sub_eq_zero_of_le (ordinary u hu))
    have rest := sum_sdiff sv (f:=fun v=>base-score v)
    rw [zero,zero_add] at rest
    rw [←rest, ←sum_fiberwise_of_maps_to (fun u (hu:u∈S)=>mem_image_of_mem key hu) (fun u=>base-score u)]
    rw [show holes.card=∑k∈keys,(group k).offDiag.card from card_biUnion separate,←sum_add_distrib]
    apply sum_le_sum
    intro k _
    change (∑u∈group k,(base-score u))≤(group k).offDiag.card+((∑u∈group k,(base-score u))-(group k).offDiag.card)
    omega
  have byKey (k) (km : k∈keys) : k.1∈F := by obtain ⟨u,um,rfl⟩ := mem_image.mp km; exact belongs _ um
  obtain ⟨pay,C,cf,spare⟩ := strictly_paid
  have backing := sum_lt_sum pay ⟨C,cf,spare⟩
  change (∑C∈F,∑k∈keys.filter (fun k=>k.1=C),(debt k:ℚ)) < _ at backing
  rw [sum_fiberwise_of_maps_to byKey] at backing
  have physical := total_budget (stock:=fun v=>(score v-base:ℕ)) cycles sub degree (fun _ _=>by positivity)
  have gain := backing.trans_le physical
  have billQ : (∑u∈V,((base-score u:ℕ):ℚ))≤(holes.card:ℚ)+∑k∈keys,(debt k:ℚ) := by exact_mod_cast bill
  have gap : (∑u∈V,((base-score u:ℕ):ℚ)) < (holes.card:ℚ)+∑u∈V,((score u-base:ℕ):ℚ) := by linarith
  have gapN : (∑u∈V,(base-score u)) < holes.card+∑u∈V,(score u-base) := by exact_mod_cast gap
  have point (u) (_ : u∈V) : (score u-base)+base=(base-score u)+score u := by omega
  have diff := sum_congr (s₁:=V) rfl point
  simp only [sum_add_distrib,sum_const_nat (fun _ _=>rfl)] at diff
  have rc := ConsecutiveShellBanks.remote_capacity free time
  rw [←sum_congr rfl actual] at rc
  change _ + (∑ u∈V, score u) ≤ V.card*(V.card+1) at rc
  have floor := Nat.mul_le_mul_left V.card room
  have contained := card_le_card genuine
  omega
/-- A scalar test on all possible group sizes, independent of the graph. -/
def groupRoom (d cap : ℕ) : Prop := ∀t∈range (d+1),t*d≤cap+t*(t-1)
instance (d cap : ℕ) : Decidable (groupRoom d cap) := by unfold groupRoom; infer_instance

theorem group_bound {U : Finset ℕ} {loss : ℕ→ℕ} {d cap} (each : ∀u∈U,loss u≤d)
    (room : groupRoom d cap) : (∑u∈U,loss u)-U.offDiag.card≤cap := by
  have bill : (∑u∈U,loss u) ≤ U.card*d := by simpa only [sum_const_nat (fun _ _=>rfl)] using sum_le_sum each
  have eq : U.offDiag.card=U.card*(U.card-1) := by rw [offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]
  rw [eq]
  by_cases small : U.card≤d
  · have := room U.card (mem_range.mpr (by omega)); omega
  · have := Nat.mul_le_mul_left U.card (show d≤U.card-1 by omega); omega

/-- A row with a proved score gain can be used by all its actual cycles;
the denominator reflects the native incidence multiplicity at that row. -/
theorem bank_stock {D V q r c F C} {score : ℕ→ℕ} {base gain} (free : QFree D V q)
    (time : c+2≤q) (deg : OutEq r D V) (rooted : ∀K∈F,∀v∈K,Rooted D V v K)
    (width : ∀K∈F,omissions D V K r≤c) (cf : C∈F)
    (high : ∀v∈C,base+gain≤score v) :
    (C.card:ℚ)*gain/((c+1)*2^c : ℕ) ≤ ∑v∈C,share D V F r (fun v=>(score v-base:ℕ)) C v := by
  have terms (v) (vm : v∈C) :
      (gain:ℚ)/((c+1)*2^c : ℕ) ≤ share D V F r (fun v=>(score v-base:ℕ)) C v := by
    have count := turns_bound (v:=v) free time rooted deg width
    have pos : 0<(turns D F v).card := card_pos.mpr ⟨_,mem_image_of_mem _ (mem_filter.mpr ⟨cf,vm⟩)⟩
    have pow : 2^omissions D V C r≤(2:ℕ)^c := Nat.pow_le_pow_right (by decide) (width C cf)
    have denom : ((turns D F v).card:ℚ)*2^omissions D V C r≤((c+1)*2^c:ℕ) := by
      exact_mod_cast Nat.mul_le_mul count pow
    have large : (gain:ℚ)≤((score v-base:ℕ):ℚ) := by exact_mod_cast (show gain≤score v-base by have := high v vm; omega)
    have denpos : (0:ℚ)<(turns D F v).card*2^omissions D V C r := by positivity
    unfold share
    rw [mul_one_div, div_div]
    exact div_le_div₀ (by positivity) large denpos denom
  have sum := sum_le_sum terms
  rw [sum_const,nsmul_eq_mul,←mul_div_assoc] at sum
  exact sum

/-- Starting with a low root, assign each such root to either its first or
second layer. Each assigned bank pays with its same r labelled cycle rows.
The score, both radii, permitted omission, degree and both per-role budgets
are independent parameters. -/
theorem no_low {D V q r i j base c gain} (free : QFree D V q) (hq : 2≤q) (cut : c+2≤q)
    (time : i+j≤q) (degree : OutEq r D V) (room : V.card+1≤base)
    (score : ℕ→ℕ) (actual : ∀u∈V,score u=(ball D V u i).card+(ball D V u j).card)
    (d cap : Bool→ℕ) (groups : ∀ flag,groupRoom (d flag) (cap flag))
    (profit : (cap false+cap true)*((c+1)*2^c) < r*gain)
    (supplier : ∀u∈V,score u<base → ∃flag : Bool,
      let C := (origin D V (fun _=>flag) u).1
      C⊆V ∧ C.card=r ∧ omissions D V C r≤c ∧ (∀v∈C,Rooted D V v C ∧ base+gain≤score v) ∧ base-score u≤d flag) :
    ∀u∈V,base≤score u := by
  classical
  by_contra! bad
  obtain ⟨w,wv,low⟩ := bad
  let S := V.filter (fun u=>score u<base)
  have sv : S⊆V := filter_subset _ _
  have choose (u) (hm : u∈S) := supplier u (sv hm) (mem_filter.mp hm).2
  let first := fun u=>if h:u∈S then (choose u h).choose else false
  let key := origin D V first
  let keys := S.image key
  let F := keys.image Prod.fst
  let grp := fun k=>S.filter (fun u=>key u=k)
  let loss := fun u=>base-score u
  let debt := fun k=>(∑u∈grp k,loss u)-(grp k).offDiag.card
  have selected u (um : u∈S) :
      (key u).1⊆V ∧ (key u).1.card=r ∧ omissions D V (key u).1 r≤c ∧
        (∀v∈(key u).1,Rooted D V v (key u).1 ∧ base+gain≤score v) ∧ loss u≤d (key u).2 := by
    simpa [key,origin,first,um,loss] using (choose u um).choose_spec
  have banks C (cf : C∈F) : C⊆V ∧ C.card=r ∧ omissions D V C r≤c ∧
      ∀v∈C,Rooted D V v C ∧ base+gain≤score v := by
    obtain ⟨k,km,rfl⟩ := mem_image.mp cf
    obtain ⟨u,um,rfl⟩ := mem_image.mp km
    have h := selected u um
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  have labels C (cf : C∈F) v (vm : v∈C) := ((banks C cf).2.2.2 v vm).1
  have meets u (um : u∈S) : (key u).1∈F := mem_image_of_mem _ (mem_image_of_mem _ um)
  have localDebt (k : Finset ℕ × Bool) : debt k≤cap k.2 := by
    apply group_bound (d:=d k.2) _ (groups _)
    intro u um
    have same := (mem_filter.mp um).2
    change key u=k at same
    exact same ▸ (selected u (mem_filter.mp um).1).2.2.2.2
  have cell C (cf : C∈F) : (∑k∈keys.filter (fun k=>k.1=C),(debt k:ℚ)) <
      ∑v∈C,share D V F r (fun v=>(score v-base:ℕ)) C v := by
    have subkeys : keys.filter (fun k=>k.1=C)⊆{(C,false),(C,true)} := by
      rintro ⟨K,tag⟩ km
      have := (mem_filter.mp km).2
      dsimp at this
      subst K
      cases tag <;> simp
    have bound := (sum_le_sum (s:=keys.filter (fun k=>k.1=C)) (fun k _=>localDebt k)).trans
      (sum_le_sum_of_subset subkeys)
    have small : (∑k∈keys.filter (fun k=>k.1=C),debt k)≤cap false+cap true := by simpa using bound
    have smallQ : (∑k∈keys.filter (fun k=>k.1=C),(debt k:ℚ))≤((cap false+cap true:ℕ):ℚ) := by exact_mod_cast small
    have more : ((cap false+cap true:ℕ):ℚ)<(C.card:ℚ)*gain/((c+1)*2^c:ℕ) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      rw [(banks C cf).2.1]
      exact_mod_cast profit
    exact lt_of_le_of_lt smallQ (lt_of_lt_of_le more
      (bank_stock free cut degree labels (fun K km=>(banks K km).2.2.1) cf (fun v vm=>((banks C cf).2.2.2 v vm).2)))
  have wm : w∈S := mem_filter.mpr ⟨wv,low⟩
  exact balance free hq time degree room first score actual S sv
    (fun u um=>le_of_not_gt (fun sm=>(mem_sdiff.mp um).2 (mem_filter.mpr ⟨(mem_sdiff.mp um).1,sm⟩)))
    F meets labels (fun C cf=>(banks C cf).1) ⟨fun C cf=>(cell C cf).le,_,meets w wm,cell _ (meets w wm)⟩

#print axioms group_bound
#print axioms bank_stock
#print axioms no_low

#print axioms common_shell
#print axioms balance
end LeanCH.BR.MixedBankPayments




