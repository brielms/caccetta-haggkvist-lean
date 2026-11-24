import checkpoints.shen_extension.TallBankTransferBudget
import checkpoints.shen_extension.TallBankTransferFibre
import checkpoints.shen_extension.dot_tensor_research.SingleOmissionPacking

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3 BR45

/-- If every floor row has a unique strong sink, the physical paths, the
fibre budget and the final return give a contradiction on this graph. -/
theorem no_unique_strong_sinks {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (degree : 6 ≤ r) (diag : r ≤ q)
    (distance : 4 + 4 ≤ q)
    (positive : 4 * r ≤ B) (order : V.card = B + B)
    (floor : ∀ u ∈ V, B ≤ (ball D V u 4).card)
    (profile : ∀ u ∈ V, (ball D V u 4).card = B →
      (ball D V u 2).card = 2 * r + 2 ∧ (ball D V u 3).card = 3 * r + 1)
    (supplier : ∀ u ∈ V, (ball D V u 4).card = B →
      ∃ a ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) a ∧
        (∀ z ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) z → z = a) ∧
        2 * r + 2 ≤ (ball D V a 2).card) : False := by
  classical
  have shell {v : ℕ} (hv : v ∈ V) (two : (ball D V v 2).card = 2 * r + 2) :
      (ball D V v 2 \ ball D V v 1).card = r + 1 := by
    have size := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 1≤2))
    rw [card_B1 (free.mono_bound (by omega : 4 ≤ q)) hv, reg v hv, two] at size
    omega
  have marks (u) : ∃ a, ∀ hu : u ∈ V, (ball D V u 4).card = B →
      a ∈ outN D V u ∧ B < (ball D V a 4).card ∧
      (ball D V a 2).card = 2 * r + 2 ∧ Nonempty (SinkBank D V u a r) := by
    by_cases h : u ∈ V ∧ (ball D V u 4).card = B
    · obtain ⟨two, three⟩ := profile u h.1 h.2
      have size := card_sdiff_add_card_eq_card
        (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
      have third := card_sdiff_add_card_eq_card
        (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
      obtain ⟨a,ha,sink,unique,strong⟩ := supplier u h.1 h.2
      obtain ⟨_,_,ba,inc⟩ :=
        SingleOmissionPacking.unique_successor (by omega : 4 ≤ r) diag
          (by omega : r - 1 < r) free reg h.1 two strong
          (show (ball D V u 3).card = 2 * r + 2 + (r - 1) by omega)
          ha sink unique
      have av := outN_subset ha
      have tall : B < (ball D V a 4).card := by
        by_contra! cap
        have bf := floor a av
        have p := (profile a av (by omega)).2
        omega
      obtain ⟨_,x,_,p,length,last,cover,shape⟩ :=
        unique_sink_geometry free diag (by omega) reg h.1 ha sink unique two (by omega) strong
      exact ⟨a,fun _ _ => ⟨ha,tall,ba,⟨⟨x,p,length,last,cover,shape⟩⟩⟩⟩
    · exact ⟨u, fun hu short => (h ⟨hu,short⟩).elim⟩
  choose child info using marks
  have head_tall (u) (hu : u ∈ V) (short : (ball D V u 4).card = B)
      {x : ℕ} (hx : x ∈ outN D V u) : B < (ball D V x 4).card := by
    obtain ⟨_,childTall,_,⟨bank⟩⟩ := info u hu short
    have xv := outN_subset hx
    have mx : x ∈ (range (bank.path.len + 1)).image bank.path.vertex := bank.support.symm ▸ hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp mx
    have ik : i ≤ bank.path.len := by have := mem_range.mp hi; omega
    by_cases last : i = bank.path.len
    · rwa [last,bank.last]
    · by_contra! cap
      have p := floor _ xv
      obtain ⟨_,_,_,⟨other⟩⟩ := info (bank.path.vertex i) xv (by omega)
      have step : bank.path.vertex (i + 1) ∈ outN D V (bank.path.vertex i) :=
        mem_outN.mpr ⟨outN_subset (bank.path.mem _ (by omega)),bank.path.edge i (by omega)⟩
      have low := other.at_most_one_internal free diag reg xv step
      have high := bank.consecutive_overlap free diag (by omega) reg hu
        (shell hu (profile u hu short).1) (i:=i) (by omega)
      omega
  apply no_balanced_child_cover (k:=4) free (by decide) (by omega)
    ⟨r,reg⟩ order (by omega) floor child
  · intro u hu short
    exact ⟨(info u hu short).1,(info u hu short).2.1⟩
  · intro u hu v hv bu bv same
    obtain ⟨ua,_,childTwo,⟨one⟩⟩ := info u hu bu
    obtain ⟨_,_,_,⟨two⟩⟩ := info v hv bv
    have other : SinkBank D V v (child u) r := same.symm ▸ two
    exact same_second_of_same_heads free (by omega) hu hv
      (one.same_heads other free diag (by omega) reg hu hv
        (shell hu (profile u hu bu).1) (shell hv (profile v hv bv).1) (shell (outN_subset ua) childTwo))
  · intro u hu v hv bu bv ne reach
    obtain ⟨_,_,_,⟨bank⟩⟩ := info u hu bu
    apply bank.transfer_four hu
    refine mem_sdiff.mpr ⟨reach,?_⟩
    intro h
    rcases (mem_ball_one hu).mp h with eq | xv
    · exact ne.symm eq
    · exact (Nat.ne_of_gt (head_tall u hu bu xv)) bv
  · intro u hu short
    obtain ⟨_,_,_,⟨bank⟩⟩ := info u hu short
    let p := bank.path
    let i := p.len - 4
    have length : p.len + 1 = r := bank.length
    have iz : i ≤ p.len := Nat.sub_le _ _
    have hx := p.mem i iz
    have av : child u ∈ V := outN_subset (bank.last ▸ p.mem _ le_rfl)
    have path := (p.walk iz le_rfl).mono (outN_subset : outN D V u ⊆ V)
    change Walk D V (p.vertex i) (p.vertex p.len) (p.len - i) at path
    have last : p.vertex p.len = child u := bank.last
    rw [last] at path
    have neq : p.vertex i ≠ child u := by
      intro eq
      have inj := p.injective (free.mono_set (outN_subset : outN D V u ⊆ V))
        ((reg u hu).le.trans diag)
      have zero := inj (mem_range.mpr (by omega : i < p.len + 1))
        (mem_range.mpr (by omega : p.len < p.len + 1)) (eq.trans last.symm)
      dsimp [i] at zero
      omega
    exact ⟨p.vertex i,hx,neq,head_tall u hu short hx,
      mem_ball_of_walk path (by dsimp [i]; omega) av⟩

/-- If every head of every floor row is strong, the existing one-omission
packing rule supplies the unique strong sinks used by the labelled proof. -/
theorem no_strong_balanced_family {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (degree : 6 ≤ r) (diag : r ≤ q)
    (distance : 4 + 4 ≤ q) (positive : 4 * r ≤ B) (order : V.card = B + B)
    (floor : ∀ u ∈ V, B ≤ (ball D V u 4).card)
    (profile : ∀ u ∈ V, (ball D V u 4).card = B →
      (ball D V u 2).card = 2 * r + 2 ∧ (ball D V u 3).card = 3 * r + 1)
    (strong : ∀ u ∈ V, (ball D V u 4).card = B →
      ∀ a ∈ outN D V u, 2 * r + 2 ≤ (ball D V a 2).card) : False := by
  apply no_unique_strong_sinks free reg degree diag distance positive order floor profile
  intro u hu eq
  obtain ⟨two, three⟩ := profile u hu eq
  obtain ⟨_,_,a,ha,sink,unique,_,_⟩ :=
    SingleOmissionPacking.recursive_successor (by omega : 4 ≤ r) diag
      (by omega : r - 1 < r) free reg hu two (strong u hu eq)
      (show (ball D V u 3).card = 2 * r + 2 + (r - 1) by omega)
  exact ⟨a,ha,sink,unique,strong u hu eq a ha⟩

/-- The first layer of an actual floor row contains a weak sink or two
distinct sinks. These alternatives retain the same source root. -/
theorem weak_sink_or_two_sinks {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (degree : 6 ≤ r) (diag : r ≤ q)
    (distance : 4 + 4 ≤ q) (positive : 4 * r ≤ B) (order : V.card = B + B)
    (floor : ∀ u ∈ V, B ≤ (ball D V u 4).card)
    (profile : ∀ u ∈ V, (ball D V u 4).card = B →
      (ball D V u 2).card = 2 * r + 2 ∧ (ball D V u 3).card = 3 * r + 1) :
    ∃ u ∈ V, (ball D V u 4).card = B ∧
      ∃ a ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) a ∧
        ((ball D V a 2).card < 2 * r + 2 ∨
          ∃ b ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) b ∧ b ≠ a) := by
  classical
  by_contra missing
  apply no_unique_strong_sinks free reg degree diag distance positive order floor profile
  intro u hu short
  let X := outN D V u
  have xc : X.card = r := reg u hu
  obtain ⟨a,ha,stop⟩ := exists_sink (T:=X) (free.mono_set outN_subset)
    (card_pos.mp (by omega)) (by omega)
  have ua : ∀ z ∈ X, SingleOmissionPacking.Sink D X z → z = a := by
    intro z hz sink
    by_contra ne
    exact missing ⟨u,hu,short,a,ha,stop,Or.inr ⟨z,hz,sink,ne⟩⟩
  have a2 : 2 * r + 2 ≤ (ball D V a 2).card := by
    by_contra! weak
    exact missing ⟨u,hu,short,a,ha,stop,Or.inl weak⟩
  exact ⟨a,ha,stop,ua,a2⟩

/-- The sink-only one-omission bound resolves the multiple-sink alternative
into a weak sink on the same physical first layer. -/
theorem weak_sink_of_balanced_profile {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (degree : 6 ≤ r) (diag : r ≤ q)
    (distance : 4 + 4 ≤ q) (positive : 4 * r ≤ B) (order : V.card = B + B)
    (floor : ∀ u ∈ V, B ≤ (ball D V u 4).card)
    (profile : ∀ u ∈ V, (ball D V u 4).card = B →
      (ball D V u 2).card = 2 * r + 2 ∧ (ball D V u 3).card = 3 * r + 1) :
    ∃ u ∈ V, (ball D V u 4).card = B ∧
      ∃ a ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) a ∧
        (ball D V a 2).card < 2 * r + 2 := by
  classical
  obtain ⟨u,hu,short,a,ha,sa,weak | many⟩ :=
    weak_sink_or_two_sinks free reg degree diag distance positive order floor profile
  · exact ⟨u,hu,short,a,ha,sa,weak⟩
  · obtain ⟨b,hb,sb,ne⟩ := many
    by_cases weak : ∃ w ∈ outN D V u, SingleOmissionPacking.Sink D (outN D V u) w ∧
        (ball D V w 2).card < 2 * r + 2
    · exact ⟨u,hu,short,weak⟩
    exfalso
    let X := outN D V u
    let Y := ball D V u 2 \ ball D V u 1
    let Z := ball D V u 3 \ ball D V u 2
    have xv : X ⊆ V := outN_subset
    have yv : Y ⊆ V := sdiff_subset.trans ball_subset
    have xc : X.card = r := reg u hu
    obtain ⟨b2,b3⟩ := profile u hu short
    have py := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1 ≤ 2))
    have pz := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2 ≤ 3))
    rw [card_B1 (free.mono_bound (by omega : 4 ≤ q)) hu, reg u hu, b2] at py
    rw [b2,b3] at pz
    change Y.card + (r + 1) = 2 * r + 2 at py
    change Z.card + (2 * r + 2) = 3 * r + 1 at pz
    have row {v : ℕ} (vy : v ∈ Y) : outN D V v ⊆ X ∪ Y ∪ Z := by
      intro w hw
      obtain ⟨wv,vw⟩ := mem_outN.mp hw
      have v2 := (mem_sdiff.mp vy).1
      have w3 := ball_step v2 wv vw
      by_cases w2 : w ∈ ball D V u 2
      · apply mem_union_left
        by_cases w1 : w ∈ ball D V u 1
        · rcases (mem_ball_one hu).mp w1 with rfl | wx
          · exact (no_back_arc free hu v2 (by omega : 2 + 1 ≤ q) vw).elim
          · exact mem_union_left _ wx
        · exact mem_union_right _ (mem_sdiff.mpr ⟨w2,w1⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨w3,w2⟩)
    have omission (s) (sx : s ∈ X) (stop : SingleOmissionPacking.Sink D X s) :
        ∃ b ∈ Y, outN D V s = Y.erase b :=
      sink_row_omission free (by omega) reg hu sx stop (by omega : Y.card = r + 1)
    have enough (s) (sx : s ∈ X) (stop : SingleOmissionPacking.Sink D X s) :
        Y.card + Z.card + 2 ≤ (ball D V s 2).card := by
      by_contra! tight
      exact weak ⟨s,sx,stop,by omega⟩
    exact SingleOmissionPacking.two_sinks_false_of_sink_ball_size
      (by omega) free xv yv (by omega) ha hb ne.symm sa sb omission (fun _ vy=>row vy) enough

/-- The only unmet premise of the strong-head closure is witnessed by
one actual low-two-ball head of a floor row. -/
theorem weak_head_of_balanced_profile {D : CH.Digraph} {V : Finset ℕ} {q r B : ℕ}
    (free : QFree D V q) (reg : OutEq r D V) (degree : 6 ≤ r) (diag : r ≤ q)
    (distance : 4 + 4 ≤ q)
    (positive : 4 * r ≤ B) (order : V.card = B + B)
    (floor : ∀ u ∈ V, B ≤ (ball D V u 4).card)
    (profile : ∀ u ∈ V, (ball D V u 4).card = B →
      (ball D V u 2).card = 2 * r + 2 ∧ (ball D V u 3).card = 3 * r + 1) :
    ∃ u ∈ V, (ball D V u 4).card = B ∧
      ∃ a ∈ outN D V u, (ball D V a 2).card < 2 * r + 2 := by
  by_contra! h
  exact no_strong_balanced_family free reg degree diag distance positive order floor profile h

#print axioms no_strong_balanced_family
#print axioms no_unique_strong_sinks
#print axioms weak_sink_or_two_sinks
#print axioms weak_sink_of_balanced_profile
#print axioms weak_head_of_balanced_profile
end LeanCH.BR.TallBankTransfer
