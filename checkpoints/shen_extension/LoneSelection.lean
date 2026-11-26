import checkpoints.shen_extension.TwoDeficits
import checkpoints.shen_extension.FlatTwoWitnesses

/-!
The capped one-short graph, and the selection test for the cutoff-three lone bank.

`capped`: an oriented graph without directed triangles on at most `3t` vertices (`t ≥ 2`)
cannot have out-degree `t` everywhere except `t - 1` at `x` while every in-degree is at
most `t`. The arc count leaves exactly one in-degree deficit; at `x` (or on fewer than
`3t` vertices) only `x` can be a good vertex, against `exists_two_goodVertices`; at another
vertex on `3t` vertices this is `two_deficits`.

`lone_selection_impossible`: the same statement for a selected subgraph `E` of a carrier
of the capstone.
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_first_eq_sum_rev (r : V → V → Prop) :
    ∑ v, (firstNeighbors r v).card = ∑ v, (firstNeighbors (rev r) v).card := by
  classical
  have hO : ∀ v, (firstNeighbors r v).card = ∑ w, if r v w then 1 else 0 := by
    intro v
    rw [← Finset.card_filter]
    congr 1
  have hI : ∀ v, (firstNeighbors (rev r) v).card = ∑ w, if r w v then 1 else 0 := by
    intro v
    rw [← Finset.card_filter]
    congr 1
  simp_rw [hO, hI]
  exact Finset.sum_comm

theorem sum_two_deficits_le (f : V → ℕ) (t : ℕ) (hle : ∀ v, f v ≤ t) (a b : V)
    (hab : a ≠ b) : ∑ v, f v + (t - f a) + (t - f b) ≤ Fintype.card V * t := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
  have hb : b ∈ (Finset.univ : Finset V).erase a :=
    Finset.mem_erase.mpr ⟨fun hc => hab hc.symm, Finset.mem_univ b⟩
  have h2 := Finset.add_sum_erase ((Finset.univ : Finset V).erase a) f hb
  have h3 : ∑ v ∈ ((Finset.univ : Finset V).erase a).erase b, f v ≤
      (((Finset.univ : Finset V).erase a).erase b).card * t := by
    have := Finset.sum_le_card_nsmul (((Finset.univ : Finset V).erase a).erase b) f t
      (fun v _ => hle v)
    simpa only [smul_eq_mul] using this
  have c1 := Finset.card_erase_add_one hb
  have c2 := Finset.card_erase_add_one (Finset.mem_univ a)
  rw [Finset.card_univ] at c2
  have hc : Fintype.card V =
      (((Finset.univ : Finset V).erase a).erase b).card + 2 := by omega
  have hmul : Fintype.card V * t =
      (((Finset.univ : Finset V).erase a).erase b).card * t + t + t := by
    rw [hc]
    ring
  have ha := hle a
  have hb' := hle b
  omega

/-- The capped one-short graph does not exist. -/
theorem capped {r : V → V → Prop} {t : ℕ} {x : V} (hr : IsOriented r)
    (htri : ∀ a b c, r a b → r b c → ¬ r c a) (hcard : Fintype.card V ≤ 3 * t)
    (ht : 2 ≤ t) (houtx : (firstNeighbors r x).card + 1 = t)
    (hout : ∀ v, v ≠ x → (firstNeighbors r v).card = t)
    (hin : ∀ v, (firstNeighbors (rev r) v).card ≤ t) : False := by
  classical
  have hne : Nonempty V := ⟨x⟩
  -- the arc count
  have hsumO : ∑ v, (firstNeighbors r v).card + 1 = Fintype.card V * t := by
    have h1 := Finset.add_sum_erase Finset.univ (fun v => (firstNeighbors r v).card)
      (Finset.mem_univ x)
    have h2 : ∑ v ∈ (Finset.univ : Finset V).erase x, (firstNeighbors r v).card =
        ((Finset.univ : Finset V).erase x).card * t := by
      rw [Finset.sum_congr rfl (fun v hv => hout v (Finset.mem_erase.mp hv).1),
        Finset.sum_const, smul_eq_mul]
    have c2 := Finset.card_erase_add_one (Finset.mem_univ x)
    rw [Finset.card_univ] at c2
    have hmul : Fintype.card V * t = ((Finset.univ : Finset V).erase x).card * t + t := by
      rw [← c2]
      ring
    omega
  have hsumI : ∑ v, (firstNeighbors (rev r) v).card + 1 = Fintype.card V * t := by
    rw [← sum_first_eq_sum_rev]
    exact hsumO
  have hsl : ∀ v, ∃ z, r v z := by
    intro v
    have hpos : 0 < (firstNeighbors r v).card := by
      by_cases hv : v = x
      · rw [hv]
        omega
      · have := hout v hv
        omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z, mem_firstNeighbors.mp hz⟩
  by_cases hy : ∃ y, y ≠ x ∧ (firstNeighbors (rev r) y).card + 1 = t ∧
      Fintype.card V = 3 * t
  · obtain ⟨y, hyx, hyin, hc⟩ := hy
    apply two_deficits (r := r) (t := t) (x := x) (y := y)
    refine ⟨hr, htri, hc, ht, fun h => hyx h.symm, houtx, hout, hyin, ?_⟩
    intro v hvy
    have h1 := sum_two_deficits_le (fun v => (firstNeighbors (rev r) v).card) t hin y v
      (fun h => hvy h.symm)
    have h2 := hin v
    omega
  · -- every vertex other than `x` is bad
    obtain ⟨u, v, huv, hu, hv⟩ := exists_two_goodVertices r hr hsl
    have key : ∀ w, w ≠ x → GoodVertex r w → False := by
      intro w hwx hgood
      unfold GoodVertex at hgood
      have h1 := card_partition r hr w
      have h2 := Finset.card_le_card (second_subset_nonadj r htri w)
      have h3 := hout w hwx
      have h4 := hin w
      have h5 := sum_two_deficits_le (fun v => (firstNeighbors (rev r) v).card) t hin w x hwx
      have h6 := hin x
      apply hy
      refine ⟨w, hwx, by omega, by omega⟩
    by_cases hux : u = x
    · exact key v (fun hvx => huv (hux.trans hvx.symm)) hv
    · exact key u hux hu

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.capped

namespace LeanCH.BR.ShenSeymour
open BRq2 BRq3 BR45 Finset

/-- **Selection test at cutoff three.** On a carrier with no directed cycle of length at
most three and at most `3t` labels (`t ≥ 2`), no subgraph `E` has out-degree `t` at every
label except `t - 1` at `x` while every in-degree is at most `t`. -/
theorem lone_selection_impossible {D E : CH.Digraph} {U : Finset ℕ} {q t x : ℕ}
    (free : QFree D U q) (cut : 3 ≤ q) (sub : ∀ a ∈ U, ∀ b ∈ U, E a b = true → D a b = true)
    (room : U.card ≤ 3 * t) (ht : 2 ≤ t) (xU : x ∈ U)
    (outx : (outN E U x).card + 1 = t)
    (out : ∀ v ∈ U, v ≠ x → (outN E U v).card = t)
    (inc : ∀ v ∈ U, (inN E U v).card ≤ t) : False := by
  classical
  let R (a b : ↥U) := E a.val b.val = true
  have oriented : OAI.SeymourSecondNeighborhood.IsOriented R :=
    ⟨fun a ha => loopfree free (by omega) a.property (sub _ a.property _ a.property ha),
     fun {a b} hab hba => digonfree free (by omega) a.property b.property
       (sub _ a.property _ b.property hab) (sub _ b.property _ a.property hba)⟩
  have tri : ∀ a b c : ↥U, R a b → R b c → ¬ R c a := by
    intro a b c hab hbc hca
    exact free a 3 (by decide) cut
      (.step b.property (sub _ a.property _ b.property hab)
        (.step c.property (sub _ b.property _ c.property hbc)
          (.step a.property (sub _ c.property _ a.property hca) (.refl _))))
  have firstCard : ∀ v : ↥U,
      (OAI.SeymourSecondNeighborhood.firstNeighbors R v).card = (outN E U v.val).card := by
    intro v
    have eq : (OAI.SeymourSecondNeighborhood.firstNeighbors R v).image Subtype.val =
        outN E U v.val := by
      ext z
      constructor
      · intro h
        obtain ⟨a, ha, rfl⟩ := mem_image.mp h
        exact mem_outN.mpr ⟨a.property,
          (OAI.SeymourSecondNeighborhood.mem_firstNeighbors (r := R)).mp ha⟩
      · intro h
        obtain ⟨hz, edge⟩ := mem_outN.mp h
        exact mem_image.mpr ⟨⟨z, hz⟩,
          (OAI.SeymourSecondNeighborhood.mem_firstNeighbors (r := R)).mpr edge, rfl⟩
    rw [← eq, card_image_of_injective _ Subtype.val_injective]
  have revCard : ∀ v : ↥U,
      (OAI.SeymourSecondNeighborhood.firstNeighbors (LeanCH.BR.TwoSeymour.rev R) v).card =
        (inN E U v.val).card := by
    intro v
    have eq : (OAI.SeymourSecondNeighborhood.firstNeighbors
        (LeanCH.BR.TwoSeymour.rev R) v).image Subtype.val = inN E U v.val := by
      ext z
      constructor
      · intro h
        obtain ⟨a, ha, rfl⟩ := mem_image.mp h
        exact mem_inN.mpr ⟨a.property, (OAI.SeymourSecondNeighborhood.mem_firstNeighbors
          (r := LeanCH.BR.TwoSeymour.rev R)).mp ha⟩
      · intro h
        obtain ⟨hz, edge⟩ := mem_inN.mp h
        exact mem_image.mpr ⟨⟨z, hz⟩, (OAI.SeymourSecondNeighborhood.mem_firstNeighbors
          (r := LeanCH.BR.TwoSeymour.rev R)).mpr edge, rfl⟩
    rw [← eq, card_image_of_injective _ Subtype.val_injective]
  apply LeanCH.BR.TwoSeymour.capped (r := R) (t := t) (x := ⟨x, xU⟩) oriented tri
  · rw [Fintype.card_coe]
    exact room
  · exact ht
  · rw [firstCard]
    exact outx
  · intro v hv
    rw [firstCard]
    exact out v.val v.property (fun h => hv (Subtype.ext h))
  · intro v
    rw [revCard]
    exact inc v.val v.property

#print axioms lone_selection_impossible

end LeanCH.BR.ShenSeymour
