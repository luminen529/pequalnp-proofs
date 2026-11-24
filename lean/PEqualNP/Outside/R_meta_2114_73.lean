import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2114_73
    (relabel :
      let r := fun (C : Circuit) (v : Fin 9) =>
        Finset.univ.filter fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs
      let clean := fun (C : Circuit) => ∀ i : Fin C.size, let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
        ((g.op = GateOp.not ∧ g.inputs.length = 1) ∨ (g.op ≠ GateOp.not ∧ g.inputs.length = 2))
      ∀ (π : Equiv.Perm (Fin 9)) (C : Circuit), IsMinimalCircuit 9 C → clean C →
        ∃ D : Circuit, IsMinimalCircuit 9 D ∧ clean D ∧ D.size = C.size ∧
          (∀ x : Fin 9 → Bool, circuitFun 9 D x = circuitFun 9 C (x ∘ π)) ∧
          ∀ v, (r D (π v)).card = (r C v).card ∧
            ((∀ i ∈ r D (π v), (D.gates.get i).op = GateOp.or) ↔
              ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or))
    (atFour :
      let f := fun x : Fin 9 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let r := fun (C : Circuit) (v : Fin 9) =>
        Finset.univ.filter fun i : Fin C.size => v.val ∈ (C.gates.get i).inputs
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size ≤ 15 → circuitFun 9 C = f →
        (∀ i : Fin C.size, let g := C.gates.get i
          (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
          ((g.op = GateOp.not ∧ g.inputs.length = 1) ∨ (g.op ≠ GateOp.not ∧ g.inputs.length = 2))) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)), (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
          ((r C v).card = 2 → ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)), ∀ i ∈ r C v, (C.gates.get i).op = GateOp.or) →
        (r C 4).card = 2 → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  dsimp only
  intro C hC hAll hTwo
  obtain ⟨hmin, hsize, hFun, hclean, hReaders⟩ := hC
  obtain ⟨v, hv, hv2⟩ := hTwo
  let f := fun x : Fin 9 → Bool =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let S : List (Fin 9) := [4, 6, 7]
  let r := fun (D : Circuit) (u : Fin 9) =>
    Finset.univ.filter fun i : Fin D.size => u.val ∈ (D.gates.get i).inputs
  have hGraph : circuitFun 9 C = f := by
    rw [hFun]
    funext x
    simp [f, List.any_cons, Bool.or_assoc]
    rfl
  have orbit (u : Fin 9) (hu : u ∈ S) :
      ∃ π : Equiv.Perm (Fin 9), π u = 4 ∧ (∀ a, a ∈ S ↔ π a ∈ S) ∧
        ∀ x : Fin 9 → Bool, f (x ∘ π) = f x := by
    change u ∈ ([4, 6, 7] : List (Fin 9)) at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨Equiv.refl _, rfl, fun _ => Iff.rfl, fun _ => rfl⟩
    · let p : Equiv.Perm (Fin 9) :=
        ((Equiv.swap (0 : Fin 9) 1).trans (Equiv.swap 2 5)).trans
          ((Equiv.swap 3 8).trans (Equiv.swap 4 6))
      have hit : p 6 = 4 := by decide +kernel
      have domain : ∀ a, a ∈ S ↔ p a ∈ S := by decide +kernel
      have keeps : ∀ x : Fin 9 → Bool, f (x ∘ p) = f x := by decide +kernel
      exact ⟨p, hit, domain, keeps⟩
    · let p : Equiv.Perm (Fin 9) :=
        ((Equiv.swap (0 : Fin 9) 2).trans (Equiv.swap 3 5)).trans (Equiv.swap 4 7)
      have hit : p 7 = 4 := by decide +kernel
      have domain : ∀ a, a ∈ S ↔ p a ∈ S := by decide +kernel
      have keeps : ∀ x : Fin 9 → Bool, f (x ∘ p) = f x := by decide +kernel
      exact ⟨p, hit, domain, keeps⟩
  obtain ⟨π, hπ, hSet, hf⟩ := orbit v hv
  obtain ⟨D, hminD, hcleanD, hsD, hFunD, hReadD⟩ := relabel π C hmin hclean
  have evalD : circuitFun 9 D = f := by
    funext x
    rw [hFunD, hGraph, hf]
  have allD (u : Fin 9) (hu : u ∈ S) : ∀ i ∈ r D u, (D.gates.get i).op = GateOp.or := by
    let a := π.symm u
    have ha : a ∈ S := (hSet a).mpr (by simpa only [a, Equiv.apply_symm_apply] using hu)
    have hr := (hReadD a).2.mpr (hAll a ha)
    change ∀ i ∈ r D (π a), (D.gates.get i).op = GateOp.or at hr
    simpa only [a, Equiv.apply_symm_apply] using hr
  have twoD : (r D 4).card = 2 := by
    have h := (hReadD v).1
    change (r D (π v)).card = (r C v).card at h
    rw [hπ] at h
    exact h.trans hv2
  refine atFour D hminD (hsD.trans_le hsize) evalD hcleanD ?_ allD twoD
  intro u hu
  let a := π.symm u
  have ha : a ∈ S := (hSet a).mpr (by simpa only [a, Equiv.apply_symm_apply] using hu)
  obtain ⟨hNonempty, hBudget, _⟩ := hReaders a ha
  have count : (r D u).card = (r C a).card := by
    have h := (hReadD a).1
    change (r D (π a)).card = (r C a).card at h
    simpa only [a, Equiv.apply_symm_apply] using h
  refine ⟨Finset.card_pos.mp (count.symm ▸ Finset.card_pos.mpr hNonempty), count.trans_le hBudget, ?_⟩
  intro _
  exact allD u hu
