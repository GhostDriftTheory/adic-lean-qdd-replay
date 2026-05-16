import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
ADIC Lean4 formalization (single-file merge)

This file is a mechanical merge of:
  * ADIC_Lean_QF.lean  (QF logic + normalization τ)
  * ADIC_Lean_Core.lean (encoded intervals + α/γ + division checks)

It is intentionally structured as:
  1) QF logic + τ
  2) Core interval semantics + division lemmas

Goal: keep a single namespace `ADIC` with one `import`.
-/

namespace ADIC

noncomputable section

/-!
ADIC Lean4 formalization (QF logic + normalization τ)

Scope:
  * Integer terms, atoms, quantifier-free formulas
  * Source-level atoms (`>`, `≥`, `≠`) and implication
  * Total normalization homomorphism τ into the core signature {+, -, *, ≤, <, =}
  * Truth-preservation of τ

This corresponds to the manuscript's `Σ_int`, `Σ_src`, `QFForm`, and `τ` lemmas.
-/


/-- Integer terms over `{const, +, -, *}`. -/
inductive IntTerm : Type
  | const : ℤ → IntTerm
  | add   : IntTerm → IntTerm → IntTerm
  | sub   : IntTerm → IntTerm → IntTerm
  | mul   : IntTerm → IntTerm → IntTerm
  deriving DecidableEq

namespace IntTerm

/-- Evaluate a term into `ℤ`. -/
def eval : IntTerm → ℤ
  | const z => z
  | add a b => eval a + eval b
  | sub a b => eval a - eval b
  | mul a b => eval a * eval b

end IntTerm

/-- Core atoms over `=, <, ≤` on integer terms. -/
inductive Atom : Type
  | eq  : IntTerm → IntTerm → Atom
  | lt  : IntTerm → IntTerm → Atom
  | le  : IntTerm → IntTerm → Atom
  deriving DecidableEq

namespace Atom

def eval : Atom → Bool
  | eq a b => decide (IntTerm.eval a = IntTerm.eval b)
  | lt a b => decide (IntTerm.eval a < IntTerm.eval b)
  | le a b => decide (IntTerm.eval a ≤ IntTerm.eval b)

end Atom

/-- Quantifier-free boolean formulas. -/
inductive QFForm : Type
  | atom : Atom → QFForm
  | and  : QFForm → QFForm → QFForm
  | or   : QFForm → QFForm → QFForm
  | not  : QFForm → QFForm
  deriving DecidableEq

namespace QFForm

/-- Evaluate a QF formula into `Bool`. -/
def eval : QFForm → Bool
  | atom a => Atom.eval a
  | and p q => eval p && eval q
  | or  p q => eval p || eval q
  | not p   => !(eval p)

/-- Truth predicate. -/
def Holds (p : QFForm) : Prop := eval p = true

end QFForm

/-- Source-level atoms: allow `>`, `≥`, `≠` (plus the core atoms). -/
inductive SrcAtom : Type
  | eq  : IntTerm → IntTerm → SrcAtom
  | lt  : IntTerm → IntTerm → SrcAtom
  | le  : IntTerm → IntTerm → SrcAtom
  | gt  : IntTerm → IntTerm → SrcAtom
  | ge  : IntTerm → IntTerm → SrcAtom
  | ne  : IntTerm → IntTerm → SrcAtom
  deriving DecidableEq

namespace SrcAtom

def eval : SrcAtom → Bool
  | eq a b => decide (IntTerm.eval a = IntTerm.eval b)
  | lt a b => decide (IntTerm.eval a < IntTerm.eval b)
  | le a b => decide (IntTerm.eval a ≤ IntTerm.eval b)
  | gt a b => decide (IntTerm.eval a > IntTerm.eval b)
  | ge a b => decide (IntTerm.eval a ≥ IntTerm.eval b)
  | ne a b => decide (IntTerm.eval a ≠ IntTerm.eval b)

end SrcAtom

/-- Source-level formulas: allow implication and `true` as a primitive token. -/
inductive SrcForm : Type
  | atom   : SrcAtom → SrcForm
  | and    : SrcForm → SrcForm → SrcForm
  | or     : SrcForm → SrcForm → SrcForm
  | not    : SrcForm → SrcForm
  | imp    : SrcForm → SrcForm → SrcForm
  | trueLit : SrcForm
  deriving DecidableEq

namespace SrcForm

def eval : SrcForm → Bool
  | atom a => SrcAtom.eval a
  | and p q => eval p && eval q
  | or  p q => eval p || eval q
  | not p   => !(eval p)
  | imp p q => (!eval p) || eval q
  | trueLit => true

def Holds (p : SrcForm) : Prop := eval p = true

end SrcForm

/-- Total normalization homomorphism `τ : SrcForm → QFForm`.

Maps:
  * `>` to swapped `<`
  * `≥` to swapped `≤`
  * `≠` to `(a<b) ∨ (b<a)`
  * `P → Q` to `¬P ∨ Q`
  * `true` to `(0=0)`
-/
def tauAtom : SrcAtom → QFForm
  | SrcAtom.eq a b => QFForm.atom (Atom.eq a b)
  | SrcAtom.lt a b => QFForm.atom (Atom.lt a b)
  | SrcAtom.le a b => QFForm.atom (Atom.le a b)
  | SrcAtom.gt a b => QFForm.atom (Atom.lt b a)
  | SrcAtom.ge a b => QFForm.atom (Atom.le b a)
  | SrcAtom.ne a b => QFForm.or (QFForm.atom (Atom.lt a b)) (QFForm.atom (Atom.lt b a))

def tau : SrcForm → QFForm
  | SrcForm.atom a => tauAtom a
  | SrcForm.and p q => QFForm.and (tau p) (tau q)
  | SrcForm.or  p q => QFForm.or  (tau p) (tau q)
  | SrcForm.not p   => QFForm.not (tau p)
  | SrcForm.imp p q => QFForm.or (QFForm.not (tau p)) (tau q)
  | SrcForm.trueLit => QFForm.atom (Atom.eq (IntTerm.const 0) (IntTerm.const 0))

/-- Trichotomy-based equivalence used for `≠` expansion. -/
lemma ne_iff_lt_or_gt (a b : ℤ) : (a ≠ b) ↔ (a < b ∨ b < a) := by
  constructor
  · intro hne
    exact lt_or_gt_of_ne hne
  · intro h
    rcases h with hlt | hgt
    · exact ne_of_lt hlt
    · exact ne_of_gt hgt

/-- Truth preservation of `τ` (normalization does not change evaluation). -/
theorem tau_preserves (p : SrcForm) : SrcForm.eval p = QFForm.eval (tau p) := by
  induction p with
  | atom a =>
      cases a with
      | eq a b => rfl
      | lt a b => rfl
      | le a b => rfl
      | gt a b => rfl
      | ge a b => rfl
      | ne a b =>
          change decide (IntTerm.eval a ≠ IntTerm.eval b) =
            (decide (IntTerm.eval a < IntTerm.eval b) || decide (IntTerm.eval b < IntTerm.eval a))
          by_cases hne : IntTerm.eval a ≠ IntTerm.eval b
          · rcases (ne_iff_lt_or_gt (IntTerm.eval a) (IntTerm.eval b)).mp hne with hlt | hgt
            · have hnot : ¬ IntTerm.eval b < IntTerm.eval a := not_lt_of_ge (le_of_lt hlt)
              simp [hne, hlt, hnot]
            · have hnot : ¬ IntTerm.eval a < IntTerm.eval b := not_lt_of_ge (le_of_lt hgt)
              simp [hne, hgt, hnot]
          · have hEq : IntTerm.eval a = IntTerm.eval b := by
              by_contra hEq'
              exact hne hEq'
            have hnot1 : ¬ IntTerm.eval a < IntTerm.eval b := by
              simp [hEq]
            have hnot2 : ¬ IntTerm.eval b < IntTerm.eval a := by
              simp [hEq]
            simp [hne, hnot1, hnot2]
  | and p q ihp ihq =>
      change (SrcForm.eval p && SrcForm.eval q) =
        (QFForm.eval (tau p) && QFForm.eval (tau q))
      simp [ihp, ihq]
  | or p q ihp ihq =>
      change (SrcForm.eval p || SrcForm.eval q) =
        (QFForm.eval (tau p) || QFForm.eval (tau q))
      simp [ihp, ihq]
  | not p ih =>
      change (!SrcForm.eval p) = (!QFForm.eval (tau p))
      simp [ih]
  | imp p q ihp ihq =>
      change ((!SrcForm.eval p) || SrcForm.eval q) =
        ((!QFForm.eval (tau p)) || QFForm.eval (tau q))
      simp [ihp, ihq]
  | trueLit =>
      rfl

/-- The Prop-level corollary: `p` holds iff `τ p` holds. -/
theorem tau_truth (p : SrcForm) : SrcForm.Holds p ↔ QFForm.Holds (tau p) := by
  unfold SrcForm.Holds QFForm.Holds
  simp [tau_preserves p]


/-!
ADIC Lean4 formalization (core skeleton)

Scope of this file:
  * Encoded fixed-point interval domain I_D
  * Concretization γ_D and outward abstraction α_D via floor/ceil
  * Orders (subset-style) and a Galois insertion α ⊣ γ
  * Witnessed division checks: FDIV/CDIV (statements + core lemmas)

This is designed to match the structure of ADIC証明8.txt, but as Lean code.
-/


open Set

/-- Positive scaling factor `D` (the global fixed-point denominator). -/
abbrev DPos := ℕ+

/-- A closed real interval represented by endpoints. Order is *subset order*. -/
structure RInterval where
  lo : ℝ
  hi : ℝ
  h  : lo ≤ hi

namespace RInterval

/-- Subset order on closed intervals: `J ≤ K` means `J ⊆ K`. -/
instance : LE RInterval where
  le J K := K.lo ≤ J.lo ∧ J.hi ≤ K.hi

theorem le_def (J K : RInterval) : (J ≤ K) = (K.lo ≤ J.lo ∧ J.hi ≤ K.hi) := rfl

instance : Preorder RInterval where
  le := (· ≤ ·)
  le_refl J := by exact ⟨le_rfl, le_rfl⟩
  le_trans A B C hAB hBC := by
    rcases hAB with ⟨hAB1, hAB2⟩
    rcases hBC with ⟨hBC1, hBC2⟩
    exact ⟨le_trans hBC1 hAB1, le_trans hAB2 hBC2⟩

@[ext] theorem ext {J K : RInterval} (hlo : J.lo = K.lo) (hhi : J.hi = K.hi) : J = K := by
  cases J
  cases K
  cases hlo
  cases hhi
  rfl

/-- As a `Set ℝ`. -/
def toSet (J : RInterval) : Set ℝ := Icc J.lo J.hi

theorem subset_iff_le {J K : RInterval} : J.toSet ⊆ K.toSet ↔ J ≤ K := by
  -- `Set.Icc_subset_Icc` characterizes inclusion by endpoints.
  simp [RInterval.toSet, RInterval.le_def, Set.Icc_subset_Icc_iff, J.h]

end RInterval

/-- Encoded fixed-point interval domain `I_D := {(a,b) ∈ ℤ×ℤ | a ≤ b}`. -/
structure IEnc (D : DPos) where
  lo : ℤ
  hi : ℤ
  h  : lo ≤ hi

namespace IEnc

/-- Subset order on encoded intervals: `I ≤ J` means `γ(I) ⊆ γ(J)`.
    This matches the paper: `(a,b) ⊑ (c,d) :↔ (c ≤ a) ∧ (b ≤ d)`.
-/
instance (D : DPos) : LE (IEnc D) where
  le I J := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

theorem le_def {D : DPos} (I J : IEnc D) : (I ≤ J) = (J.lo ≤ I.lo ∧ I.hi ≤ J.hi) := rfl

instance (D : DPos) : Preorder (IEnc D) where
  le := (· ≤ ·)
  le_refl I := by exact ⟨le_rfl, le_rfl⟩
  le_trans A B C hAB hBC := by
    rcases hAB with ⟨hAB1, hAB2⟩
    rcases hBC with ⟨hBC1, hBC2⟩
    exact ⟨le_trans hBC1 hAB1, le_trans hAB2 hBC2⟩

@[ext] theorem ext {D : DPos} {I J : IEnc D} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
  cases I
  cases J
  cases hlo
  cases hhi
  rfl

/-- Coercion of `D : ℕ+` into `ℝ`. -/
def Dℝ (D : DPos) : ℝ := (D : ℕ)  -- will be coerced to ℝ

lemma Dℝ_pos (D : DPos) : (0 : ℝ) < (D : ℕ) := by
  exact_mod_cast D.2

/-- Concretization `γ_D : I_D → RInterval`, i.e. decode `[a/D, b/D]`. -/
def gamma (D : DPos) (I : IEnc D) : RInterval := by
  refine ⟨(I.lo : ℝ) / (D : ℕ), (I.hi : ℝ) / (D : ℕ), ?_⟩
  have hD : (0 : ℝ) < (D : ℕ) := Dℝ_pos D
  -- divide inequality by positive constant
  exact (div_le_div_of_nonneg_right (by exact_mod_cast I.h) (le_of_lt hD))

/-- Outward abstraction `α_D : RInterval → I_D` via floor/ceil.
    Lower endpoint uses floor, upper endpoint uses ceil.
-/
def alpha (D : DPos) (J : RInterval) : IEnc D := by
  let x : ℝ := (D : ℕ) * J.lo
  let y : ℝ := (D : ℕ) * J.hi
  refine ⟨Int.floor x, Int.ceil y, ?_⟩
  -- show `floor x ≤ ceil y`
  have hD : (0 : ℝ) ≤ (D : ℕ) := le_of_lt (Dℝ_pos D)
  have hxy : x ≤ y := by
    -- multiply `J.lo ≤ J.hi` by nonnegative `(D:ℝ)`
    simpa [x, y] using (mul_le_mul_of_nonneg_left J.h hD)
  have hcast : ((Int.floor x : ℝ) ≤ (Int.ceil y : ℝ)) := by
    have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have h2 : y ≤ (Int.ceil y : ℝ) := Int.le_ceil y
    exact le_trans (le_trans h1 hxy) h2
  -- turn cast-inequality back into `ℤ` inequality
  exact (by
    -- `exact_mod_cast` is the standard bridge for `Int.cast` inequalities.
    exact_mod_cast hcast)

/-- `γ` is monotone w.r.t. the subset orders. -/
lemma gamma_mono {D : DPos} : Monotone (gamma D) := by
  intro I J hIJ
  -- unfold order and reduce to endpoint comparisons
  rcases hIJ with ⟨hlo, hhi⟩
  -- Want: `gamma D I ≤ gamma D J` in RInterval order,
  -- i.e. `J.lo ≤ I.lo` and `I.hi ≤ J.hi` after decoding.
  -- This is immediate by dividing by positive `D`.
  have hD : (0 : ℝ) < (D : ℕ) := Dℝ_pos D
  constructor
  · -- lower endpoints: (J.lo)/D ≤ (I.lo)/D
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo) (le_of_lt hD))
  · -- upper endpoints: (I.hi)/D ≤ (J.hi)/D
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hhi) (le_of_lt hD))

/-- `α` is monotone w.r.t. the subset orders. -/
lemma alpha_mono {D : DPos} : Monotone (alpha D) := by
  intro J K hJK
  -- `hJK : J ≤ K` means `K.lo ≤ J.lo` and `J.hi ≤ K.hi` (subset order).
  rcases hJK with ⟨hlo, hhi⟩
  classical
  -- Goal: `alpha D J ≤ alpha D K` in encoded subset order, i.e.
  --   floor(D*K.lo) ≤ floor(D*J.lo)   and   ceil(D*J.hi) ≤ ceil(D*K.hi).
  refine And.intro ?_ ?_
  · -- lower endpoint (floor) is monotone
    have hD : (0 : ℝ) ≤ (D : ℕ) := le_of_lt (Dℝ_pos D)
    have hx : ((D : ℕ) * K.lo) ≤ ((D : ℕ) * J.lo) := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hlo hD)
    have hx' : (Int.floor ((D : ℕ) * K.lo) : ℝ) ≤ ((D : ℕ) * J.lo) :=
      le_trans (Int.floor_le _) hx
    -- `z ≤ floor a ↔ (z:ℝ) ≤ a` with `z = floor(D*K.lo)` and `a = D*J.lo`
    exact (Int.le_floor).2 hx'
  · -- upper endpoint (ceil) is monotone
    have hD : (0 : ℝ) ≤ (D : ℕ) := le_of_lt (Dℝ_pos D)
    have hy : ((D : ℕ) * J.hi) ≤ ((D : ℕ) * K.hi) := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hhi hD)
    have hy' : ((D : ℕ) * J.hi) ≤ (Int.ceil ((D : ℕ) * K.hi) : ℝ) :=
      le_trans hy (Int.le_ceil _)
    -- `ceil a ≤ z ↔ a ≤ (z:ℝ)` with `a = D*J.hi` and `z = ceil(D*K.hi)`
    exact (Int.ceil_le).2 hy'

lemma div_le_of_le_mul_pos_aux {a b c : ℝ} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 ≤ c⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma le_div_of_mul_le_pos_aux {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 ≤ c⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Galois connection `α ⊣ γ` (the adjunction condition). -/
theorem gc_alpha_gamma (D : DPos) : GaloisConnection (alpha D) (gamma D) := by
  intro J I
  constructor
  · intro h
    rcases h with ⟨hlo, hhi⟩
    have hDpos : (0 : ℝ) < (D : ℕ) := Dℝ_pos D
    constructor
    · have h0 : (I.lo : ℝ) ≤ J.lo * (((D : ℕ) : ℝ)) := by
        simpa [mul_comm] using (Int.le_floor).1 hlo
      have : (I.lo : ℝ) / (D : ℕ) ≤ J.lo :=
        div_le_of_le_mul_pos_aux hDpos h0
      simpa [gamma] using this
    · have h0 : J.hi * (((D : ℕ) : ℝ)) ≤ (I.hi : ℝ) := by
        simpa [mul_comm] using (Int.ceil_le).1 hhi
      have : J.hi ≤ (I.hi : ℝ) / (D : ℕ) :=
        le_div_of_mul_le_pos_aux hDpos h0
      simpa [gamma] using this
  · intro h
    rcases h with ⟨hlo, hhi⟩
    have hDpos : (0 : ℝ) < (D : ℕ) := Dℝ_pos D
    have hDnn : (0 : ℝ) ≤ (D : ℕ) := le_of_lt hDpos
    constructor
    · have h0 := mul_le_mul_of_nonneg_left hlo hDnn
      have : (I.lo : ℝ) ≤ ((D : ℕ) : ℝ) * J.lo := by
        simpa [gamma, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ne_of_gt hDpos] using h0
      exact (Int.le_floor).2 this
    · have h0 := mul_le_mul_of_nonneg_left hhi hDnn
      have : (((D : ℕ) : ℝ) * J.hi) ≤ (I.hi : ℝ) := by
        simpa [gamma, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ne_of_gt hDpos] using h0
      exact (Int.ceil_le).2 this

/-- The key insertion identity: `α (γ I) = I`. -/
lemma alpha_gamma_id (D : DPos) (I : IEnc D) : alpha D (gamma D I) = I := by
  cases I with
  | mk lo hi h =>
      have hDne : ((D : ℕ) : ℝ) ≠ 0 := by
        exact ne_of_gt (Dℝ_pos D)
      have hlo : ((D : ℕ) : ℝ) * ((lo : ℝ) / (D : ℕ)) = (lo : ℝ) := by
        field_simp [hDne]
      have hhi : ((D : ℕ) : ℝ) * ((hi : ℝ) / (D : ℕ)) = (hi : ℝ) := by
        field_simp [hDne]
      simp [alpha, gamma, hlo, hhi]

/-- Strictness in the form used by the manuscript: `α ∘ γ = id`. -/
theorem alpha_gamma_strict (D : DPos) (I : IEnc D) : alpha D (gamma D I) = I :=
  alpha_gamma_id D I

end IEnc

/-- Witnessed “floor division” check (exactly as in the paper). -/
def CheckFDIV (z d Q : ℤ) : Prop :=
  (0 < d ∧ Q * d ≤ z ∧ z < (Q + 1) * d)
  ∨ (d < 0 ∧ Q * d ≥ z ∧ z > (Q + 1) * d)

/-- Witnessed “ceiling division” check (exactly as in the paper). -/
def CheckCDIV (z d Q : ℤ) : Prop :=
  (0 < d ∧ (Q - 1) * d < z ∧ z ≤ Q * d)
  ∨ (d < 0 ∧ (Q - 1) * d > z ∧ z ≥ Q * d)

namespace Division

/-- A small helper: cast `ℤ` into `ℝ`. -/
abbrev zR (z : ℤ) : ℝ := (z : ℝ)

/-! NOTE: We intentionally rely on Mathlib's division-inequality lemmas
    (`le_div_iff_of_neg`, `div_lt_iff_of_neg`, `lt_div_iff_of_neg`, `div_le_iff_of_neg`)
    instead of re-proving “divide by negative flips inequalities”. -/

lemma le_div_of_mul_le_pos {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 ≤ c⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma div_le_of_le_mul_pos {a b c : ℝ} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 ≤ c⁻¹ := by positivity
  have hmul := mul_le_mul_of_nonneg_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma div_lt_of_lt_mul_pos {a b c : ℝ} (hc : 0 < c) (h : a < b * c) : a / c < b := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 < c⁻¹ := by positivity
  have hmul := mul_lt_mul_of_pos_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma lt_div_of_mul_lt_pos {a b c : ℝ} (hc : 0 < c) (h : a * c < b) : a < b / c := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hinv : 0 < c⁻¹ := by positivity
  have hmul := mul_lt_mul_of_pos_right h hinv
  simpa [div_eq_mul_inv, hc0, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- FDIV bounding lemma (statement matches the manuscript):
    If `CheckFDIV z d Q` holds, then `Q ≤ z/d < Q+1` in real arithmetic.
-/
lemma fdiv_bound (z d Q : ℤ) :
    CheckFDIV z d Q →
      ((Q : ℝ) ≤ (z : ℝ) / (d : ℝ) ∧ (z : ℝ) / (d : ℝ) < ((Q + 1 : ℤ) : ℝ)) := by
  intro h
  rcases h with hpos | hneg
  · rcases hpos with ⟨hd, h1, h2⟩
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h1R : (Q : ℝ) * (d : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1
    have h2R : (z : ℝ) < (((Q + 1 : ℤ) : ℝ) * (d : ℝ)) := by exact_mod_cast h2
    exact ⟨le_div_of_mul_le_pos hdR h1R, div_lt_of_lt_mul_pos hdR h2R⟩
  · rcases hneg with ⟨hd, h1, h2⟩
    have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
    have h1R : (z : ℝ) ≤ (Q : ℝ) * (d : ℝ) := by
      simpa [ge_iff_le] using (by exact_mod_cast h1 : (Q : ℝ) * (d : ℝ) ≥ (z : ℝ))
    have h2R : (((Q + 1 : ℤ) : ℝ) * (d : ℝ)) < (z : ℝ) := by
      simpa [gt_iff_lt] using (by exact_mod_cast h2 : (z : ℝ) > (((Q + 1 : ℤ) : ℝ) * (d : ℝ)))
    exact ⟨(le_div_iff_of_neg hdR).2 h1R, by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (div_lt_iff_of_neg hdR).2 h2R⟩

/-- CDIV bounding lemma (statement matches the manuscript):
    If `CheckCDIV z d Q` holds, then `Q-1 < z/d ≤ Q` in real arithmetic.
-/
lemma cdiv_bound (z d Q : ℤ) :
    CheckCDIV z d Q →
      ((((Q - 1 : ℤ) : ℝ) < (z : ℝ) / (d : ℝ)) ∧ ((z : ℝ) / (d : ℝ) ≤ (Q : ℝ))) := by
  intro h
  rcases h with hpos | hneg
  · rcases hpos with ⟨hd, h1, h2⟩
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h1R : (((Q - 1 : ℤ) : ℝ) * (d : ℝ)) < (z : ℝ) := by exact_mod_cast h1
    have h2R : (z : ℝ) ≤ ((Q : ℝ) * (d : ℝ)) := by exact_mod_cast h2
    exact ⟨lt_div_of_mul_lt_pos hdR h1R, div_le_of_le_mul_pos hdR h2R⟩
  · rcases hneg with ⟨hd, h1, h2⟩
    have hdR : (d : ℝ) < 0 := by exact_mod_cast hd
    have h1R : (z : ℝ) < (((Q - 1 : ℤ) : ℝ) * (d : ℝ)) := by
      simpa [gt_iff_lt] using (by exact_mod_cast h1 : (((Q - 1 : ℤ) : ℝ) * (d : ℝ)) > (z : ℝ))
    have h2R : ((Q : ℝ) * (d : ℝ)) ≤ (z : ℝ) := by
      simpa [ge_iff_le] using (by exact_mod_cast h2 : (z : ℝ) ≥ ((Q : ℝ) * (d : ℝ)))
    exact ⟨(lt_div_iff_of_neg hdR).2 h1R, by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (div_le_iff_of_neg hdR).2 h2R⟩

end Division


/-!
Section: Primitive R-SOUND (Σ_prim)

We formalize R-SOUND for the concrete primitives:
  +, -, ×, inv, sqrt, relu

Style:
  * Soundness is stated elementwise on concretizations `γset`.
  * The multiplication / inversion / sqrt cases are witness-based and use
    the already-proved FDIV/CDIV bounds.
-/

namespace Primitives

open Set
open Division

variable {D : DPos}

-- Basic helpers: concretization set and endpoints.
def loR (D : DPos) (I : IEnc D) : ℝ := (I.lo : ℝ) / (D : ℕ)
def hiR (D : DPos) (I : IEnc D) : ℝ := (I.hi : ℝ) / (D : ℕ)

def γset (D : DPos) (I : IEnc D) : Set ℝ := Icc (loR D I) (hiR D I)

@[simp] lemma mem_γset {D : DPos} {I : IEnc D} {x : ℝ} :
    x ∈ γset D I ↔ loR D I ≤ x ∧ x ≤ hiR D I := Iff.rfl

lemma DposR (D : DPos) : (0 : ℝ) < (D : ℕ) := IEnc.Dℝ_pos D
lemma Dne0R (D : DPos) : ((D : ℕ) : ℝ) ≠ 0 := ne_of_gt (DposR D)

lemma div_le_div_Dpos {D : DPos} {a b : ℝ} (h : a ≤ b) : a / (D : ℕ) ≤ b / (D : ℕ) :=
  div_le_div_of_nonneg_right h (le_of_lt (DposR D))

lemma div_lt_div_Dpos {D : DPos} {a b : ℝ} (h : a < b) : a / (D : ℕ) < b / (D : ℕ) :=
  div_lt_div_of_pos_right h (DposR D)


lemma scale_mem_Icc_of_mem_γ {D : DPos} {I : IEnc D} {x : ℝ}
    (hx : x ∈ γset D I) :
    (((D : ℕ) : ℝ) * x) ∈ Icc (I.lo : ℝ) (I.hi : ℝ) := by
  rcases hx with ⟨hxL, hxU⟩
  have hDpos : (0 : ℝ) < (D : ℕ) := DposR D
  have hDnn : (0 : ℝ) ≤ (D : ℕ) := le_of_lt hDpos
  constructor
  · have h := mul_le_mul_of_nonneg_left hxL hDnn
    simpa [loR, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Dne0R D] using h
  · have h := mul_le_mul_of_nonneg_left hxU hDnn
    simpa [hiR, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Dne0R D] using h

lemma mul_fixed_right_bounds {a b x y : ℝ}
    (hx : x ∈ Icc a b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases hx with ⟨hax, hxb⟩
  by_cases hy : 0 ≤ y
  · have hL : a * y ≤ x * y := mul_le_mul_of_nonneg_right hax hy
    have hU : x * y ≤ b * y := mul_le_mul_of_nonneg_right hxb hy
    exact ⟨le_trans (min_le_left _ _) hL, le_trans hU (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hL : b * y ≤ x * y := mul_le_mul_of_nonpos_right hxb hy'
    have hU : x * y ≤ a * y := mul_le_mul_of_nonpos_right hax hy'
    exact ⟨le_trans (min_le_right _ _) hL, le_trans hU (le_max_left _ _)⟩

lemma mul_fixed_left_bounds {c d x y : ℝ}
    (hy : y ∈ Icc c d) :
    min (x * c) (x * d) ≤ x * y ∧ x * y ≤ max (x * c) (x * d) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_fixed_right_bounds (a := c) (b := d) (x := y) (y := x) hy)

lemma div_pow_two_le_of_sq_le_mul {a b D : ℝ}
    (hD : 0 < D) (h : a ^ 2 ≤ b * D) : (a / D) ^ 2 ≤ b / D := by
  have hD2 : 0 < D ^ 2 := by positivity
  have hdiv : a ^ 2 / D ^ 2 ≤ (b * D) / D ^ 2 :=
    div_le_div_of_nonneg_right h (le_of_lt hD2)
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hleft : a ^ 2 / D ^ 2 = (a / D) ^ 2 := by
    field_simp [pow_two, hD0]
  have hright : (b * D) / D ^ 2 = b / D := by
    field_simp [pow_two, hD0]
  rw [hleft, hright] at hdiv
  exact hdiv

lemma le_div_pow_two_of_mul_le_sq {a b D : ℝ}
    (hD : 0 < D) (h : b * D ≤ a ^ 2) : b / D ≤ (a / D) ^ 2 := by
  have hD2 : 0 < D ^ 2 := by positivity
  have hdiv : (b * D) / D ^ 2 ≤ a ^ 2 / D ^ 2 :=
    div_le_div_of_nonneg_right h (le_of_lt hD2)
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hleft : (b * D) / D ^ 2 = b / D := by
    field_simp [pow_two, hD0]
  have hright : a ^ 2 / D ^ 2 = (a / D) ^ 2 := by
    field_simp [pow_two, hD0]
  rw [hleft, hright] at hdiv
  exact hdiv

-- ---------------------------------------------------------------------------
-- Addition
-- ---------------------------------------------------------------------------

def T_add (D : DPos) (I J : IEnc D) : IEnc D :=
  ⟨I.lo + J.lo, I.hi + J.hi, by exact add_le_add I.h J.h⟩

theorem rsound_add (D : DPos) (I J : IEnc D) :
    ∀ {x y : ℝ}, x ∈ γset D I → y ∈ γset D J → (x + y) ∈ γset D (T_add D I J) := by
  intro x y hx hy
  rcases hx with ⟨hxL, hxU⟩
  rcases hy with ⟨hyL, hyU⟩
  refine ⟨?_, ?_⟩
  · -- lower
    -- (I.lo)/D + (J.lo)/D ≤ x + y
    have : loR D I + loR D J ≤ x + y := add_le_add hxL hyL
    simpa [γset, loR, hiR, T_add, add_div] using this
  · -- upper
    have : x + y ≤ hiR D I + hiR D J := add_le_add hxU hyU
    simpa [γset, loR, hiR, T_add, add_div] using this

-- ---------------------------------------------------------------------------
-- Subtraction
-- ---------------------------------------------------------------------------

def T_sub (D : DPos) (I J : IEnc D) : IEnc D :=
  ⟨I.lo - J.hi, I.hi - J.lo, by
      have h1 : I.lo - J.hi ≤ I.hi - J.hi := sub_le_sub_right I.h _
      have h2 : I.hi - J.hi ≤ I.hi - J.lo := by
        have : -J.hi ≤ -J.lo := by exact neg_le_neg J.h
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (add_le_add_left this I.hi)
      exact le_trans h1 h2⟩

theorem rsound_sub (D : DPos) (I J : IEnc D) :
    ∀ {x y : ℝ}, x ∈ γset D I → y ∈ γset D J → (x - y) ∈ γset D (T_sub D I J) := by
  intro x y hx hy
  rcases hx with ⟨hxL, hxU⟩
  rcases hy with ⟨hyL, hyU⟩
  refine ⟨?_, ?_⟩
  · have hcast :
      loR D (T_sub D I J) = (I.lo : ℝ) / (D : ℕ) - (J.hi : ℝ) / (D : ℕ) := by
      unfold loR T_sub
      rw [Int.cast_sub, sub_div]
    rw [hcast]
    exact sub_le_sub hxL hyU
  · have hcast :
      hiR D (T_sub D I J) = (I.hi : ℝ) / (D : ℕ) - (J.lo : ℝ) / (D : ℕ) := by
      unfold hiR T_sub
      rw [Int.cast_sub, sub_div]
    rw [hcast]
    exact sub_le_sub hxU hyL

-- ---------------------------------------------------------------------------
-- ReLU
-- ---------------------------------------------------------------------------

def relu (x : ℝ) : ℝ := max x 0

def T_relu (D : DPos) (I : IEnc D) : IEnc D :=
  ⟨max I.lo 0, max I.hi 0, by
      -- max lo 0 ≤ max hi 0
      exact max_le_max I.h (le_rfl)⟩

lemma loR_T_relu (D : DPos) (I : IEnc D) :
    loR D (T_relu D I) = max (loR D I) 0 := by
  by_cases h : 0 ≤ I.lo
  · have hloR : 0 ≤ loR D I := by
      unfold loR
      exact div_nonneg (by exact_mod_cast h) (le_of_lt (DposR D))
    have h1 : max I.lo 0 = I.lo := max_eq_left h
    have h2 : max (loR D I) 0 = loR D I := max_eq_left hloR
    rw [h2]
    simp [loR, T_relu, h1]
  · have hlt : I.lo < 0 := lt_of_not_ge h
    have hloR : loR D I ≤ 0 := by
      unfold loR
      exact div_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast le_of_lt hlt)
        (le_of_lt (DposR D))
    have h1 : max I.lo 0 = 0 := max_eq_right (le_of_lt hlt)
    have h2 : max (loR D I) 0 = 0 := max_eq_right hloR
    rw [h2]
    simp [loR, T_relu, h1]

lemma hiR_T_relu (D : DPos) (I : IEnc D) :
    hiR D (T_relu D I) = max (hiR D I) 0 := by
  by_cases h : 0 ≤ I.hi
  · have hhiR : 0 ≤ hiR D I := by
      unfold hiR
      exact div_nonneg (by exact_mod_cast h) (le_of_lt (DposR D))
    have h1 : max I.hi 0 = I.hi := max_eq_left h
    have h2 : max (hiR D I) 0 = hiR D I := max_eq_left hhiR
    rw [h2]
    simp [hiR, T_relu, h1]
  · have hlt : I.hi < 0 := lt_of_not_ge h
    have hhiR : hiR D I ≤ 0 := by
      unfold hiR
      exact div_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast le_of_lt hlt)
        (le_of_lt (DposR D))
    have h1 : max I.hi 0 = 0 := max_eq_right (le_of_lt hlt)
    have h2 : max (hiR D I) 0 = 0 := max_eq_right hhiR
    rw [h2]
    simp [hiR, T_relu, h1]

theorem rsound_relu (D : DPos) (I : IEnc D) :
    ∀ {x : ℝ}, x ∈ γset D I → relu x ∈ γset D (T_relu D I) := by
  intro x hx
  rcases hx with ⟨hxL, hxU⟩
  refine ⟨?_, ?_⟩
  · have h : max (loR D I) 0 ≤ max x 0 := max_le_max hxL le_rfl
    simpa [relu, γset, loR_T_relu] using h
  · have h : max x 0 ≤ max (hiR D I) 0 := max_le_max hxU le_rfl
    simpa [relu, γset, hiR_T_relu] using h

-- ---------------------------------------------------------------------------
-- Multiplication: helper bounds on rectangles (vertex extrema).
-- ---------------------------------------------------------------------------

/-- Corner products (in ℝ). -/
def p1 (a _b c _d : ℝ) : ℝ := a * c
def p2 (a _b _c d : ℝ) : ℝ := a * d
def p3 (_a b c _d : ℝ) : ℝ := b * c
def p4 (_a b _c d : ℝ) : ℝ := b * d

def min4 (a b c d : ℝ) : ℝ := min (min (p1 a b c d) (p2 a b c d)) (min (p3 a b c d) (p4 a b c d))
def max4 (a b c d : ℝ) : ℝ := max (max (p1 a b c d) (p2 a b c d)) (max (p3 a b c d) (p4 a b c d))

/-- If `x ∈ Icc a b` and `y ∈ Icc c d`, then `x*y` is between the min and max of corner products. -/
lemma mul_bounds4 {a b c d x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    min4 a b c d ≤ x * y ∧ x * y ≤ max4 a b c d := by
  have hxy : min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) :=
    mul_fixed_right_bounds (a := a) (b := b) (x := x) (y := y) hx
  have hay : min (a * c) (a * d) ≤ a * y ∧ a * y ≤ max (a * c) (a * d) :=
    mul_fixed_left_bounds (c := c) (d := d) (x := a) (y := y) hy
  have hby : min (b * c) (b * d) ≤ b * y ∧ b * y ≤ max (b * c) (b * d) :=
    mul_fixed_left_bounds (c := c) (d := d) (x := b) (y := y) hy
  have hmidL : min4 a b c d ≤ min (a * y) (b * y) := by
    unfold min4 p1 p2 p3 p4
    refine le_min ?_ ?_
    · exact le_trans (min_le_left _ _) hay.1
    · exact le_trans (min_le_right _ _) hby.1
  have hmidU : max (a * y) (b * y) ≤ max4 a b c d := by
    unfold max4 p1 p2 p3 p4
    refine max_le ?_ ?_
    · exact le_trans hay.2 (le_max_left _ _)
    · exact le_trans hby.2 (le_max_right _ _)
  exact ⟨le_trans hmidL hxy.1, le_trans hxy.2 hmidU⟩

-- ---------------------------------------------------------------------------
-- Multiplication: witness + R-SOUND
-- ---------------------------------------------------------------------------

structure WMul where
  pmin : ℤ
  pmax : ℤ
  qf   : ℤ
  qc   : ℤ

def CheckMin (pmin p1 p2 p3 p4 : ℤ) : Prop :=
  (pmin = p1 ∨ pmin = p2 ∨ pmin = p3 ∨ pmin = p4) ∧
  pmin ≤ p1 ∧ pmin ≤ p2 ∧ pmin ≤ p3 ∧ pmin ≤ p4

def CheckMax (pmax p1 p2 p3 p4 : ℤ) : Prop :=
  (pmax = p1 ∨ pmax = p2 ∨ pmax = p3 ∨ pmax = p4) ∧
  p1 ≤ pmax ∧ p2 ≤ pmax ∧ p3 ≤ pmax ∧ p4 ≤ pmax

def CheckMul (D : DPos) (I J : IEnc D) (W : WMul) : Prop :=
  let a := I.lo; let b := I.hi; let c := J.lo; let d := J.hi
  let p1 := a*c; let p2 := a*d; let p3 := b*c; let p4 := b*d
  CheckMin W.pmin p1 p2 p3 p4 ∧
  CheckMax W.pmax p1 p2 p3 p4 ∧
  CheckFDIV W.pmin ((D : ℕ) : ℤ) W.qf ∧
  CheckCDIV W.pmax ((D : ℕ) : ℤ) W.qc

/-- Closedness (qf ≤ qc) derived from `CheckMul`. -/
lemma rsound_mul_closed (D : DPos) (I J : IEnc D) (W : WMul) (hW : CheckMul D I J W) :
    W.qf ≤ W.qc := by
  have hDposR : (0:ℝ) < (D : ℕ) := DposR D
  -- unpack checks
  rcases hW with ⟨hmin, hmax, hfdiv, hcdiv⟩
  -- get pmin ≤ pmax by chaining through any corner (use p1)
  have hpmin_le_p1 : W.pmin ≤ I.lo * J.lo := hmin.2.1
  have hp1_le_pmax : I.lo * J.lo ≤ W.pmax := hmax.2.1
  have hpmin_le_pmax : W.pmin ≤ W.pmax := le_trans hpmin_le_p1 hp1_le_pmax
  -- FDIV: qf ≤ pmin/D
  have hf :
      ((W.qf : ℝ) ≤ (W.pmin : ℝ) / (((D : ℕ) : ℤ) : ℝ)) := by
    exact (fdiv_bound W.pmin ((D : ℕ) : ℤ) W.qf hfdiv).1
  have hc :
      ((W.pmax : ℝ) / (((D : ℕ) : ℤ) : ℝ) ≤ (W.qc : ℝ)) := by
    exact (cdiv_bound W.pmax ((D : ℕ) : ℤ) W.qc hcdiv).2
  have hpm : (W.pmin : ℝ) / (((D : ℕ) : ℤ) : ℝ) ≤ (W.pmax : ℝ) / (((D : ℕ) : ℤ) : ℝ) := by
    have hDpos : (0:ℝ) < (((D : ℕ) : ℤ) : ℝ) := by exact_mod_cast hDposR
    exact div_le_div_of_nonneg_right (by exact_mod_cast hpmin_le_pmax) (le_of_lt hDpos)
  -- chain
  have : (W.qf : ℝ) ≤ (W.qc : ℝ) := le_trans hf (le_trans hpm hc)
  exact_mod_cast this


/-- Soundness for multiplication, witness-based. -/
theorem rsound_mul (D : DPos) (I J : IEnc D) (W : WMul) (hW : CheckMul D I J W) :
    ∀ {x y : ℝ}, x ∈ γset D I → y ∈ γset D J →
      (x * y) ∈ γset D ⟨W.qf, W.qc, rsound_mul_closed D I J W hW⟩ := by
  intro x y hx hy
  rcases hW with ⟨hmin, hmax, hfdiv, hcdiv⟩
  let Dz : ℝ := (D : ℕ)
  let X : ℝ := Dz * x
  let Y : ℝ := Dz * y
  have hDzpos : (0 : ℝ) < Dz := DposR D
  have hDznonneg : (0 : ℝ) ≤ Dz := le_of_lt hDzpos
  have hX : X ∈ Icc (I.lo : ℝ) (I.hi : ℝ) := by
    simpa [X, Dz] using (scale_mem_Icc_of_mem_γ (D := D) (I := I) hx)
  have hY : Y ∈ Icc (J.lo : ℝ) (J.hi : ℝ) := by
    simpa [Y, Dz] using (scale_mem_Icc_of_mem_γ (D := D) (I := J) hy)
  have hXY :
      min4 (I.lo : ℝ) (I.hi : ℝ) (J.lo : ℝ) (J.hi : ℝ) ≤ X * Y
        ∧ X * Y ≤ max4 (I.lo : ℝ) (I.hi : ℝ) (J.lo : ℝ) (J.hi : ℝ) :=
    mul_bounds4 hX hY
  have hp1 : (W.pmin : ℝ) ≤ (I.lo : ℝ) * (J.lo : ℝ) := by
    exact_mod_cast hmin.2.1
  have hp2 : (W.pmin : ℝ) ≤ (I.lo : ℝ) * (J.hi : ℝ) := by
    exact_mod_cast hmin.2.2.1
  have hp3 : (W.pmin : ℝ) ≤ (I.hi : ℝ) * (J.lo : ℝ) := by
    exact_mod_cast hmin.2.2.2.1
  have hp4 : (W.pmin : ℝ) ≤ (I.hi : ℝ) * (J.hi : ℝ) := by
    exact_mod_cast hmin.2.2.2.2
  have hpmin_le :
      (W.pmin : ℝ) ≤ min4 (I.lo : ℝ) (I.hi : ℝ) (J.lo : ℝ) (J.hi : ℝ) := by
    unfold min4 p1 p2 p3 p4
    exact le_min (le_min hp1 hp2) (le_min hp3 hp4)
  have hq1 : (I.lo : ℝ) * (J.lo : ℝ) ≤ (W.pmax : ℝ) := by
    exact_mod_cast hmax.2.1
  have hq2 : (I.lo : ℝ) * (J.hi : ℝ) ≤ (W.pmax : ℝ) := by
    exact_mod_cast hmax.2.2.1
  have hq3 : (I.hi : ℝ) * (J.lo : ℝ) ≤ (W.pmax : ℝ) := by
    exact_mod_cast hmax.2.2.2.1
  have hq4 : (I.hi : ℝ) * (J.hi : ℝ) ≤ (W.pmax : ℝ) := by
    exact_mod_cast hmax.2.2.2.2
  have hpmax_ge :
      max4 (I.lo : ℝ) (I.hi : ℝ) (J.lo : ℝ) (J.hi : ℝ) ≤ (W.pmax : ℝ) := by
    unfold max4 p1 p2 p3 p4
    exact max_le (max_le hq1 hq2) (max_le hq3 hq4)
  have hlowXY : (W.pmin : ℝ) ≤ X * Y := le_trans hpmin_le hXY.1
  have hhighXY : X * Y ≤ (W.pmax : ℝ) := le_trans hXY.2 hpmax_ge
  have hf : (W.qf : ℝ) ≤ (W.pmin : ℝ) / Dz := by
    simpa [Dz] using (fdiv_bound W.pmin ((D : ℕ) : ℤ) W.qf hfdiv).1
  have hc : (W.pmax : ℝ) / Dz ≤ (W.qc : ℝ) := by
    simpa [Dz] using (cdiv_bound W.pmax ((D : ℕ) : ℤ) W.qc hcdiv).2
  have hqf : (W.qf : ℝ) ≤ (X * Y) / Dz := by
    have hdiv : (W.pmin : ℝ) / Dz ≤ (X * Y) / Dz :=
      div_le_div_of_nonneg_right hlowXY hDznonneg
    exact le_trans hf hdiv
  have hqc : (X * Y) / Dz ≤ (W.qc : ℝ) := by
    have hdiv : (X * Y) / Dz ≤ (W.pmax : ℝ) / Dz :=
      div_le_div_of_nonneg_right hhighXY hDznonneg
    exact le_trans hdiv hc
  have hxy_scaled : (X * Y) / Dz = Dz * (x * y) := by
    dsimp [X, Y, Dz]
    field_simp [Dne0R D]
  refine ⟨?_, ?_⟩
  · have hscaled : (W.qf : ℝ) ≤ (x * y) * Dz := by
      simpa [hxy_scaled, mul_assoc, mul_left_comm, mul_comm] using hqf
    have : (W.qf : ℝ) / Dz ≤ x * y :=
      Division.div_le_of_le_mul_pos hDzpos hscaled
    simpa [γset, loR, hiR, Dz] using this
  · have hscaled : (x * y) * Dz ≤ (W.qc : ℝ) := by
      simpa [hxy_scaled, mul_assoc, mul_left_comm, mul_comm] using hqc
    have : x * y ≤ (W.qc : ℝ) / Dz :=
      Division.le_div_of_mul_le_pos hDzpos hscaled
    simpa [γset, loR, hiR, Dz] using this

-- ---------------------------------------------------------------------------
-- Inversion: witness + R-SOUND
-- ---------------------------------------------------------------------------


lemma inv_bounds_pos {l u x : ℝ}
    (hl : 0 < l) (hlx : l ≤ x) (hxu : x ≤ u) :
    1 / u ≤ 1 / x ∧ 1 / x ≤ 1 / l := by
  have hxpos : 0 < x := lt_of_lt_of_le hl hlx
  exact ⟨one_div_le_one_div_of_le hxpos hxu, one_div_le_one_div_of_le hl hlx⟩

lemma inv_bounds_neg {l u x : ℝ}
    (hlx : l ≤ x) (hxu : x ≤ u) (hu : u < 0) :
    1 / u ≤ 1 / x ∧ 1 / x ≤ 1 / l := by
  have hxneg : x < 0 := lt_of_le_of_lt hxu hu
  exact ⟨one_div_le_one_div_of_neg_of_le hu hxu, one_div_le_one_div_of_neg_of_le hxneg hlx⟩

structure WInv where
  ql : ℤ
  qu : ℤ

def DomInv (D : DPos) (I : IEnc D) : Prop :=
  (0 < I.lo) ∨ (I.hi < 0)

def CheckInv (D : DPos) (I : IEnc D) (W : WInv) : Prop :=
  DomInv D I ∧
  CheckFDIV (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.hi W.ql ∧
  CheckCDIV (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.lo W.qu


lemma rsound_inv_closed (D : DPos) (I : IEnc D) (W : WInv) (hW : CheckInv D I W) :
    W.ql ≤ W.qu := by
  rcases hW with ⟨hdom, hfdiv, hcdiv⟩
  have hD2pos : (0 : ℝ) < ((D : ℕ) : ℝ) ^ 2 := by positivity
  have hlohi : (I.lo : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast I.h
  have hL : (W.ql : ℝ) ≤ (((D : ℕ) : ℝ) ^ 2) / (I.hi : ℝ) := by
    simpa [pow_two] using
      (fdiv_bound (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.hi W.ql hfdiv).1
  have hU : (((D : ℕ) : ℝ) ^ 2) / (I.lo : ℝ) ≤ (W.qu : ℝ) := by
    simpa [pow_two] using
      (cdiv_bound (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.lo W.qu hcdiv).2
  have hmid : (((D : ℕ) : ℝ) ^ 2) / (I.hi : ℝ) ≤ (((D : ℕ) : ℝ) ^ 2) / (I.lo : ℝ) := by
    rcases hdom with hpos | hneg
    · have hlo : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hpos
      have hrec : 1 / (I.hi : ℝ) ≤ 1 / (I.lo : ℝ) :=
        (inv_bounds_pos (x := (I.lo : ℝ)) hlo le_rfl hlohi).1
      have : (((D : ℕ) : ℝ) ^ 2) * (1 / (I.hi : ℝ))
          ≤ (((D : ℕ) : ℝ) ^ 2) * (1 / (I.lo : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hrec (le_of_lt hD2pos)
      simpa [div_eq_mul_inv] using this
    · have hhi : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
      have hrec : 1 / (I.hi : ℝ) ≤ 1 / (I.lo : ℝ) :=
        (inv_bounds_neg (x := (I.hi : ℝ)) hlohi le_rfl hhi).2
      have : (((D : ℕ) : ℝ) ^ 2) * (1 / (I.hi : ℝ))
          ≤ (((D : ℕ) : ℝ) ^ 2) * (1 / (I.lo : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hrec (le_of_lt hD2pos)
      simpa [div_eq_mul_inv] using this
  have : (W.ql : ℝ) ≤ (W.qu : ℝ) := le_trans hL (le_trans hmid hU)
  exact_mod_cast this

theorem rsound_inv (D : DPos) (I : IEnc D) (W : WInv) (hW : CheckInv D I W) :
    ∀ {x : ℝ}, x ∈ γset D I → (1 / x) ∈ γset D ⟨W.ql, W.qu, rsound_inv_closed D I W hW⟩ := by
  intro x hx
  rcases hx with ⟨hxL, hxU⟩
  rcases hW with ⟨hdom, hfdiv, hcdiv⟩
  have hDpos : (0 : ℝ) < (D : ℕ) := DposR D
  have hDnonneg : (0 : ℝ) ≤ (D : ℕ) := le_of_lt hDpos
  have hL0 : (W.ql : ℝ) ≤ (((D : ℕ) : ℝ) ^ 2) / (I.hi : ℝ) := by
    simpa [pow_two] using
      (fdiv_bound (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.hi W.ql hfdiv).1
  have hU0 : (((D : ℕ) : ℝ) ^ 2) / (I.lo : ℝ) ≤ (W.qu : ℝ) := by
    simpa [pow_two] using
      (cdiv_bound (((D : ℕ) : ℤ) * ((D : ℕ) : ℤ)) I.lo W.qu hcdiv).2
  have hhi_ne : (I.hi : ℝ) ≠ 0 := by
    rcases hdom with hpos | hneg
    · have hlo_pos : (0 : ℝ) < (I.lo : ℝ) := by
        exact_mod_cast hpos
      have hlohiR : (I.lo : ℝ) ≤ (I.hi : ℝ) := by
        exact_mod_cast I.h
      have hhi_pos : (0 : ℝ) < (I.hi : ℝ) := by
        exact lt_of_lt_of_le hlo_pos hlohiR
      exact ne_of_gt hhi_pos
    · have hnegR : (I.hi : ℝ) < 0 := by
        exact_mod_cast hneg
      exact ne_of_lt hnegR
  have hlo_ne : (I.lo : ℝ) ≠ 0 := by
    rcases hdom with hpos | hneg
    · have hposR : (0 : ℝ) < (I.lo : ℝ) := by
        exact_mod_cast hpos
      exact ne_of_gt hposR
    · have hlohiR : (I.lo : ℝ) ≤ (I.hi : ℝ) := by
        exact_mod_cast I.h
      have hnegR : (I.hi : ℝ) < 0 := by
        exact_mod_cast hneg
      have hlo_neg : (I.lo : ℝ) < 0 := by
        exact lt_of_le_of_lt hlohiR hnegR
      exact ne_of_lt hlo_neg
  have hL : (W.ql : ℝ) / (D : ℕ) ≤ ((D : ℕ) : ℝ) / (I.hi : ℝ) := by
    have htmp :
        (W.ql : ℝ) / (D : ℕ) ≤ ((((D : ℕ) : ℝ) ^ 2) / (I.hi : ℝ)) / (D : ℕ) := by
      exact div_le_div_of_nonneg_right hL0 hDnonneg
    have hEq :
        ((((D : ℕ) : ℝ) ^ 2) / (I.hi : ℝ)) / (D : ℕ) = ((D : ℕ) : ℝ) / (I.hi : ℝ) := by
      field_simp [Dne0R D, hhi_ne]
    rw [hEq] at htmp
    exact htmp
  have hU : ((D : ℕ) : ℝ) / (I.lo : ℝ) ≤ (W.qu : ℝ) / (D : ℕ) := by
    have htmp :
        ((((D : ℕ) : ℝ) ^ 2) / (I.lo : ℝ)) / (D : ℕ) ≤ (W.qu : ℝ) / (D : ℕ) := by
      exact div_le_div_of_nonneg_right hU0 hDnonneg
    have hEq :
        ((((D : ℕ) : ℝ) ^ 2) / (I.lo : ℝ)) / (D : ℕ) = ((D : ℕ) : ℝ) / (I.lo : ℝ) := by
      field_simp [Dne0R D, hlo_ne]
    rw [hEq] at htmp
    exact htmp
  have hhi_eq : ((D : ℕ) : ℝ) / (I.hi : ℝ) = 1 / (hiR D I) := by
    unfold hiR
    field_simp [Dne0R D, hhi_ne]
  have hlo_eq : ((D : ℕ) : ℝ) / (I.lo : ℝ) = 1 / (loR D I) := by
    unfold loR
    field_simp [Dne0R D, hlo_ne]
  have hrec : 1 / (hiR D I) ≤ 1 / x ∧ 1 / x ≤ 1 / (loR D I) := by
    rcases hdom with hpos | hneg
    · have hlo_pos : (0 : ℝ) < loR D I := by
        have : (0 : ℝ) < (I.lo : ℝ) := by
          exact_mod_cast hpos
        exact div_pos this hDpos
      exact inv_bounds_pos hlo_pos hxL hxU
    · have hhi_neg : hiR D I < 0 := by
        have : (I.hi : ℝ) < 0 := by
          exact_mod_cast hneg
        exact div_neg_of_neg_of_pos this hDpos
      exact inv_bounds_neg hxL hxU hhi_neg
  refine ⟨?_, ?_⟩
  · have : (W.ql : ℝ) / (D : ℕ) ≤ 1 / x := by
      exact le_trans (by simpa [hhi_eq] using hL) hrec.1
    simpa [γset, loR, hiR] using this
  · have : 1 / x ≤ (W.qu : ℝ) / (D : ℕ) := by
      exact le_trans hrec.2 (by simpa [hlo_eq] using hU)
    simpa [γset, loR, hiR] using this

-- ---------------------------------------------------------------------------
-- Sqrt: witness + R-SOUND
-- ---------------------------------------------------------------------------

structure WSqrt where
  p : ℤ
  q : ℤ

def DomSqrt (D : DPos) (I : IEnc D) : Prop :=
  (0 : ℤ) ≤ I.lo

def CheckSqrt (D : DPos) (I : IEnc D) (W : WSqrt) : Prop :=
  DomSqrt D I ∧
  (0 : ℤ) ≤ W.p ∧
  (0 : ℤ) ≤ W.q ∧
  (W.p * W.p) ≤ (I.lo * ((D : ℕ) : ℤ)) ∧
  (I.hi * ((D : ℕ) : ℤ)) ≤ (W.q * W.q)


lemma rsound_sqrt_closed (D : DPos) (I : IEnc D) (W : WSqrt) (hW : CheckSqrt D I W) :
    W.p ≤ W.q := by
  rcases hW with ⟨hdom, hp0, hq0, hp2, hq2⟩
  have hp2R : (W.p : ℝ) ^ 2 ≤ (I.lo : ℝ) * (D : ℕ) := by
    have : (((W.p * W.p : ℤ) : ℝ)) ≤ (((I.lo * ((D : ℕ) : ℤ) : ℤ) : ℝ)) := by
      exact_mod_cast hp2
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hq2R : (I.hi : ℝ) * (D : ℕ) ≤ (W.q : ℝ) ^ 2 := by
    have : (((I.hi * ((D : ℕ) : ℤ) : ℤ) : ℝ)) ≤ (((W.q * W.q : ℤ) : ℝ)) := by
      exact_mod_cast hq2
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hlohi : (I.lo : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast I.h
  have hlohiD : (I.lo : ℝ) * (D : ℕ) ≤ (I.hi : ℝ) * (D : ℕ) := by
    exact mul_le_mul_of_nonneg_right hlohi (le_of_lt (DposR D))
  have hpq : (W.p : ℝ) ^ 2 ≤ (W.q : ℝ) ^ 2 := le_trans hp2R (le_trans hlohiD hq2R)
  have hp0R : (0 : ℝ) ≤ (W.p : ℝ) := by exact_mod_cast hp0
  have hq0R : (0 : ℝ) ≤ (W.q : ℝ) := by exact_mod_cast hq0
  have habs : |(W.p : ℝ)| ≤ |(W.q : ℝ)| := (sq_le_sq).mp hpq
  have : (W.p : ℝ) ≤ (W.q : ℝ) := by
    simpa [abs_of_nonneg hp0R, abs_of_nonneg hq0R] using habs
  exact_mod_cast this

theorem rsound_sqrt (D : DPos) (I : IEnc D) (W : WSqrt) (hW : CheckSqrt D I W) :
    ∀ {x : ℝ}, x ∈ γset D I → (Real.sqrt x) ∈ γset D ⟨W.p, W.q, rsound_sqrt_closed D I W hW⟩ := by
  intro x hx
  rcases hx with ⟨hxL, hxU⟩
  rcases hW with ⟨hdom, hp0, hq0, hp2, hq2⟩
  have hDpos : (0 : ℝ) < (D : ℕ) := DposR D
  have hIlo_nonneg : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hdom
  have hlo0 : (0 : ℝ) ≤ loR D I := by
    exact div_nonneg hIlo_nonneg (le_of_lt hDpos)
  have hx0 : (0 : ℝ) ≤ x := le_trans hlo0 hxL
  have hp2R : (W.p : ℝ) ^ 2 ≤ (I.lo : ℝ) * (D : ℕ) := by
    have : (((W.p * W.p : ℤ) : ℝ)) ≤ (((I.lo * ((D : ℕ) : ℤ) : ℤ) : ℝ)) := by
      exact_mod_cast hp2
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hq2R : (I.hi : ℝ) * (D : ℕ) ≤ (W.q : ℝ) ^ 2 := by
    have : (((I.hi * ((D : ℕ) : ℤ) : ℤ) : ℝ)) ≤ (((W.q * W.q : ℤ) : ℝ)) := by
      exact_mod_cast hq2
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  have hp_sq_lo : ((W.p : ℝ) / (D : ℕ)) ^ 2 ≤ loR D I := by
    unfold loR
    exact div_pow_two_le_of_sq_le_mul (D := (D : ℕ)) hDpos hp2R
  have hq_sq_hi : hiR D I ≤ ((W.q : ℝ) / (D : ℕ)) ^ 2 := by
    unfold hiR
    exact le_div_pow_two_of_mul_le_sq (D := (D : ℕ)) hDpos hq2R
  have hp_sq : ((W.p : ℝ) / (D : ℕ)) ^ 2 ≤ x := le_trans hp_sq_lo hxL
  have hq_sq : x ≤ ((W.q : ℝ) / (D : ℕ)) ^ 2 := le_trans hxU hq_sq_hi
  have hp_nonneg : (0 : ℝ) ≤ (W.p : ℝ) / (D : ℕ) := by
    exact div_nonneg (by exact_mod_cast hp0) (le_of_lt hDpos)
  have hq_nonneg : (0 : ℝ) ≤ (W.q : ℝ) / (D : ℕ) := by
    exact div_nonneg (by exact_mod_cast hq0) (le_of_lt hDpos)
  have hp_le : (W.p : ℝ) / (D : ℕ) ≤ Real.sqrt x := by
    exact Real.le_sqrt_of_sq_le hp_sq
  have hq_ge : Real.sqrt x ≤ (W.q : ℝ) / (D : ℕ) := by
    exact (Real.sqrt_le_iff).2 ⟨hq_nonneg, by simpa [pow_two] using hq_sq⟩
  refine ⟨?_, ?_⟩
  · simpa [γset, loR, hiR] using hp_le
  · simpa [γset, loR, hiR] using hq_ge

end Primitives

/-!
Section: ReplayCore

This section connects primitive R-SOUND to certificate replay soundness.

Core chain:
  verifier acceptance
  -> program replay enclosure
  -> specification replay enclosure
  -> root upper-bound soundness
  -> real-valued semantic validity
-/

namespace ReplayCore

set_option linter.style.emptyLine false
set_option linter.unusedSimpArgs false

local instance instDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

open Primitives

open Primitives

abbrev IEnv (D : DPos) := List (IEnc D)
abbrev REnv := List ℝ
abbrev InputOracle := Nat → ℝ

universe u

def listGetOpt {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOpt xs n

lemma listGetOpt_eq_some_length {α : Type u} {xs : List α} {n : Nat} {x : α} :
    listGetOpt xs n = some x → n < xs.length := by
  induction xs generalizing n with
  | nil =>
      cases n <;> intro h <;> simp [listGetOpt] at h
  | cons a xs ih =>
      cases n with
      | zero =>
          intro h
          simp
      | succ n =>
          intro h
          simp only [List.length_cons, Order.lt_add_one_iff, Order.add_one_le_iff]
          exact ih h

lemma listGetOpt_exists_of_lt {α : Type u} (xs : List α) {n : Nat} :
    n < xs.length → ∃ x, listGetOpt xs n = some x := by
  induction xs generalizing n with
  | nil =>
      intro h
      cases h
  | cons a xs ih =>
      cases n with
      | zero =>
          intro h
          exact ⟨a, rfl⟩
      | succ n =>
          intro h
          exact ih (Nat.succ_lt_succ_iff.mp h)

lemma listGetOpt_append_singleton_eq_some {α : Type u}
    {xs : List α} {a : α} {n : Nat} {z : α} :
    listGetOpt (xs ++ [a]) n = some z →
    (listGetOpt xs n = some z) ∨ (n = xs.length ∧ z = a) := by
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero =>
          intro h
          right
          simp [listGetOpt] at h
          exact ⟨rfl, h.symm⟩
      | succ n =>
          intro h
          simp [listGetOpt] at h
  | cons x xs ih =>
      cases n with
      | zero =>
          intro h
          left
          simp [listGetOpt] at h
          simp [listGetOpt, h.symm]
      | succ n =>
          intro h
          simp [listGetOpt] at h
          rcases ih h with hOld | hLast
          · left
            simpa [listGetOpt] using hOld
          · right
            rcases hLast with ⟨hn, hz⟩
            exact ⟨by simp [hn], hz⟩

def IBoundsEq {D : DPos} (I J : IEnc D) : Prop :=
  I.lo = J.lo ∧ I.hi = J.hi

lemma IBoundsEq_refl {D : DPos} (I : IEnc D) :
    IBoundsEq I I := by
  exact ⟨rfl, rfl⟩

lemma IBoundsEq_symm {D : DPos} {I J : IEnc D} :
    IBoundsEq I J → IBoundsEq J I := by
  intro h
  exact ⟨h.1.symm, h.2.symm⟩

lemma IBoundsEq_trans {D : DPos} {I J K : IEnc D} :
    IBoundsEq I J → IBoundsEq J K → IBoundsEq I K := by
  intro hIJ hJK
  exact ⟨hIJ.1.trans hJK.1, hIJ.2.trans hJK.2⟩

def ISingleton (D : DPos) (k : ℤ) : IEnc D :=
  ⟨k, k, le_rfl⟩

lemma mem_gamma_transfer {D : DPos} {I J : IEnc D} {x : ℝ} :
    IBoundsEq I J →
    x ∈ Primitives.γset D I →
    x ∈ Primitives.γset D J := by
  intro h hx
  rcases h with ⟨hlo, hhi⟩
  rcases hx with ⟨hxlo, hxhi⟩
  constructor
  · simpa [Primitives.γset, Primitives.loR, hlo] using hxlo
  · simpa [Primitives.γset, Primitives.hiR, hhi] using hxhi

lemma mem_gamma_transfer_symm {D : DPos} {I J : IEnc D} {x : ℝ} :
    IBoundsEq I J →
    x ∈ Primitives.γset D J →
    x ∈ Primitives.γset D I := by
  intro h hx
  exact mem_gamma_transfer (IBoundsEq_symm h) hx

lemma singleton_contains (D : DPos) (k : ℤ) :
    ((k : ℝ) / (D : ℕ)) ∈ Primitives.γset D (ISingleton D k) := by
  constructor <;> simp [Primitives.γset, Primitives.loR, Primitives.hiR, ISingleton]

def EnvSound (D : DPos) (ienv : IEnv D) (renv : REnv) : Prop :=
  ienv.length = renv.length ∧
  ∀ n I x,
    listGetOpt ienv n = some I →
    listGetOpt renv n = some x →
    x ∈ Primitives.γset D I

lemma EnvSound_get {D : DPos}
    {ienv : IEnv D} {renv : REnv}
    (h : EnvSound D ienv renv)
    {n : Nat} {I : IEnc D} {x : ℝ} :
    listGetOpt ienv n = some I →
    listGetOpt renv n = some x →
    x ∈ Primitives.γset D I := by
  exact h.2 n I x

lemma EnvSound_real_exists_of_interval {D : DPos}
    {ienv : IEnv D} {renv : REnv}
    (h : EnvSound D ienv renv)
    {n : Nat} {I : IEnc D} :
    listGetOpt ienv n = some I →
    ∃ x, listGetOpt renv n = some x := by
  intro hI
  have hnI : n < ienv.length := listGetOpt_eq_some_length hI
  have hnR : n < renv.length := by
    simpa [h.1] using hnI
  exact listGetOpt_exists_of_lt renv hnR

lemma EnvSound_append {D : DPos}
    {ienv : IEnv D} {renv : REnv}
    {I : IEnc D} {x : ℝ} :
    EnvSound D ienv renv →
    x ∈ Primitives.γset D I →
    EnvSound D (ienv ++ [I]) (renv ++ [x]) := by
  intro hEnv hx
  constructor
  · simp [hEnv.1]
  · intro n J y hJ hy
    rcases listGetOpt_append_singleton_eq_some hJ with hJold | hJlast
    · rcases listGetOpt_append_singleton_eq_some hy with hyold | hylast
      · exact hEnv.2 n J y hJold hyold
      · rcases hylast with ⟨hn, hyx⟩
        have hnI : n < ienv.length := listGetOpt_eq_some_length hJold
        have : n < renv.length := by simpa [hEnv.1] using hnI
        rw [hn] at this
        exact False.elim (Nat.lt_irrefl _ this)
    · rcases listGetOpt_append_singleton_eq_some hy with hyold | hylast
      · rcases hJlast with ⟨hn, hJI⟩
        have hnR : n < renv.length := listGetOpt_eq_some_length hyold
        have : n < ienv.length := by simpa [hEnv.1] using hnR
        rw [hn] at this
        exact False.elim (Nat.lt_irrefl _ this)
      · rcases hJlast with ⟨_, hJI⟩
        rcases hylast with ⟨_, hyx⟩
        simpa [hJI, hyx] using hx

inductive ProgRow (D : DPos) : Type
  | input : Nat → IEnc D → ProgRow D
  | const : ℤ → ProgRow D
  | add   : Nat → Nat → IEnc D → ProgRow D
  | sub   : Nat → Nat → IEnc D → ProgRow D
  | mul   : Nat → Nat → Primitives.WMul → IEnc D → ProgRow D
  | inv   : Nat → Primitives.WInv → IEnc D → ProgRow D
  | sqrt  : Nat → Primitives.WSqrt → IEnc D → ProgRow D
  | relu  : Nat → IEnc D → ProgRow D

/-- Program-row dependency well-formedness.
A program row may reference only values already produced earlier. -/
def ProgRowRefsOK {D : DPos} (n : Nat) : ProgRow D → Prop
  | ProgRow.input _ _ => True
  | ProgRow.const _ => True
  | ProgRow.add i j _ => i < n ∧ j < n
  | ProgRow.sub i j _ => i < n ∧ j < n
  | ProgRow.mul i j _ _ => i < n ∧ j < n
  | ProgRow.inv i _ _ => i < n
  | ProgRow.sqrt i _ _ => i < n
  | ProgRow.relu i _ => i < n

/-- Topological well-formedness for program rows. -/
def ProgRowsRefsOK {D : DPos} : Nat → List (ProgRow D) → Prop
  | _, [] => True
  | n, row :: rows =>
      ProgRowRefsOK n row ∧ ProgRowsRefsOK (D := D) (n + 1) rows

def ProgRowsTopological (D : DPos) (rows : List (ProgRow D)) : Prop :=
  ProgRowsRefsOK (D := D) 0 rows

def RowInputAdmissible (D : DPos) (u : InputOracle) : ProgRow D → Prop
  | ProgRow.input q I => u q ∈ Primitives.γset D I
  | _ => True

def RowsInputAdmissible (D : DPos) (u : InputOracle) (rows : List (ProgRow D)) : Prop :=
  ∀ row ∈ rows, RowInputAdmissible D u row

def ReplayRow (D : DPos) (ienv : IEnv D) : ProgRow D → IEnc D → Prop
  | ProgRow.input _ I, Iout =>
      IBoundsEq Iout I

  | ProgRow.const k, Iout =>
      IBoundsEq Iout (ISingleton D k)

  | ProgRow.add i j Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt ienv i = some A ∧
        listGetOpt ienv j = some B ∧
        IBoundsEq Icert (Primitives.T_add D A B)

  | ProgRow.sub i j Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt ienv i = some A ∧
        listGetOpt ienv j = some B ∧
        IBoundsEq Icert (Primitives.T_sub D A B)

  | ProgRow.mul i j W Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt ienv i = some A ∧
        listGetOpt ienv j = some B ∧
        Primitives.CheckMul D A B W ∧
        Icert.lo = W.qf ∧
        Icert.hi = W.qc

  | ProgRow.inv i W Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A,
        listGetOpt ienv i = some A ∧
        Primitives.CheckInv D A W ∧
        Icert.lo = W.ql ∧
        Icert.hi = W.qu

  | ProgRow.sqrt i W Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A,
        listGetOpt ienv i = some A ∧
        Primitives.CheckSqrt D A W ∧
        Icert.lo = W.p ∧
        Icert.hi = W.q

  | ProgRow.relu i Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A,
        listGetOpt ienv i = some A ∧
        IBoundsEq Icert (Primitives.T_relu D A)

def EvalRow (D : DPos) (u : InputOracle) (renv : REnv) :
    ProgRow D → ℝ → Prop
  | ProgRow.input q _, x =>
      x = u q

  | ProgRow.const k, x =>
      x = (k : ℝ) / (D : ℕ)

  | ProgRow.add i j _, x =>
      ∃ a b,
        listGetOpt renv i = some a ∧
        listGetOpt renv j = some b ∧
        x = a + b

  | ProgRow.sub i j _, x =>
      ∃ a b,
        listGetOpt renv i = some a ∧
        listGetOpt renv j = some b ∧
        x = a - b

  | ProgRow.mul i j _ _, x =>
      ∃ a b,
        listGetOpt renv i = some a ∧
        listGetOpt renv j = some b ∧
        x = a * b

  | ProgRow.inv i _ _, x =>
      ∃ a,
        listGetOpt renv i = some a ∧
        a ≠ 0 ∧
        x = 1 / a

  | ProgRow.sqrt i _ _, x =>
      ∃ a,
        listGetOpt renv i = some a ∧
        0 ≤ a ∧
        x = Real.sqrt a

  | ProgRow.relu i _, x =>
      ∃ a,
        listGetOpt renv i = some a ∧
        x = Primitives.relu a

lemma CheckInv_real_domain {D : DPos}
    {I : IEnc D} {W : Primitives.WInv} {x : ℝ} :
    Primitives.CheckInv D I W →
    x ∈ Primitives.γset D I →
    x ≠ 0 := by
  intro hW hx
  rcases hW with ⟨hdom, _, _⟩
  rcases hx with ⟨hxL, hxU⟩
  rcases hdom with hpos | hneg
  · have hloR : 0 < Primitives.loR D I := by
      unfold Primitives.loR
      exact div_pos (by exact_mod_cast hpos) (Primitives.DposR D)
    have hxpos : 0 < x := lt_of_lt_of_le hloR hxL
    exact ne_of_gt hxpos
  · have hhiR : Primitives.hiR D I < 0 := by
      unfold Primitives.hiR
      exact div_neg_of_neg_of_pos (by exact_mod_cast hneg) (Primitives.DposR D)
    have hxneg : x < 0 := lt_of_le_of_lt hxU hhiR
    exact ne_of_lt hxneg

lemma CheckSqrt_real_domain {D : DPos}
    {I : IEnc D} {W : Primitives.WSqrt} {x : ℝ} :
    Primitives.CheckSqrt D I W →
    x ∈ Primitives.γset D I →
    0 ≤ x := by
  intro hW hx
  rcases hW with ⟨hdom, _, _, _, _⟩
  rcases hx with ⟨hxL, _⟩
  have hloR : 0 ≤ Primitives.loR D I := by
    unfold Primitives.loR
    exact div_nonneg (by exact_mod_cast hdom) (le_of_lt (Primitives.DposR D))
  exact le_trans hloR hxL

theorem replayRow_total_sound
    (D : DPos)
    (u : InputOracle)
    (ienv : IEnv D)
    (renv : REnv)
    (row : ProgRow D)
    (Iout : IEnc D) :
    EnvSound D ienv renv →
    RowInputAdmissible D u row →
    ReplayRow D ienv row Iout →
    ∃ xout,
      EvalRow D u renv row xout ∧
      xout ∈ Primitives.γset D Iout := by
  intro hEnv hInput hReplay
  cases row with
  | input q I =>
      dsimp [ReplayRow] at hReplay
      dsimp [RowInputAdmissible] at hInput
      refine ⟨u q, ?_, ?_⟩
      · dsimp [EvalRow]
      · exact mem_gamma_transfer_symm hReplay hInput

  | const k =>
      dsimp [ReplayRow] at hReplay
      refine ⟨(k : ℝ) / (D : ℕ), ?_, ?_⟩
      · dsimp [EvalRow]
      · exact mem_gamma_transfer_symm hReplay (singleton_contains D k)

  | add i j Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hCert⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hEnv hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hEnv hB hbR
      have hs : a + b ∈ Primitives.γset D (Primitives.T_add D A B) :=
        Primitives.rsound_add D A B ha hb
      have hsCert : a + b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a + b, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | sub i j Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hCert⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hEnv hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hEnv hB hbR
      have hs : a - b ∈ Primitives.γset D (Primitives.T_sub D A B) :=
        Primitives.rsound_sub D A B ha hb
      have hsCert : a - b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a - b, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | mul i j W Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hW, hlo, hhi⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hEnv hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hEnv hB hbR
      let Imul : IEnc D := ⟨W.qf, W.qc, Primitives.rsound_mul_closed D A B W hW⟩
      have hCert : IBoundsEq Icert Imul := by
        exact ⟨hlo, hhi⟩
      have hs : a * b ∈ Primitives.γset D Imul :=
        Primitives.rsound_mul D A B W hW ha hb
      have hsCert : a * b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a * b, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | inv i W Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, hA, hW, hlo, hhi⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have hane : a ≠ 0 := CheckInv_real_domain hW ha
      let Iinv : IEnc D := ⟨W.ql, W.qu, Primitives.rsound_inv_closed D A W hW⟩
      have hCert : IBoundsEq Icert Iinv := by
        exact ⟨hlo, hhi⟩
      have hs : (1 / a) ∈ Primitives.γset D Iinv :=
        Primitives.rsound_inv D A W hW ha
      have hsCert : (1 / a) ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨1 / a, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, haR, hane, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | sqrt i W Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, hA, hW, hlo, hhi⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have ha0 : 0 ≤ a := CheckSqrt_real_domain hW ha
      let Isqrt : IEnc D := ⟨W.p, W.q, Primitives.rsound_sqrt_closed D A W hW⟩
      have hCert : IBoundsEq Icert Isqrt := by
        exact ⟨hlo, hhi⟩
      have hs : Real.sqrt a ∈ Primitives.γset D Isqrt :=
        Primitives.rsound_sqrt D A W hW ha
      have hsCert : Real.sqrt a ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨Real.sqrt a, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, haR, ha0, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | relu i Icert =>
      dsimp [ReplayRow] at hReplay
      rcases hReplay with ⟨hOut, A, hA, hCert⟩
      rcases EnvSound_real_exists_of_interval hEnv hA with ⟨a, haR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hEnv hA haR
      have hs : Primitives.relu a ∈ Primitives.γset D (Primitives.T_relu D A) :=
        Primitives.rsound_relu D A ha
      have hsCert : Primitives.relu a ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨Primitives.relu a, ?_, ?_⟩
      · dsimp [EvalRow]
        exact ⟨a, haR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

inductive ReplayProgFrom (D : DPos) :
    IEnv D → List (ProgRow D) → IEnv D → Prop
  | nil (ienv : IEnv D) :
      ReplayProgFrom D ienv [] ienv
  | cons
      (ienv out : IEnv D)
      (row : ProgRow D)
      (rows : List (ProgRow D))
      (Iout : IEnc D) :
      ReplayRow D ienv row Iout →
      ReplayProgFrom D (ienv ++ [Iout]) rows out →
      ReplayProgFrom D ienv (row :: rows) out

inductive EvalProgFrom (D : DPos) (u : InputOracle) :
    REnv → List (ProgRow D) → REnv → Prop
  | nil (renv : REnv) :
      EvalProgFrom D u renv [] renv
  | cons
      (renv out : REnv)
      (row : ProgRow D)
      (rows : List (ProgRow D))
      (xout : ℝ) :
      EvalRow D u renv row xout →
      EvalProgFrom D u (renv ++ [xout]) rows out →
      EvalProgFrom D u renv (row :: rows) out

/-! ### Concrete trajectory uniqueness for program replay -/

lemma listGetOpt_some_unique {α : Type u} {xs : List α} {n : Nat} {a b : α} :
    listGetOpt xs n = some a →
    listGetOpt xs n = some b →
    a = b := by
  intro ha hb
  have hsome : some a = some b := by
    rw [← ha, ← hb]
  cases hsome
  rfl

theorem evalRow_unique
    (D : DPos)
    (u : InputOracle)
    (renv : REnv)
    (row : ProgRow D)
    (x y : ℝ) :
    EvalRow D u renv row x →
    EvalRow D u renv row y →
    x = y := by
  intro hx hy
  cases row with
  | input q I =>
      dsimp [EvalRow] at hx hy
      exact hx.trans hy.symm

  | const k =>
      dsimp [EvalRow] at hx hy
      exact hx.trans hy.symm

  | add i j Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a + b := hxout
        _ = c + d := by simp [hac, hbd]
        _ = y := hyout.symm

  | sub i j Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a - b := hxout
        _ = c - d := by simp [hac, hbd]
        _ = y := hyout.symm

  | mul i j W Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a * b := hxout
        _ = c * d := by simp [hac, hbd]
        _ = y := hyout.symm

  | inv i W Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, ha, _hane, hxout⟩
      rcases hy with ⟨b, hb, _hbne, hyout⟩
      have hab : a = b := listGetOpt_some_unique ha hb
      calc
        x = 1 / a := hxout
        _ = 1 / b := by simp [hab]
        _ = y := hyout.symm

  | sqrt i W Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, ha, _ha0, hxout⟩
      rcases hy with ⟨b, hb, _hb0, hyout⟩
      have hab : a = b := listGetOpt_some_unique ha hb
      calc
        x = Real.sqrt a := hxout
        _ = Real.sqrt b := by simp [hab]
        _ = y := hyout.symm

  | relu i Icert =>
      dsimp [EvalRow] at hx hy
      rcases hx with ⟨a, ha, hxout⟩
      rcases hy with ⟨b, hb, hyout⟩
      have hab : a = b := listGetOpt_some_unique ha hb
      calc
        x = Primitives.relu a := hxout
        _ = Primitives.relu b := by simp [hab]
        _ = y := hyout.symm

theorem evalProgFrom_unique
    (D : DPos)
    (u : InputOracle)
    (renv : REnv)
    (rows : List (ProgRow D))
    (out₁ out₂ : REnv) :
    EvalProgFrom D u renv rows out₁ →
    EvalProgFrom D u renv rows out₂ →
    out₁ = out₂ := by
  intro h₁ h₂
  induction h₁ generalizing out₂ with
  | nil renv =>
      cases h₂
      rfl
  | cons renv out row rows xout hx hrest ih =>
      cases h₂ with
      | cons _ out₂ _ _ yout hy hrest₂ =>
          have hxy : xout = yout :=
            evalRow_unique D u renv row xout yout hx hy
          subst yout
          exact ih out₂ hrest₂

theorem replayProg_total_sound
    (D : DPos)
    (u : InputOracle)
    (rows : List (ProgRow D))
    (progI : IEnv D) :
    RowsInputAdmissible D u rows →
    ReplayProgFrom D [] rows progI →
    ∃ progR,
      EvalProgFrom D u [] rows progR ∧
      EnvSound D progI progR := by
  intro hInput hReplay

  have hEmpty : EnvSound D ([] : IEnv D) ([] : REnv) := by
    constructor
    · rfl
    · intro n I x hI hx
      cases n <;> simp [listGetOpt] at hI

  have aux :
      ∀ (ienv : IEnv D)
        (rows : List (ProgRow D))
        (out : IEnv D)
        (renv : REnv),
        EnvSound D ienv renv →
        RowsInputAdmissible D u rows →
        ReplayProgFrom D ienv rows out →
        ∃ renvOut,
          EvalProgFrom D u renv rows renvOut ∧
          EnvSound D out renvOut := by
    intro ienv rows out renv hEnv hRows hRep
    induction hRep generalizing renv with
    | nil ienv =>
        exact ⟨renv, EvalProgFrom.nil renv, hEnv⟩

    | cons ienv out row rows Iout hRow hRest ih =>
        have hRowInput : RowInputAdmissible D u row := by
          exact hRows row (by simp)

        rcases replayRow_total_sound D u ienv renv row Iout
            hEnv hRowInput hRow with
          ⟨xout, hxEval, hxSound⟩

        have hEnvNext :
            EnvSound D (ienv ++ [Iout]) (renv ++ [xout]) :=
          EnvSound_append hEnv hxSound

        have hRowsTail : RowsInputAdmissible D u rows := by
          intro row' hmem
          exact hRows row' (by simp [hmem])

        rcases ih (renv := renv ++ [xout]) hEnvNext hRowsTail with
          ⟨renvOut, hEvalRest, hSoundOut⟩

        exact ⟨renvOut,
          EvalProgFrom.cons renv renvOut row rows xout hxEval hEvalRest,
          hSoundOut⟩

  exact aux ([] : IEnv D) rows progI ([] : REnv) hEmpty hInput hReplay

/-- Replay acceptance determines a unique concrete program trajectory. -/
theorem replayProg_total_exists_unique
    (D : DPos)
    (u : InputOracle)
    (rows : List (ProgRow D))
    (progI : IEnv D) :
    RowsInputAdmissible D u rows →
    ReplayProgFrom D [] rows progI →
    ∃! progR,
      EvalProgFrom D u [] rows progR ∧
      EnvSound D progI progR := by
  intro hInput hReplay
  rcases replayProg_total_sound D u rows progI hInput hReplay with
    ⟨progR, hEval, hSound⟩
  refine ⟨progR, ⟨hEval, hSound⟩, ?_⟩
  intro progR' hProgR'
  exact (evalProgFrom_unique D u [] rows progR progR' hEval hProgR'.1).symm

inductive SpecRow (D : DPos) : Type
  | var   : Nat → IEnc D → SpecRow D
  | const : ℤ → SpecRow D
  | add   : Nat → Nat → IEnc D → SpecRow D
  | sub   : Nat → Nat → IEnc D → SpecRow D
  | mul   : Nat → Nat → Primitives.WMul → IEnc D → SpecRow D

/-- Specification-row dependency well-formedness.
`var` references the program environment; other rows reference earlier spec rows. -/
def SpecRowRefsOK {D : DPos} (progLen specLen : Nat) : SpecRow D → Prop
  | SpecRow.var v _ => v < progLen
  | SpecRow.const _ => True
  | SpecRow.add i j _ => i < specLen ∧ j < specLen
  | SpecRow.sub i j _ => i < specLen ∧ j < specLen
  | SpecRow.mul i j _ _ => i < specLen ∧ j < specLen

/-- Topological well-formedness for specification rows. -/
def SpecRowsRefsOK {D : DPos} (progLen : Nat) : Nat → List (SpecRow D) → Prop
  | _, [] => True
  | n, row :: rows =>
      SpecRowRefsOK progLen n row ∧
      SpecRowsRefsOK (D := D) progLen (n + 1) rows

def SpecRowsTopological
    (D : DPos)
    (progLen : Nat)
    (rows : List (SpecRow D)) : Prop :=
  SpecRowsRefsOK (D := D) progLen 0 rows

def ReplaySpecRow
    (D : DPos)
    (progI : IEnv D)
    (specI : IEnv D) :
    SpecRow D → IEnc D → Prop
  | SpecRow.var v Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A,
        listGetOpt progI v = some A ∧
        IBoundsEq Icert A

  | SpecRow.const k, Iout =>
      IBoundsEq Iout (ISingleton D k)

  | SpecRow.add i j Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt specI i = some A ∧
        listGetOpt specI j = some B ∧
        IBoundsEq Icert (Primitives.T_add D A B)

  | SpecRow.sub i j Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt specI i = some A ∧
        listGetOpt specI j = some B ∧
        IBoundsEq Icert (Primitives.T_sub D A B)

  | SpecRow.mul i j W Icert, Iout =>
      IBoundsEq Iout Icert ∧
      ∃ A B,
        listGetOpt specI i = some A ∧
        listGetOpt specI j = some B ∧
        Primitives.CheckMul D A B W ∧
        Icert.lo = W.qf ∧
        Icert.hi = W.qc

def EvalSpecRow
    (D : DPos)
    (progR : REnv)
    (specR : REnv) :
    SpecRow D → ℝ → Prop
  | SpecRow.var v _, x =>
      listGetOpt progR v = some x

  | SpecRow.const k, x =>
      x = (k : ℝ) / (D : ℕ)

  | SpecRow.add i j _, x =>
      ∃ a b,
        listGetOpt specR i = some a ∧
        listGetOpt specR j = some b ∧
        x = a + b

  | SpecRow.sub i j _, x =>
      ∃ a b,
        listGetOpt specR i = some a ∧
        listGetOpt specR j = some b ∧
        x = a - b

  | SpecRow.mul i j _ _, x =>
      ∃ a b,
        listGetOpt specR i = some a ∧
        listGetOpt specR j = some b ∧
        x = a * b

theorem replaySpecRow_total_sound
    (D : DPos)
    (progI : IEnv D)
    (progR : REnv)
    (specI : IEnv D)
    (specR : REnv)
    (row : SpecRow D)
    (Iout : IEnc D) :
    EnvSound D progI progR →
    EnvSound D specI specR →
    ReplaySpecRow D progI specI row Iout →
    ∃ xout,
      EvalSpecRow D progR specR row xout ∧
      xout ∈ Primitives.γset D Iout := by
  intro hProg hSpec hReplay
  cases row with
  | var v Icert =>
      dsimp [ReplaySpecRow] at hReplay
      rcases hReplay with ⟨hOut, A, hA, hCert⟩
      rcases EnvSound_real_exists_of_interval hProg hA with ⟨x, hxR⟩
      have hxA : x ∈ Primitives.γset D A := EnvSound_get hProg hA hxR
      have hxCert : x ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hxA
      refine ⟨x, ?_, ?_⟩
      · dsimp [EvalSpecRow]
        exact hxR
      · exact mem_gamma_transfer_symm hOut hxCert

  | const k =>
      dsimp [ReplaySpecRow] at hReplay
      refine ⟨(k : ℝ) / (D : ℕ), ?_, ?_⟩
      · dsimp [EvalSpecRow]
      · exact mem_gamma_transfer_symm hReplay (singleton_contains D k)

  | add i j Icert =>
      dsimp [ReplaySpecRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hCert⟩
      rcases EnvSound_real_exists_of_interval hSpec hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hSpec hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hSpec hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hSpec hB hbR
      have hs : a + b ∈ Primitives.γset D (Primitives.T_add D A B) :=
        Primitives.rsound_add D A B ha hb
      have hsCert : a + b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a + b, ?_, ?_⟩
      · dsimp [EvalSpecRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | sub i j Icert =>
      dsimp [ReplaySpecRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hCert⟩
      rcases EnvSound_real_exists_of_interval hSpec hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hSpec hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hSpec hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hSpec hB hbR
      have hs : a - b ∈ Primitives.γset D (Primitives.T_sub D A B) :=
        Primitives.rsound_sub D A B ha hb
      have hsCert : a - b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a - b, ?_, ?_⟩
      · dsimp [EvalSpecRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

  | mul i j W Icert =>
      dsimp [ReplaySpecRow] at hReplay
      rcases hReplay with ⟨hOut, A, B, hA, hB, hW, hlo, hhi⟩
      rcases EnvSound_real_exists_of_interval hSpec hA with ⟨a, haR⟩
      rcases EnvSound_real_exists_of_interval hSpec hB with ⟨b, hbR⟩
      have ha : a ∈ Primitives.γset D A := EnvSound_get hSpec hA haR
      have hb : b ∈ Primitives.γset D B := EnvSound_get hSpec hB hbR
      let Imul : IEnc D := ⟨W.qf, W.qc, Primitives.rsound_mul_closed D A B W hW⟩
      have hCert : IBoundsEq Icert Imul := by
        exact ⟨hlo, hhi⟩
      have hs : a * b ∈ Primitives.γset D Imul :=
        Primitives.rsound_mul D A B W hW ha hb
      have hsCert : a * b ∈ Primitives.γset D Icert :=
        mem_gamma_transfer_symm hCert hs
      refine ⟨a * b, ?_, ?_⟩
      · dsimp [EvalSpecRow]
        exact ⟨a, b, haR, hbR, rfl⟩
      · exact mem_gamma_transfer_symm hOut hsCert

inductive ReplaySpecFrom (D : DPos) (progI : IEnv D) :
    IEnv D → List (SpecRow D) → IEnv D → Prop
  | nil (specI : IEnv D) :
      ReplaySpecFrom D progI specI [] specI
  | cons
      (specI out : IEnv D)
      (row : SpecRow D)
      (rows : List (SpecRow D))
      (Iout : IEnc D) :
      ReplaySpecRow D progI specI row Iout →
      ReplaySpecFrom D progI (specI ++ [Iout]) rows out →
      ReplaySpecFrom D progI specI (row :: rows) out

inductive EvalSpecFrom (D : DPos) (progR : REnv) :
    REnv → List (SpecRow D) → REnv → Prop
  | nil (specR : REnv) :
      EvalSpecFrom D progR specR [] specR
  | cons
      (specR out : REnv)
      (row : SpecRow D)
      (rows : List (SpecRow D))
      (xout : ℝ) :
      EvalSpecRow D progR specR row xout →
      EvalSpecFrom D progR (specR ++ [xout]) rows out →
      EvalSpecFrom D progR specR (row :: rows) out

/-! ### Concrete trajectory uniqueness for specification replay -/

theorem evalSpecRow_unique
    (D : DPos)
    (progR : REnv)
    (specR : REnv)
    (row : SpecRow D)
    (x y : ℝ) :
    EvalSpecRow D progR specR row x →
    EvalSpecRow D progR specR row y →
    x = y := by
  intro hx hy
  cases row with
  | var v Icert =>
      dsimp [EvalSpecRow] at hx hy
      exact listGetOpt_some_unique hx hy

  | const k =>
      dsimp [EvalSpecRow] at hx hy
      exact hx.trans hy.symm

  | add i j Icert =>
      dsimp [EvalSpecRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a + b := hxout
        _ = c + d := by simp [hac, hbd]
        _ = y := hyout.symm

  | sub i j Icert =>
      dsimp [EvalSpecRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a - b := hxout
        _ = c - d := by simp [hac, hbd]
        _ = y := hyout.symm

  | mul i j W Icert =>
      dsimp [EvalSpecRow] at hx hy
      rcases hx with ⟨a, b, ha, hb, hxout⟩
      rcases hy with ⟨c, d, hc, hd, hyout⟩
      have hac : a = c := listGetOpt_some_unique ha hc
      have hbd : b = d := listGetOpt_some_unique hb hd
      calc
        x = a * b := hxout
        _ = c * d := by simp [hac, hbd]
        _ = y := hyout.symm

theorem evalSpecFrom_unique
    (D : DPos)
    (progR : REnv)
    (specR : REnv)
    (rows : List (SpecRow D))
    (out₁ out₂ : REnv) :
    EvalSpecFrom D progR specR rows out₁ →
    EvalSpecFrom D progR specR rows out₂ →
    out₁ = out₂ := by
  intro h₁ h₂
  induction h₁ generalizing out₂ with
  | nil specR =>
      cases h₂
      rfl
  | cons specR out row rows xout hx hrest ih =>
      cases h₂ with
      | cons _ out₂ _ _ yout hy hrest₂ =>
          have hxy : xout = yout :=
            evalSpecRow_unique D progR specR row xout yout hx hy
          subst yout
          exact ih out₂ hrest₂

theorem replaySpec_total_sound
    (D : DPos)
    (progI : IEnv D)
    (progR : REnv)
    (specRows : List (SpecRow D))
    (specI : IEnv D) :
    EnvSound D progI progR →
    ReplaySpecFrom D progI [] specRows specI →
    ∃ specR,
      EvalSpecFrom D progR [] specRows specR ∧
      EnvSound D specI specR := by
  intro hProg hReplay

  have hEmpty : EnvSound D ([] : IEnv D) ([] : REnv) := by
    constructor
    · rfl
    · intro n I x hI hx
      cases n <;> simp [listGetOpt] at hI

  have aux :
      ∀ (specI₀ : IEnv D)
        (rows : List (SpecRow D))
        (out : IEnv D)
        (specR₀ : REnv),
        EnvSound D specI₀ specR₀ →
        ReplaySpecFrom D progI specI₀ rows out →
        ∃ specRout,
          EvalSpecFrom D progR specR₀ rows specRout ∧
          EnvSound D out specRout := by
    intro specI₀ rows out specR₀ hSpec hRep
    induction hRep generalizing specR₀ with
    | nil specI₀ =>
        exact ⟨specR₀, EvalSpecFrom.nil specR₀, hSpec⟩

    | cons specI₀ out row rows Iout hRow hRest ih =>
        rcases replaySpecRow_total_sound D progI progR specI₀ specR₀ row Iout
            hProg hSpec hRow with
          ⟨xout, hxEval, hxSound⟩

        have hSpecNext :
            EnvSound D (specI₀ ++ [Iout]) (specR₀ ++ [xout]) :=
          EnvSound_append hSpec hxSound

        rcases ih (specR₀ := specR₀ ++ [xout]) hSpecNext with
          ⟨specRout, hEvalRest, hSoundOut⟩

        exact ⟨specRout,
          EvalSpecFrom.cons specR₀ specRout row rows xout hxEval hEvalRest,
          hSoundOut⟩

  exact aux ([] : IEnv D) specRows specI ([] : REnv) hEmpty hReplay

/-- Replay acceptance determines a unique concrete specification trajectory
    once the concrete program trajectory is fixed. -/
theorem replaySpec_total_exists_unique
    (D : DPos)
    (progI : IEnv D)
    (progR : REnv)
    (specRows : List (SpecRow D))
    (specI : IEnv D) :
    EnvSound D progI progR →
    ReplaySpecFrom D progI [] specRows specI →
    ∃! specR,
      EvalSpecFrom D progR [] specRows specR ∧
      EnvSound D specI specR := by
  intro hProg hReplay
  rcases replaySpec_total_sound D progI progR specRows specI hProg hReplay with
    ⟨specR, hEval, hSound⟩
  refine ⟨specR, ⟨hEval, hSound⟩, ?_⟩
  intro specR' hSpecR'
  exact (evalSpecFrom_unique D progR [] specRows specR specR' hEval hSpecR'.1).symm

/-! ### DAG dependency helpers -/

/-- Dependencies of a program row: the list of earlier node IDs it reads. -/
def ProgRowDeps (D : DPos) : ProgRow D → List Nat
  | ProgRow.input _ _ => []
  | ProgRow.const _   => []
  | ProgRow.add i j _ => [i, j]
  | ProgRow.sub i j _ => [i, j]
  | ProgRow.mul i j _ _ => [i, j]
  | ProgRow.inv i _ _   => [i]
  | ProgRow.sqrt i _ _  => [i]
  | ProgRow.relu i _    => [i]

/-- Dependencies of a specification row: the earlier spec-node IDs it reads.
    `var` references the program environment and has no spec-side dependency. -/
def SpecRowDeps (D : DPos) : SpecRow D → List Nat
  | SpecRow.var _ _    => []
  | SpecRow.const _    => []
  | SpecRow.add i j _  => [i, j]
  | SpecRow.sub i j _  => [i, j]
  | SpecRow.mul i j _ _ => [i, j]

/-! ### Node and edge types -/

/-- A program node: a unique ID paired with its row payload. -/
structure ProgNode (D : DPos) where
  id : Nat
  row : ProgRow D

/-- A specification node: a unique ID paired with its row payload. -/
structure SpecNode (D : DPos) where
  id : Nat
  row : SpecRow D

/-- A directed edge in the program DAG. -/
structure ProgEdge where
  src : Nat
  dst : Nat

/-- A directed edge in the specification DAG. -/
structure SpecEdge where
  src : Nat
  dst : Nat

/-- Edges generated by a single program node: one per dependency. -/
def ProgNodeEdges (D : DPos) (node : ProgNode D) : List ProgEdge :=
  (ProgRowDeps D node.row).map (fun dep => { src := dep, dst := node.id })

/-- Edges generated by a single specification node: one per dependency. -/
def SpecNodeEdges (D : DPos) (node : SpecNode D) : List SpecEdge :=
  (SpecRowDeps D node.row).map (fun dep => { src := dep, dst := node.id })

/-! ### Topological well-formedness -/

/-- `ProgNodesWellFormedFrom D n nodes`:
    every node's `id` equals its list position (counting from `n`),
    and every dependency index is strictly below that position. -/
def ProgNodesWellFormedFrom (D : DPos) : Nat → List (ProgNode D) → Prop
  | _, []           => True
  | n, node :: rest =>
      node.id = n ∧
      (∀ dep ∈ ProgRowDeps D node.row, dep < n) ∧
      ProgNodesWellFormedFrom D (n + 1) rest

/-- `SpecNodesWellFormedFrom D progLen n nodes`:
    every node's `id` equals its list position (counting from `n`),
    `var`-rows reference only valid program indices (< `progLen`),
    and every spec-side dependency index is strictly below that position. -/
def SpecNodesWellFormedFrom
    (D : DPos) (progLen : Nat) : Nat → List (SpecNode D) → Prop
  | _, []           => True
  | n, node :: rest =>
      node.id = n ∧
      (match node.row with
       | SpecRow.var v _ => v < progLen
       | _               => True) ∧
      (∀ dep ∈ SpecRowDeps D node.row, dep < n) ∧
      SpecNodesWellFormedFrom D progLen (n + 1) rest

/-! ### List utility for edge serialisation -/

/-- Lean 4.28 does not expose `List.bind` as a field projection in this environment,
    so we use an explicit local flatten-map. -/
def listBind {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | a :: as, f => f a ++ listBind as f

/-! ### DAG structures (node/edge representation) -/

/-- A well-formed program DAG.
    Nodes carry sequential IDs and row payloads; edges are exactly those
    induced by row dependencies. -/
structure ProgDAG (D : DPos) where
  nodes : List (ProgNode D)
  edges    : List ProgEdge
  wf       : ProgNodesWellFormedFrom D 0 nodes
  edges_ok : edges = listBind nodes (ProgNodeEdges D)

/-- A well-formed specification DAG.
    `var`-rows refer to a program environment of length `progLen`. -/
structure SpecDAG (D : DPos) (progLen : Nat) where
  nodes : List (SpecNode D)
  edges    : List SpecEdge
  wf       : SpecNodesWellFormedFrom D progLen 0 nodes
  edges_ok : edges = listBind nodes (SpecNodeEdges D)

/-! ### Lowering nodes to rows -/

/-- Forget the node ID; keep only the row payload. -/
def lowerProgNode (D : DPos) (node : ProgNode D) : ProgRow D := node.row

/-- Forget the node ID; keep only the row payload. -/
def lowerSpecNode (D : DPos) (node : SpecNode D) : SpecRow D := node.row

/-! ### Compilers: DAG → topologically-ordered row list -/

/-- Compile a program DAG to its topologically-ordered row list. -/
def compileProgDAG (D : DPos) (G : ProgDAG D) : List (ProgRow D) :=
  G.nodes.map (lowerProgNode D)

/-- Compile a specification DAG to its topologically-ordered row list. -/
def compileSpecDAG
    (D : DPos) (progLen : Nat) (S : SpecDAG D progLen) : List (SpecRow D) :=
  S.nodes.map (lowerSpecNode D)

/-! ### Direct node/edge DAG semantics -/

/-- Semantics of a program DAG: evaluate nodes in topological order.
    Defined directly via the compiled row list; never references a bare
    `.rows` field. -/
def ProgDAGSem
    (D : DPos) (u : InputOracle) (G : ProgDAG D) (progR : REnv) : Prop :=
  EvalProgFrom D u [] (G.nodes.map (lowerProgNode D)) progR

/-- Semantics of a specification DAG: evaluate nodes in topological order.
    Defined directly via the compiled row list. -/
def SpecDAGSem
    (D : DPos) (progR : REnv) (progLen : Nat)
    (S : SpecDAG D progLen) (specR : REnv) : Prop :=
  EvalSpecFrom D progR [] (S.nodes.map (lowerSpecNode D)) specR

/-! ### Compiler-correctness linking lemmas -/

/-- Program DAG compiler correctness:
    the node/edge DAG semantics and the compiled-row semantics coincide. -/
theorem compileProgDAG_semantics_correct
    (D : DPos)
    (u : InputOracle)
    (G : ProgDAG D)
    (progR : REnv) :
    ProgDAGSem D u G progR ↔
    EvalProgFrom D u [] (compileProgDAG D G) progR := by
  simp only [ProgDAGSem, compileProgDAG, lowerProgNode]

/-- Specification DAG compiler correctness:
    the node/edge DAG semantics and the compiled-row semantics coincide. -/
theorem compileSpecDAG_semantics_correct
    (D : DPos)
    (progR : REnv)
    (progLen : Nat)
    (S : SpecDAG D progLen)
    (specR : REnv) :
    SpecDAGSem D progR progLen S specR ↔
    EvalSpecFrom D progR [] (compileSpecDAG D progLen S) specR := by
  simp only [SpecDAGSem, compileSpecDAG, lowerSpecNode]

/-! ### Source-level specification expressions and SpecExpr → SpecDAG compilation

This layer closes the source-syntax gap in Section 6 of the paper:
source specification expressions are made explicit, given direct real semantics,
and compiled into tree-shaped specification DAG payloads.  The semantic
correctness theorem below is the Lean counterpart of compile correctness for
specification expressions.
-/

/-- Source-level polynomial specification expressions.

The interval certificates carried by the constructors are ignored by real
semantics, but they are retained because replay rows need exactly these
payloads. -/
inductive SpecExpr (D : DPos) : Type where
  | var   : Nat → IEnc D → SpecExpr D
  | const : ℤ → SpecExpr D
  | add   : SpecExpr D → SpecExpr D → IEnc D → SpecExpr D
  | sub   : SpecExpr D → SpecExpr D → IEnc D → SpecExpr D
  | mul   : SpecExpr D → SpecExpr D → Primitives.WMul → IEnc D → SpecExpr D

namespace SpecExpr

/-- Direct real semantics of source-level specification expressions. -/
def eval {D : DPos} (x : Nat → ℝ) : SpecExpr D → ℝ
  | var v _       => x v
  | const k       => (k : ℝ) / (D : ℕ)
  | add e₁ e₂ _   => eval x e₁ + eval x e₂
  | sub e₁ e₂ _   => eval x e₁ - eval x e₂
  | mul e₁ e₂ _ _ => eval x e₁ * eval x e₂

end SpecExpr

/-- Tree-shaped specification DAG syntax produced by source compilation. -/
inductive SpecTreeDAG (D : DPos) : Type where
  | var   : Nat → IEnc D → SpecTreeDAG D
  | const : ℤ → SpecTreeDAG D
  | add   : SpecTreeDAG D → SpecTreeDAG D → IEnc D → SpecTreeDAG D
  | sub   : SpecTreeDAG D → SpecTreeDAG D → IEnc D → SpecTreeDAG D
  | mul   : SpecTreeDAG D → SpecTreeDAG D → Primitives.WMul → IEnc D → SpecTreeDAG D

namespace SpecTreeDAG

/-- Real semantics of the compiled tree-shaped specification DAG. -/
def eval {D : DPos} (x : Nat → ℝ) : SpecTreeDAG D → ℝ
  | var v _       => x v
  | const k       => (k : ℝ) / (D : ℕ)
  | add g₁ g₂ _   => eval x g₁ + eval x g₂
  | sub g₁ g₂ _   => eval x g₁ - eval x g₂
  | mul g₁ g₂ _ _ => eval x g₁ * eval x g₂

end SpecTreeDAG

/-- Compile a source specification expression into a tree-shaped specification DAG. -/
def compileSpecExprTree {D : DPos} : SpecExpr D → SpecTreeDAG D
  | SpecExpr.var v I       => SpecTreeDAG.var v I
  | SpecExpr.const k       => SpecTreeDAG.const k
  | SpecExpr.add e₁ e₂ I   => SpecTreeDAG.add (compileSpecExprTree e₁) (compileSpecExprTree e₂) I
  | SpecExpr.sub e₁ e₂ I   => SpecTreeDAG.sub (compileSpecExprTree e₁) (compileSpecExprTree e₂) I
  | SpecExpr.mul e₁ e₂ W I => SpecTreeDAG.mul (compileSpecExprTree e₁) (compileSpecExprTree e₂) W I

/-- Source-to-tree-DAG compile correctness for specification expressions. -/
theorem compileSpecExprTree_correct
    {D : DPos}
    (x : Nat → ℝ)
    (e : SpecExpr D) :
    SpecTreeDAG.eval x (compileSpecExprTree e) = SpecExpr.eval x e := by
  induction e with
  | var v I => rfl
  | const k => rfl
  | add e₁ e₂ I ih₁ ih₂ =>
      simp [compileSpecExprTree, SpecTreeDAG.eval, SpecExpr.eval, ih₁, ih₂]
  | sub e₁ e₂ I ih₁ ih₂ =>
      simp [compileSpecExprTree, SpecTreeDAG.eval, SpecExpr.eval, ih₁, ih₂]
  | mul e₁ e₂ W I ih₁ ih₂ =>
      simp [compileSpecExprTree, SpecTreeDAG.eval, SpecExpr.eval, ih₁, ih₂]

/-- Shift specification-side row references by an already-emitted prefix length. -/
def shiftSpecRowRefs {D : DPos} (k : Nat) : SpecRow D → SpecRow D
  | SpecRow.var v I       => SpecRow.var v I
  | SpecRow.const c       => SpecRow.const c
  | SpecRow.add i j I     => SpecRow.add (k + i) (k + j) I
  | SpecRow.sub i j I     => SpecRow.sub (k + i) (k + j) I
  | SpecRow.mul i j W I   => SpecRow.mul (k + i) (k + j) W I

/-- Row-list serialisation of a compiled specification expression.

The list is post-order: children first, then the parent OP row.  No
sub-expression sharing is performed. -/
def compileSpecExprRows {D : DPos} : SpecExpr D → List (SpecRow D)
  | SpecExpr.var v I       => [SpecRow.var v I]
  | SpecExpr.const k       => [SpecRow.const k]
  | SpecExpr.add e₁ e₂ I   =>
      let r₁ := compileSpecExprRows e₁
      let r₂ := compileSpecExprRows e₂
      r₁ ++ r₂.map (shiftSpecRowRefs r₁.length) ++
        [SpecRow.add (r₁.length - 1) (r₁.length + (r₂.length - 1)) I]
  | SpecExpr.sub e₁ e₂ I   =>
      let r₁ := compileSpecExprRows e₁
      let r₂ := compileSpecExprRows e₂
      r₁ ++ r₂.map (shiftSpecRowRefs r₁.length) ++
        [SpecRow.sub (r₁.length - 1) (r₁.length + (r₂.length - 1)) I]
  | SpecExpr.mul e₁ e₂ W I =>
      let r₁ := compileSpecExprRows e₁
      let r₂ := compileSpecExprRows e₂
      r₁ ++ r₂.map (shiftSpecRowRefs r₁.length) ++
        [SpecRow.mul (r₁.length - 1) (r₁.length + (r₂.length - 1)) W I]

/-- The root index of the row-list serialisation. -/
def compileSpecExprRoot {D : DPos} (e : SpecExpr D) : Nat :=
  (compileSpecExprRows e).length - 1

/-- Attach consecutive node IDs to a row list. -/
def rowsToSpecNodesFrom {D : DPos} : Nat → List (SpecRow D) → List (SpecNode D)
  | _, [] => []
  | n, row :: rows => { id := n, row := row } :: rowsToSpecNodesFrom (n + 1) rows

/-- Node-list serialisation of a compiled source-level specification expression. -/
def compileSpecExprNodes {D : DPos} (e : SpecExpr D) : List (SpecNode D) :=
  rowsToSpecNodesFrom 0 (compileSpecExprRows e)

/-- Edge-list serialisation induced by compiled source-level specification nodes. -/
def compileSpecExprEdges {D : DPos} (e : SpecExpr D) : List SpecEdge :=
  listBind (compileSpecExprNodes e) (SpecNodeEdges D)

/-- All source-level program-variable references are within the compiled program length. -/
def SpecExpr.varsOK {D : DPos} (progLen : Nat) : SpecExpr D → Prop
  | SpecExpr.var v _       => v < progLen
  | SpecExpr.const _       => True
  | SpecExpr.add e₁ e₂ _   => SpecExpr.varsOK progLen e₁ ∧ SpecExpr.varsOK progLen e₂
  | SpecExpr.sub e₁ e₂ _   => SpecExpr.varsOK progLen e₁ ∧ SpecExpr.varsOK progLen e₂
  | SpecExpr.mul e₁ e₂ _ _ => SpecExpr.varsOK progLen e₁ ∧ SpecExpr.varsOK progLen e₂

/-- A concrete compiled source-expression DAG package. -/
structure CompiledSpecExprDAG (D : DPos) where
  nodes : List (SpecNode D)
  edges : List SpecEdge
  root  : Nat

/-- Compile a source expression into a concrete node/edge DAG package. -/
def compileSpecExprDAG {D : DPos} (e : SpecExpr D) : CompiledSpecExprDAG D :=
  { nodes := compileSpecExprNodes e
    edges := compileSpecExprEdges e
    root  := compileSpecExprRoot e }

/-- View a compiled source-expression DAG as the existing `SpecDAG` type once
    its topological well-formedness proof has been supplied. -/
def compileSpecExprAsSpecDAG
    {D : DPos}
    (progLen : Nat)
    (e : SpecExpr D)
    (wf : SpecNodesWellFormedFrom D progLen 0 (compileSpecExprNodes e)) :
    SpecDAG D progLen :=
  { nodes := compileSpecExprNodes e
    edges := compileSpecExprEdges e
    wf := wf
    edges_ok := by rfl }



def RootUpperOK (D : DPos) (specI : IEnv D) (roots : List Nat) : Prop :=
  ∀ r, r ∈ roots →
    ∃ I,
      listGetOpt specI r = some I ∧
      I.hi ≤ 0

def RootsWellFormed (D : DPos) (specI : IEnv D) (roots : List Nat) : Prop :=
  ∀ r, r ∈ roots → r < specI.length

lemma RootUpperOK_wf
    (D : DPos)
    (specI : IEnv D)
    (roots : List Nat) :
    RootUpperOK D specI roots →
    RootsWellFormed D specI roots := by
  intro h r hr
  rcases h r hr with ⟨I, hI, _⟩
  exact listGetOpt_eq_some_length hI

lemma upper_nonpos_sound
    (D : DPos)
    (I : IEnc D)
    (x : ℝ) :
    x ∈ Primitives.γset D I →
    I.hi ≤ 0 →
    x ≤ 0 := by
  intro hx hhi
  rcases hx with ⟨_, hxhi⟩
  have hD : (0 : ℝ) < (D : ℕ) := Primitives.DposR D
  have hdiv : (I.hi : ℝ) / (D : ℕ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hhi) (le_of_lt hD)
  exact le_trans hxhi hdiv

theorem roots_nonpos_sound
    (D : DPos)
    (specI : IEnv D)
    (specR : REnv)
    (roots : List Nat) :
    EnvSound D specI specR →
    RootUpperOK D specI roots →
    ∀ r, r ∈ roots →
      ∃ x,
        listGetOpt specR r = some x ∧
        x ≤ 0 := by
  intro hEnv hRoot r hr
  rcases hRoot r hr with ⟨I, hI, hhi⟩
  rcases EnvSound_real_exists_of_interval hEnv hI with ⟨x, hx⟩
  have hxMem : x ∈ Primitives.γset D I := EnvSound_get hEnv hI hx
  have hxNonpos : x ≤ 0 := upper_nonpos_sound D I x hxMem hhi
  exact ⟨x, hx, hxNonpos⟩

structure Cert (D : DPos) where
  rows : List (ProgRow D)
  specRows : List (SpecRow D)
  roots : List Nat

/-- A DAG certificate: a program DAG, a compatible specification DAG,
    and a list of root output indices. -/
structure DAGCert (D : DPos) where
  progDag : ProgDAG D
  specDag : SpecDAG D (compileProgDAG D progDag).length
  roots   : List Nat

/-- Convert a DAG certificate to the flat row-list format expected by the
    Boolean replay verifier. -/
def DAGCert.toCert (D : DPos) (dcert : DAGCert D) : Cert D :=
  { rows     := compileProgDAG D dcert.progDag
    specRows := compileSpecDAG D (compileProgDAG D dcert.progDag).length dcert.specDag
    roots    := dcert.roots }

/-- Semantic root condition for real specification evaluations. -/
def RootsNonPosSem
    (specR : REnv)
    (roots : List Nat) : Prop :=
  ∀ r, r ∈ roots →
    ∃ x,
      listGetOpt specR r = some x ∧
      x ≤ 0

/-- Direct semantic validity of a DAG certificate, stated at the node/edge
    DAG level before compilation. -/
def DAGSemanticValid
    (D : DPos)
    (dcert : DAGCert D) : Prop :=
  ∀ u : InputOracle,
    RowsInputAdmissible D u (compileProgDAG D dcert.progDag) →
    ∃ progR specR,
      ProgDAGSem D u dcert.progDag progR ∧
      SpecDAGSem D progR (compileProgDAG D dcert.progDag).length
        dcert.specDag specR ∧
      RootsNonPosSem specR dcert.roots

def AcceptProp (D : DPos) (cert : Cert D) : Prop :=
  ∃ progI specI,
    ReplayProgFrom D [] cert.rows progI ∧
    ReplaySpecFrom D progI [] cert.specRows specI ∧
    RootUpperOK D specI cert.roots

def SemanticValid
    (D : DPos)
    (rows : List (ProgRow D))
    (specRows : List (SpecRow D))
    (roots : List Nat) : Prop :=
  ∀ u : InputOracle,
    RowsInputAdmissible D u rows →
    ∃ progR specR,
      EvalProgFrom D u [] rows progR ∧
      EvalSpecFrom D progR [] specRows specR ∧
      ∀ r, r ∈ roots →
        ∃ x,
          listGetOpt specR r = some x ∧
          x ≤ 0

/-- Semantic validity of the compiled replay certificate. -/
def CompiledDAGSemanticValid
    (D : DPos)
    (dcert : DAGCert D) : Prop :=
  SemanticValid D
    (compileProgDAG D dcert.progDag)
    (compileSpecDAG D (compileProgDAG D dcert.progDag).length dcert.specDag)
    dcert.roots

/-- Full DAG compiler correctness.

    The direct node/edge DAG semantics coincide with the semantics of the
    compiled replay-verifier certificate.  The proof routes explicitly through
    `compileProgDAG_semantics_correct` and `compileSpecDAG_semantics_correct`
    rather than relying on row-list identity. -/
theorem dagCompiler_correct
    (D : DPos)
    (dcert : DAGCert D) :
    DAGSemanticValid D dcert ↔
    CompiledDAGSemanticValid D dcert := by
  constructor
  · intro hDAG u hInput
    rcases hDAG u hInput with ⟨progR, specR, hProg, hSpec, hRoots⟩
    refine ⟨progR, specR, ?_, ?_, hRoots⟩
    · exact (compileProgDAG_semantics_correct D u dcert.progDag progR).mp hProg
    · exact (compileSpecDAG_semantics_correct D progR
          (compileProgDAG D dcert.progDag).length dcert.specDag specR).mp hSpec
  · intro hComp u hInput
    rcases hComp u hInput with ⟨progR, specR, hProg, hSpec, hRoots⟩
    refine ⟨progR, specR, ?_, ?_, hRoots⟩
    · exact (compileProgDAG_semantics_correct D u dcert.progDag progR).mpr hProg
    · exact (compileSpecDAG_semantics_correct D progR
          (compileProgDAG D dcert.progDag).length dcert.specDag specR).mpr hSpec

/-- Soundness direction of DAG compiler correctness. -/
theorem dagCompiler_sound
    (D : DPos)
    (dcert : DAGCert D) :
    DAGSemanticValid D dcert →
    CompiledDAGSemanticValid D dcert :=
  (dagCompiler_correct D dcert).mp

/-- Completeness direction of DAG compiler correctness. -/
theorem dagCompiler_complete
    (D : DPos)
    (dcert : DAGCert D) :
    CompiledDAGSemanticValid D dcert →
    DAGSemanticValid D dcert :=
  (dagCompiler_correct D dcert).mpr

theorem acceptProp_sound
    (D : DPos)
    (cert : Cert D) :
    AcceptProp D cert →
    SemanticValid D cert.rows cert.specRows cert.roots := by
  intro hAcc u hInput
  rcases hAcc with ⟨progI, specI, hProgReplay, hSpecReplay, hRoots⟩

  rcases replayProg_total_sound D u cert.rows progI hInput hProgReplay with
    ⟨progR, hProgEval, hProgSound⟩

  rcases replaySpec_total_sound D progI progR cert.specRows specI
      hProgSound hSpecReplay with
    ⟨specR, hSpecEval, hSpecSound⟩

  have hRootSound :
      ∀ r, r ∈ cert.roots →
        ∃ x,
          listGetOpt specR r = some x ∧
          x ≤ 0 :=
    roots_nonpos_sound D specI specR cert.roots hSpecSound hRoots

  exact ⟨progR, specR, hProgEval, hSpecEval, hRootSound⟩

/-- Acceptance implies existence and uniqueness of the concrete real trajectory
    `(program trajectory, specification trajectory)`. -/
theorem acceptProp_sound_unique
    (D : DPos)
    (cert : Cert D) :
    AcceptProp D cert →
    ∀ u : InputOracle,
      RowsInputAdmissible D u cert.rows →
      ∃! traj : REnv × REnv,
        EvalProgFrom D u [] cert.rows traj.1 ∧
        EvalSpecFrom D traj.1 [] cert.specRows traj.2 ∧
        (∀ r, r ∈ cert.roots →
          ∃ x,
            listGetOpt traj.2 r = some x ∧
            x ≤ 0) := by
  intro hAcc u hInput
  rcases hAcc with ⟨progI, specI, hProgReplay, hSpecReplay, hRoots⟩

  rcases replayProg_total_sound D u cert.rows progI hInput hProgReplay with
    ⟨progR, hProgEval, hProgSound⟩

  rcases replaySpec_total_sound D progI progR cert.specRows specI
      hProgSound hSpecReplay with
    ⟨specR, hSpecEval, hSpecSound⟩

  have hRootSound :
      ∀ r, r ∈ cert.roots →
        ∃ x,
          listGetOpt specR r = some x ∧
          x ≤ 0 :=
    roots_nonpos_sound D specI specR cert.roots hSpecSound hRoots

  refine ⟨(progR, specR), ?_, ?_⟩
  · exact ⟨hProgEval, hSpecEval, hRootSound⟩
  · intro traj hTraj
    rcases traj with ⟨progR', specR'⟩
    rcases hTraj with ⟨hProgEval', hSpecEval', _hRoots'⟩
    have hProgEq : progR = progR' :=
      evalProgFrom_unique D u [] cert.rows progR progR' hProgEval hProgEval'
    subst progR'
    have hSpecEq : specR = specR' :=
      evalSpecFrom_unique D progR [] cert.specRows specR specR' hSpecEval hSpecEval'
    subst specR'
    rfl

/-!
Boolean replay verifier.

This layer is intentionally thin:
  Bool replay/checking
  -> Prop-level AcceptProp
  -> semantic soundness by acceptProp_sound
-/

def replayRowBool (D : DPos) (ienv : IEnv D) : ProgRow D → Option (IEnc D)
  | ProgRow.input _ I =>
      some I

  | ProgRow.const k =>
      some (ISingleton D k)

  | ProgRow.add i j Icert =>
      match listGetOpt ienv i, listGetOpt ienv j with
      | some A, some B =>
          if _h : IBoundsEq Icert (Primitives.T_add D A B) then
            some Icert
          else
            none
      | _, _ => none

  | ProgRow.sub i j Icert =>
      match listGetOpt ienv i, listGetOpt ienv j with
      | some A, some B =>
          if h : IBoundsEq Icert (Primitives.T_sub D A B) then
            some Icert
          else
            none
      | _, _ => none

  | ProgRow.mul i j W Icert =>
      match listGetOpt ienv i, listGetOpt ienv j with
      | some A, some B =>
          if h :
              Primitives.CheckMul D A B W ∧
              Icert.lo = W.qf ∧
              Icert.hi = W.qc then
            some Icert
          else
            none
      | _, _ => none

  | ProgRow.inv i W Icert =>
      match listGetOpt ienv i with
      | some A =>
          if h :
              Primitives.CheckInv D A W ∧
              Icert.lo = W.ql ∧
              Icert.hi = W.qu then
            some Icert
          else
            none
      | none => none

  | ProgRow.sqrt i W Icert =>
      match listGetOpt ienv i with
      | some A =>
          if h :
              Primitives.CheckSqrt D A W ∧
              Icert.lo = W.p ∧
              Icert.hi = W.q then
            some Icert
          else
            none
      | none => none

  | ProgRow.relu i Icert =>
      match listGetOpt ienv i with
      | some A =>
          if h : IBoundsEq Icert (Primitives.T_relu D A) then
            some Icert
          else
            none
      | none => none

def replayProgBoolFrom (D : DPos) (ienv : IEnv D) :
    List (ProgRow D) → Option (IEnv D)
  | [] => some ienv
  | row :: rows =>
      match replayRowBool D ienv row with
      | none => none
      | some Iout => replayProgBoolFrom D (ienv ++ [Iout]) rows

def replayProgBool (D : DPos) (rows : List (ProgRow D)) : Option (IEnv D) :=
  replayProgBoolFrom D [] rows

def replaySpecRowBool
    (D : DPos)
    (progI : IEnv D)
    (specI : IEnv D) :
    SpecRow D → Option (IEnc D)
  | SpecRow.var v Icert =>
      match listGetOpt progI v with
      | some A =>
          if h : IBoundsEq Icert A then
            some Icert
          else
            none
      | none => none

  | SpecRow.const k =>
      some (ISingleton D k)

  | SpecRow.add i j Icert =>
      match listGetOpt specI i, listGetOpt specI j with
      | some A, some B =>
          if _h : IBoundsEq Icert (Primitives.T_add D A B) then
            some Icert
          else
            none
      | _, _ => none

  | SpecRow.sub i j Icert =>
      match listGetOpt specI i, listGetOpt specI j with
      | some A, some B =>
          if h : IBoundsEq Icert (Primitives.T_sub D A B) then
            some Icert
          else
            none
      | _, _ => none

  | SpecRow.mul i j W Icert =>
      match listGetOpt specI i, listGetOpt specI j with
      | some A, some B =>
          if h :
              Primitives.CheckMul D A B W ∧
              Icert.lo = W.qf ∧
              Icert.hi = W.qc then
            some Icert
          else
            none
      | _, _ => none

def replaySpecBoolFrom
    (D : DPos)
    (progI : IEnv D)
    (specI : IEnv D) :
    List (SpecRow D) → Option (IEnv D)
  | [] => some specI
  | row :: rows =>
      match replaySpecRowBool D progI specI row with
      | none => none
      | some Iout => replaySpecBoolFrom D progI (specI ++ [Iout]) rows

def replaySpecBool
    (D : DPos)
    (progI : IEnv D)
    (rows : List (SpecRow D)) : Option (IEnv D) :=
  replaySpecBoolFrom D progI [] rows

def rootsBool (D : DPos) (specI : IEnv D) : List Nat → Bool
  | [] => true
  | r :: roots =>
      match listGetOpt specI r with
      | some I =>
          decide (I.hi ≤ 0) && rootsBool D specI roots
      | none => false

def verifierBool (D : DPos) (cert : Cert D) : Bool :=
  match replayProgBool D cert.rows with
  | none => false
  | some progI =>
      match replaySpecBool D progI cert.specRows with
      | none => false
      | some specI =>
          rootsBool D specI cert.roots

def verifierDAGBool (D : DPos) (dcert : DAGCert D) : Bool :=
  verifierBool D (DAGCert.toCert D dcert)
/-!
Structural complexity bounds for replay verification.

The following cost model counts one bounded local replay/check step for each
program row, specification row, and root check.  It deliberately abstracts away
bit-complexity of integer arithmetic; that arithmetic cost is represented in
the paper by the external factor C(b).
-/

def replayProgBoolFromCost {D : DPos} : List (ProgRow D) → Nat
  | [] => 0
  | _ :: rows => 1 + replayProgBoolFromCost rows

def replaySpecBoolFromCost {D : DPos} : List (SpecRow D) → Nat
  | [] => 0
  | _ :: rows => 1 + replaySpecBoolFromCost rows

def rootsBoolCost : List Nat → Nat
  | [] => 0
  | _ :: roots => 1 + rootsBoolCost roots

def replayVerifierStructuralCost
    {D : DPos}
    (rows : List (ProgRow D))
    (specRows : List (SpecRow D)) : Nat :=
  replayProgBoolFromCost rows + replaySpecBoolFromCost specRows

def verifierBoolStructuralCost {D : DPos} (cert : Cert D) : Nat :=
  replayVerifierStructuralCost cert.rows cert.specRows + rootsBoolCost cert.roots

theorem replayProgBoolFromCost_eq_length
    {D : DPos}
    (rows : List (ProgRow D)) :
    replayProgBoolFromCost rows = rows.length := by
  induction rows with
  | nil => rfl
  | cons _ rows ih =>
      simpa [replayProgBoolFromCost, ih, Nat.add_comm]

theorem replaySpecBoolFromCost_eq_length
    {D : DPos}
    (rows : List (SpecRow D)) :
    replaySpecBoolFromCost rows = rows.length := by
  induction rows with
  | nil => rfl
  | cons _ rows ih =>
      simpa [replaySpecBoolFromCost, ih, Nat.add_comm]

theorem rootsBoolCost_eq_length
    (roots : List Nat) :
    rootsBoolCost roots = roots.length := by
  induction roots with
  | nil => rfl
  | cons _ roots ih =>
      simpa [rootsBoolCost, ih, Nat.add_comm]

theorem replayVerifierStructuralCost_eq_size
    {D : DPos}
    (rows : List (ProgRow D))
    (specRows : List (SpecRow D)) :
    replayVerifierStructuralCost rows specRows =
      rows.length + specRows.length := by
  simp [replayVerifierStructuralCost,
    replayProgBoolFromCost_eq_length,
    replaySpecBoolFromCost_eq_length]

theorem verifierBoolStructuralCost_eq_size
    {D : DPos}
    (cert : Cert D) :
    verifierBoolStructuralCost cert =
      cert.rows.length + cert.specRows.length + cert.roots.length := by
  simp [verifierBoolStructuralCost,
    replayVerifierStructuralCost_eq_size,
    rootsBoolCost_eq_length,
    Nat.add_assoc]

theorem replayVerifierStructuralCost_linear
    {D : DPos}
    (rows : List (ProgRow D))
    (specRows : List (SpecRow D)) :
    replayVerifierStructuralCost rows specRows ≤
      rows.length + specRows.length := by
  rw [replayVerifierStructuralCost_eq_size]

theorem verifierBoolStructuralCost_linear
    {D : DPos}
    (cert : Cert D) :
    verifierBoolStructuralCost cert ≤
      cert.rows.length + cert.specRows.length + cert.roots.length := by
  rw [verifierBoolStructuralCost_eq_size]


/-- Product-level implementation correspondence.
A product verifier is sound when it extensionally matches the Lean verifier. -/
def ProductVerifierMatches
    (D : DPos)
    (v : Cert D → Bool) : Prop :=
  ∀ cert, v cert = verifierBool D cert

theorem replayRowBool_sound
    (D : DPos)
    (ienv : IEnv D)
    (row : ProgRow D)
    (Iout : IEnc D) :
    replayRowBool D ienv row = some Iout →
    ReplayRow D ienv row Iout := by
  intro h
  cases row with
  | input q I =>
      simp [replayRowBool] at h
      subst Iout
      dsimp [ReplayRow]
      exact IBoundsEq_refl I

  | const k =>
      simp [replayRowBool] at h
      subst Iout
      dsimp [ReplayRow]
      exact IBoundsEq_refl (ISingleton D k)

  | add i j Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt ienv j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert : IBoundsEq Icert (Primitives.T_add D A B)
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplayRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB, hCert⟩
              · simp [hA, hB, hCert] at h

  | sub i j Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt ienv j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert : IBoundsEq Icert (Primitives.T_sub D A B)
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplayRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB, hCert⟩
              · simp [hA, hB, hCert] at h

  | mul i j W Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt ienv j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert :
                  Primitives.CheckMul D A B W ∧
                  Icert.lo = W.qf ∧
                  Icert.hi = W.qc
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplayRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB,
                  hCert.1, hCert.2.1, hCert.2.2⟩
              · simp [hA, hB, hCert] at h

  | inv i W Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          by_cases hCert :
              Primitives.CheckInv D A W ∧
              Icert.lo = W.ql ∧
              Icert.hi = W.qu
          · simp [hA, hCert] at h
            subst Iout
            dsimp [ReplayRow]
            exact ⟨IBoundsEq_refl Icert, A, hA,
              hCert.1, hCert.2.1, hCert.2.2⟩
          · simp [hA, hCert] at h

  | sqrt i W Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          by_cases hCert :
              Primitives.CheckSqrt D A W ∧
              Icert.lo = W.p ∧
              Icert.hi = W.q
          · simp [hA, hCert] at h
            subst Iout
            dsimp [ReplayRow]
            exact ⟨IBoundsEq_refl Icert, A, hA,
              hCert.1, hCert.2.1, hCert.2.2⟩
          · simp [hA, hCert] at h

  | relu i Icert =>
      dsimp [replayRowBool] at h
      cases hA : listGetOpt ienv i with
      | none =>
          simp [hA] at h
      | some A =>
          by_cases hCert : IBoundsEq Icert (Primitives.T_relu D A)
          · simp [hA, hCert] at h
            subst Iout
            dsimp [ReplayRow]
            exact ⟨IBoundsEq_refl Icert, A, hA, hCert⟩
          · simp [hA, hCert] at h

theorem replayProgBoolFrom_sound
    (D : DPos)
    (ienv out : IEnv D)
    (rows : List (ProgRow D)) :
    replayProgBoolFrom D ienv rows = some out →
    ReplayProgFrom D ienv rows out := by
  induction rows generalizing ienv out with
  | nil =>
      intro h
      simp [replayProgBoolFrom] at h
      subst out
      exact ReplayProgFrom.nil ienv

  | cons row rows ih =>
      intro h
      dsimp [replayProgBoolFrom] at h
      cases hRow : replayRowBool D ienv row with
      | none =>
          simp [hRow] at h
      | some Iout =>
          have hRowSound :
              ReplayRow D ienv row Iout :=
            replayRowBool_sound D ienv row Iout hRow

          have hRest :
              ReplayProgFrom D (ienv ++ [Iout]) rows out :=
            ih (ienv := ienv ++ [Iout]) (out := out) (by
              simpa [hRow] using h)

          exact ReplayProgFrom.cons ienv out row rows Iout hRowSound hRest

theorem replayProgBool_sound
    (D : DPos)
    (rows : List (ProgRow D))
    (progI : IEnv D) :
    replayProgBool D rows = some progI →
    ReplayProgFrom D [] rows progI := by
  intro h
  exact replayProgBoolFrom_sound D [] progI rows h

theorem replaySpecRowBool_sound
    (D : DPos)
    (progI specI : IEnv D)
    (row : SpecRow D)
    (Iout : IEnc D) :
    replaySpecRowBool D progI specI row = some Iout →
    ReplaySpecRow D progI specI row Iout := by
  intro h
  cases row with
  | var v Icert =>
      dsimp [replaySpecRowBool] at h
      cases hA : listGetOpt progI v with
      | none =>
          simp [hA] at h
      | some A =>
          by_cases hCert : IBoundsEq Icert A
          · simp [hA, hCert] at h
            subst Iout
            dsimp [ReplaySpecRow]
            exact ⟨IBoundsEq_refl Icert, A, hA, hCert⟩
          · simp [hA, hCert] at h

  | const k =>
      simp [replaySpecRowBool] at h
      subst Iout
      dsimp [ReplaySpecRow]
      exact IBoundsEq_refl (ISingleton D k)

  | add i j Icert =>
      dsimp [replaySpecRowBool] at h
      cases hA : listGetOpt specI i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt specI j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert : IBoundsEq Icert (Primitives.T_add D A B)
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplaySpecRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB, hCert⟩
              · simp [hA, hB, hCert] at h

  | sub i j Icert =>
      dsimp [replaySpecRowBool] at h
      cases hA : listGetOpt specI i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt specI j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert : IBoundsEq Icert (Primitives.T_sub D A B)
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplaySpecRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB, hCert⟩
              · simp [hA, hB, hCert] at h

  | mul i j W Icert =>
      dsimp [replaySpecRowBool] at h
      cases hA : listGetOpt specI i with
      | none =>
          simp [hA] at h
      | some A =>
          cases hB : listGetOpt specI j with
          | none =>
              simp [hA, hB] at h
          | some B =>
              by_cases hCert :
                  Primitives.CheckMul D A B W ∧
                  Icert.lo = W.qf ∧
                  Icert.hi = W.qc
              · simp [hA, hB, hCert] at h
                subst Iout
                dsimp [ReplaySpecRow]
                exact ⟨IBoundsEq_refl Icert, A, B, hA, hB,
                  hCert.1, hCert.2.1, hCert.2.2⟩
              · simp [hA, hB, hCert] at h

theorem replaySpecBoolFrom_sound
    (D : DPos)
    (progI specI out : IEnv D)
    (rows : List (SpecRow D)) :
    replaySpecBoolFrom D progI specI rows = some out →
    ReplaySpecFrom D progI specI rows out := by
  induction rows generalizing specI out with
  | nil =>
      intro h
      simp [replaySpecBoolFrom] at h
      subst out
      exact ReplaySpecFrom.nil specI

  | cons row rows ih =>
      intro h
      dsimp [replaySpecBoolFrom] at h
      cases hRow : replaySpecRowBool D progI specI row with
      | none =>
          simp [hRow] at h
      | some Iout =>
          have hRowSound :
              ReplaySpecRow D progI specI row Iout :=
            replaySpecRowBool_sound D progI specI row Iout hRow

          have hRest :
              ReplaySpecFrom D progI (specI ++ [Iout]) rows out :=
            ih (specI := specI ++ [Iout]) (out := out) (by
              simpa [hRow] using h)

          exact ReplaySpecFrom.cons specI out row rows Iout hRowSound hRest

theorem replaySpecBool_sound
    (D : DPos)
    (progI : IEnv D)
    (rows : List (SpecRow D))
    (specI : IEnv D) :
    replaySpecBool D progI rows = some specI →
    ReplaySpecFrom D progI [] rows specI := by
  intro h
  exact replaySpecBoolFrom_sound D progI [] specI rows h

theorem rootsBool_sound
    (D : DPos)
    (specI : IEnv D)
    (roots : List Nat) :
    rootsBool D specI roots = true →
    RootUpperOK D specI roots := by
  induction roots with
  | nil =>
      intro _ r hr
      cases hr

  | cons r roots ih =>
      intro h q hq
      dsimp [rootsBool] at h
      cases hI : listGetOpt specI r with
      | none =>
          simp [hI] at h

      | some I =>
          cases hDec : decide (I.hi ≤ 0) with
          | false =>
              simp [hI, hDec] at h

          | true =>
              cases hTail : rootsBool D specI roots with
              | false =>
                  simp [hI, hDec, hTail] at h

              | true =>
                  have hHi : I.hi ≤ 0 := by
                    exact of_decide_eq_true hDec

                  simp at hq
                  rcases hq with hqr | hqtail
                  · subst q
                    exact ⟨I, hI, hHi⟩
                  · exact ih hTail q hqtail

theorem verifierBool_acceptProp
    (D : DPos)
    (cert : Cert D) :
    verifierBool D cert = true →
    AcceptProp D cert := by
  intro h
  unfold verifierBool at h
  cases hProg : replayProgBool D cert.rows with
  | none =>
      simp [hProg] at h
  | some progI =>
      cases hSpec : replaySpecBool D progI cert.specRows with
      | none =>
          simp [hProg, hSpec] at h
      | some specI =>
          have hRootsBool : rootsBool D specI cert.roots = true := by
            simpa [hProg, hSpec] using h

          have hProgSound :
              ReplayProgFrom D [] cert.rows progI :=
            replayProgBool_sound D cert.rows progI hProg

          have hSpecSound :
              ReplaySpecFrom D progI [] cert.specRows specI :=
            replaySpecBool_sound D progI cert.specRows specI hSpec

          have hRoots :
              RootUpperOK D specI cert.roots :=
            rootsBool_sound D specI cert.roots hRootsBool

          exact ⟨progI, specI, hProgSound, hSpecSound, hRoots⟩

/-- Boolean verifier acceptance determines a unique concrete real trajectory. -/
theorem verifierBool_sound_unique
    (D : DPos)
    (cert : Cert D) :
    verifierBool D cert = true →
    ∀ u : InputOracle,
      RowsInputAdmissible D u cert.rows →
      ∃! traj : REnv × REnv,
        EvalProgFrom D u [] cert.rows traj.1 ∧
        EvalSpecFrom D traj.1 [] cert.specRows traj.2 ∧
        (∀ r, r ∈ cert.roots →
          ∃ x,
            listGetOpt traj.2 r = some x ∧
            x ≤ 0) := by
  intro h
  exact acceptProp_sound_unique D cert (verifierBool_acceptProp D cert h)

theorem verifierBool_sound
    (D : DPos)
    (cert : Cert D) :
    verifierBool D cert = true →
    SemanticValid D cert.rows cert.specRows cert.roots := by
  intro h
  exact acceptProp_sound D cert (verifierBool_acceptProp D cert h)

theorem verifierDAGBool_sound
    (D : DPos)
    (dcert : DAGCert D) :
    verifierDAGBool D dcert = true →
    SemanticValid D
      (compileProgDAG D dcert.progDag)
      (compileSpecDAG D (compileProgDAG D dcert.progDag).length dcert.specDag)
      dcert.roots := by
  intro h
  have hCert : verifierBool D (DAGCert.toCert D dcert) = true := by
    simpa [verifierDAGBool] using h
  simpa [DAGCert.toCert]
    using verifierBool_sound D (DAGCert.toCert D dcert) hCert

/-- Accepted DAG certificates are directly semantically valid at the DAG level. -/
theorem verifierDAGBool_direct_sound
    (D : DPos)
    (dcert : DAGCert D) :
    verifierDAGBool D dcert = true →
    DAGSemanticValid D dcert := by
  intro h
  have hCompiled :
      CompiledDAGSemanticValid D dcert := by
    simpa [CompiledDAGSemanticValid]
      using verifierDAGBool_sound D dcert h
  exact dagCompiler_complete D dcert hCompiled


/-- End-to-end soundness for DAG certificates.

A DAG certificate accepted by the Lean verifier is semantically valid
after compilation to the replay-verifier certificate format. -/
theorem dagCert_end_to_end_sound
    (D : DPos)
    (dcert : DAGCert D) :
    verifierBool D (DAGCert.toCert D dcert) = true →
    SemanticValid D
      (compileProgDAG D dcert.progDag)
      (compileSpecDAG D (compileProgDAG D dcert.progDag).length dcert.specDag)
      dcert.roots := by
  intro h
  have hDAG : verifierDAGBool D dcert = true := by
    simpa [verifierDAGBool] using h
  exact verifierDAGBool_sound D dcert hDAG

theorem productVerifier_sound
    (D : DPos)
    (v : Cert D → Bool)
    (cert : Cert D) :
    ProductVerifierMatches D v →
    v cert = true →
    SemanticValid D cert.rows cert.specRows cert.roots := by
  intro hMatch hv
  have hLean : verifierBool D cert = true := by
    rw [← hMatch cert]
    exact hv
  exact verifierBool_sound D cert hLean

end ReplayCore

end

#print axioms ADIC.tau_preserves
#print axioms ADIC.tau_truth
#print axioms ADIC.ReplayCore.dagCompiler_correct
#print axioms ADIC.ReplayCore.dagCompiler_sound
#print axioms ADIC.ReplayCore.dagCompiler_complete
#print axioms ADIC.ReplayCore.acceptProp_sound
#print axioms ADIC.ReplayCore.acceptProp_sound_unique
#print axioms ADIC.ReplayCore.verifierBool_acceptProp
#print axioms ADIC.ReplayCore.verifierBool_sound
#print axioms ADIC.ReplayCore.verifierBool_sound_unique
#print axioms ADIC.ReplayCore.verifierDAGBool_sound
#print axioms ADIC.ReplayCore.verifierDAGBool_direct_sound
#print axioms ADIC.ReplayCore.dagCert_end_to_end_sound
#print axioms ADIC.ReplayCore.productVerifier_sound

end ADIC
