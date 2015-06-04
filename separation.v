Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.nominal.
Require Import CoqUtils.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Local Open Scope ring_scope.

Definition int_partOrdMixin :=
  @PartOrdMixin int <=%R (@Num.Theory.lerr _) (@Num.Theory.ler_trans _)
                         (@Num.Theory.ler_anti _).

Canonical int_partOrdType :=
  Eval hnf in PartOrdType int int_partOrdMixin.

Definition int_ordMixin :=
  @OrdMixin [partOrdType of int] (@Num.Theory.ler_total _).

Canonical int_ordType :=
  Eval hnf in OrdType int int_ordMixin.

Definition int_nominalMixin := TrivialNominalMixin int.
Canonical int_nominalType := Eval hnf in NominalType int int_nominalMixin.

Definition string_nominalMixin := TrivialNominalMixin string.
Canonical string_nominalType :=
  Eval hnf in NominalType string string_nominalMixin.

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Inductive expr :=
| Var of string
| Num of int
| Binop of binop & expr & expr
| ENil.

Inductive com : Type :=
| Assn of string & expr
| Load of string & expr
| Store of expr & expr
| Alloc of string & expr
| Free of expr
| Skip
| Seq of com & com
| If of expr & com & com
| While of expr & com.

Definition ptr : Type := (name * int)%type.

Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of ptr
| VNil.

Definition is_vnat v :=
  if v is VNum (Posz _) then true else false.

Definition sum_of_value v :=
  match v with
  | VBool b => inl b
  | VNum n => inr (inl n)
  | VPtr p => inr (inr (inl p))
  | VNil => inr (inr (inr tt))
  end.

Definition value_of_sum v :=
  match v with
  | inl b => VBool b
  | inr (inl n) => VNum n
  | inr (inr (inl p)) => VPtr p
  | inr (inr (inr tt)) => VNil
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.
Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. by do ![case=>//]. Qed.
Definition value_eqMixin := CanEqMixin sum_of_valueK.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.
Definition value_partOrdMixin := CanPartOrdMixin sum_of_valueK.
Canonical value_partOrdType :=
  Eval hnf in PartOrdType value value_partOrdMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin := BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Definition locals := {partmap string -> value}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition alloc h n :=
  let b := fresh (names h) in
  (b, unionm (mkpartmap [seq ((b, Posz i), VNum 0) | i <- iota 0 n]) h).

Definition free h b :=
  filterm (fun p _ => p.1 != b) h.

Definition eval_binop b v1 v2 :=
  match b, v1, v2 with
  | Add, VNum n1, VNum n2 => VNum (n1 + n2)
  | Add, VPtr p, VNum n
  | Add, VNum n, VPtr p => VPtr (p.1, p.2 + n)
  | Add, _, _ => VNil
  | Sub, VNum n1, VNum n2 => VNum (n1 - n2)
  | Sub, VPtr p, VNum n => VPtr (p.1, p.2 - n)
  | Sub, _, _ => VNil
  | Mul, VNum n1, VNum n2 => VNum (n1 * n2)
  | Mul, _, _ => VNil
  | Eq, _, _ => VBool (v1 == v2)
  | Leq, VNum n1, VNum n2 => VBool (n1 <= n2)
  | Leq, _, _ => VNil
  | And, VBool b1, VBool b2 => VBool (b1 && b2)
  | And, _, _ => VNil
  | Or, VBool b1, VBool b2 => VBool (b1 || b2)
  | Or, _, _ => VNil
  end.

Fixpoint eval_expr ls e :=
  match e with
  | Var x => odflt VNil (ls x)
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr ls e1) (eval_expr ls e2)
  | ENil => VNil
  end.

Inductive result :=
| Done of locals & heap
| Error
| NotYet.

Definition sum_of_result r :=
  match r with
  | Done ls h => inl (ls, h)
  | Error => inr true
  | NotYet => inr false
  end.

Definition result_of_sum r :=
  match r with
  | inl (ls, h) => Done ls h
  | inr true => Error
  | inr false => NotYet
  end.

Lemma sum_of_resultK : cancel sum_of_result result_of_sum.
Proof. by case. Qed.
Lemma result_of_sumK : cancel result_of_sum sum_of_result.
Proof. by do ![case=>//]. Qed.

Definition result_eqMixin := CanEqMixin sum_of_resultK.
Canonical result_eqType := Eval hnf in EqType result result_eqMixin.
Definition result_partOrdMixin := CanPartOrdMixin sum_of_resultK.
Canonical result_partOrdType :=
  Eval hnf in PartOrdType result result_partOrdMixin.
Definition result_ordMixin := CanOrdMixin sum_of_resultK.
Canonical result_ordType := Eval hnf in OrdType result result_ordMixin.
Definition result_nominalMixin := BijNominalMixin sum_of_resultK result_of_sumK.
Canonical result_nominalType :=
  Eval hnf in NominalType result result_nominalMixin.

Fixpoint eval_com ls h c k :=
  if k is S k' then
    match c with
    | Assn x e =>
      Done (setm ls x (eval_expr ls e)) h

    | Load x e =>
      if eval_expr ls e is VPtr p then
        if h p is Some v then Done (setm ls x v) h
        else Error
      else Error

    | Store e e' =>
      if eval_expr ls e is VPtr p then
        if updm h p (eval_expr ls e') is Some h' then Done ls h'
        else Error
      else Error

    | Alloc x e =>
      if eval_expr ls e is VNum (Posz n) then
        let: (i, h') := alloc h n in
        Done (setm ls x (VPtr (i, 0))) h'
      else Error

    | Free e =>
      if eval_expr ls e is VPtr p then
        if fpick [pred p' | p'.1 == p.1] (domm h) then
          Done ls (free h p.1)
        else Error
      else Error

    | Skip => Done ls h

    | Seq c1 c2 =>
      let r1 := eval_com ls h c1 k' in
      if r1 is Done ls' h' then
        eval_com ls' h' c2 k'
      else r1

    | If e ct ce =>
      if eval_expr ls e is VBool b then
        eval_com ls h (if b then ct else ce) k'
      else Error

    | While e c =>
      if eval_expr ls e is VBool b then
        eval_com ls h (if b then While e c else Skip) k'
      else Error
    end
  else NotYet.

Definition refine_result r1 r2 :=
  (r1 == NotYet) || (r1 == r2).

Lemma eval_com_leq ls h c k k' :
  (k <= k')%N ->
  refine_result (eval_com ls h c k) (eval_com ls h c k').
Proof.
move=> Pk; elim: k' k Pk ls h c => [|k' IH] [|k] // /IH {IH} IH ls h.
rewrite /refine_result.
case=> [x e|x e|e e'|x e|e| |c1 c2|e ct ce|e c] /=; try by rewrite eqxx ?orbT.
- case/orP: (IH ls h c1) => [/eqP -> //|/eqP ->].
  case: (eval_com _ _ c1 _) => [ls' h'| |] //=.
  by eauto.
- by case: (eval_expr ls e) => [b| | |] //=; eauto.
by case: (eval_expr ls e) => [b| | |] //=; eauto.
Qed.

End Def.
