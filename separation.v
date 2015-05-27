Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.nominal.
Require Import CoqUtils.string.

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

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Inductive loc : Type :=
| Var of string
| Deref of expr

with expr : Type :=
| Num of int
| Loc of loc
| Binop of binop & expr & expr
| Alloc of expr
| Skip
| Seq of expr & expr
| Let of string & expr & expr
| Ass of loc & expr
| If of expr & expr & expr
| While of expr & expr.

Definition ptr : Type := (name * int)%type.

Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of name * int.

Definition sum_of_value v :=
  match v with
  | VBool b => inl b
  | VNum n => inr (inl n)
  | VPtr p => inr (inr p)
  end.

Definition value_of_sum v :=
  match v with
  | inl b => VBool b
  | inr (inl n) => VNum n
  | inr (inr p) => VPtr p
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.
Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. by do 2!case. Qed.
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

Definition locals := {partmap string -> name}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition alloc h n :=
  let b := fresh (names h) in
  (b, unionm (mkpartmap [seq ((b, Posz i), VNum 0) | i <- iota 0 n]) h).

Definition free h b :=
  filterm (fun p _ => p.1 != b) h.

Definition eval_binop b v1 v2 :=
  match b, v1, v2 with
  | Add, VNum n1, VNum n2 => Some (VNum (n1 + n2))
  | Add, VPtr p, VNum n
  | Add, VNum n, VPtr p => Some (VPtr (p.1, p.2 + n))
  | Add, _, _ => None
  | Sub, VNum n1, VNum n2 => Some (VNum (n1 - n2))
  | Sub, VPtr p, VNum n => Some (VPtr (p.1, p.2 - n))
  | Sub, _, _ => None
  | Mul, VNum n1, VNum n2 => Some (VNum (n1 * n2))
  | Mul, _, _ => None
  | Eq, _, _ => Some (VBool (v1 == v2))
  | Leq, VNum n1, VNum n2 => Some (VBool (n1 <= n2))
  | Leq, _, _ => None
  | And, VBool b1, VBool b2 => Some (VBool (b1 && b2))
  | And, _, _ => None
  | Or, VBool b1, VBool b2 => Some (VBool (b1 || b2))
  | Or, _, _ => None
  end.

Inductive eval_loc ls h : loc -> ptr -> heap -> Prop :=
| EVar v b of ls v = Some b : eval_loc ls h (Var v) (b, 0) h

| EDeref e p h'
  of eval_expr ls h e (VPtr p) h'
  :  eval_loc  ls h (Deref e) p h'

with eval_expr ls h : expr -> value -> heap -> Prop :=
| ENum n : eval_expr ls h (Num n) (VNum n) h

| ELoc l p v h'
  of eval_loc ls h l p h'
  &  h' p = Some v
  :  eval_expr ls h (Loc l) v h'

| EBinop b e1 v1 h' e2 v2 h'' v
  of eval_expr ls h e1 v1 h'
  &  eval_expr ls h' e2 v2 h''
  &  eval_binop b v1 v2 = Some v
  :  eval_expr ls h (Binop b e1 e2) v h''

| EAlloc e n h'
  of eval_expr ls h e (VNum (Posz n)) h'
  :  eval_expr ls h (Alloc e) (VPtr ((alloc h' n).1, 0)) (alloc h' n).2

| ESkip : eval_expr ls h Skip (VNum 0) h

| ESeq e1 v1 h' e2 v2 h''
  of eval_expr ls h e1 v1 h'
  &  eval_expr ls h e2 v2 h''
  :  eval_expr ls h (Seq e1 e2) (VNum 0) h''

| ELet x e1 v1 h' b h'' e2 v2 h'''
  of eval_expr ls h e1 v1 h'
  &  alloc h' 1 = (b, h'')
  &  eval_expr (setm ls x b) h'' e2 v2 h'''
  :  eval_expr ls h (Let x e1 e2) v2 (free h''' b)

| EAss l p h' e v h'' h'''
  of eval_loc ls h l p h'
  &  eval_expr ls h e v h''
  &  updm h'' p v = Some h'''
  :  eval_expr ls h (Ass l e) v h'''

| EIf e1 b h' e2 e3 v h''
  of eval_expr ls h e1 (VBool b) h'
  &  eval_expr ls h (if b then e2 else e3) v h''
  :  eval_expr ls h (If e1 e2 e3) v h''

| EWhileEnd e1 h' e2
  of eval_expr ls h e1 (VBool false) h'
  :  eval_expr ls h (While e1 e2) (VNum 0) h'

| EWhileLoop e1 h' e2 v h'' v' h'''
  of eval_expr ls h   e1 (VBool true) h'
  &  eval_expr ls h'  e2 v h''
  &  eval_expr ls h'' (While e1 e2) v' h'''
  :  eval_expr ls h   (While e1 e2) v' h'''.

End Def.
