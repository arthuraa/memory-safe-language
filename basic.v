Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.choice.
Require Import Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg MathComp.bigop.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.

Local Open Scope fset_scope.

Definition int_partOrdMixin :=
  (@PartOrdMixin int <=%R (@Num.Theory.lerr _) (@Num.Theory.ler_trans _)
                          (@Num.Theory.ler_anti _))%R.

Canonical int_partOrdType :=
  Eval hnf in PartOrdType int int_partOrdMixin.

Definition int_ordMixin :=
  @OrdMixin [partOrdType of int] (@Num.Theory.ler_total _).

Canonical int_ordType :=
  Eval hnf in OrdType int int_ordMixin.

Canonical int_nominalType :=
  Eval hnf in [nominalType for int by //].
Canonical int_trivialNominalType :=
  Eval hnf in [trivialNominalType for int].

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Inductive expr :=
| Var of string
| Num of int
| Binop of binop & expr & expr
| ENil
| Cast of expr.

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

(** Type of pointers. [name] corresponds to an atom, in the nominal
set sense. *)
Definition ptr : Type := (name * int)%type.

Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of ptr
| VNil.

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
Definition value_choiceMixin := CanChoiceMixin sum_of_valueK.
Canonical value_choiceType := Eval hnf in ChoiceType value value_choiceMixin.
Definition value_partOrdMixin := CanPartOrdMixin sum_of_valueK.
Canonical value_partOrdType :=
  Eval hnf in PartOrdType value value_partOrdMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin := BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Lemma renamevE pm v :
  rename pm v =
  match v with
  | VBool b => VBool b
  | VNum n => VNum n
  | VPtr p => VPtr (rename pm p)
  | VNil => VNil
  end.
Proof. by case: v. Qed.

Lemma namesvE v :
  names v =
  match v with
  | VPtr p => fset1 p.1
  | _ => fset0
  end.
Proof.
case: v=> [b|n|[i n]|] //=.
rewrite /names /= /bij_names /=; do ![rewrite /names /=].
by rewrite /prod_names fsetU0.
Qed.

Definition locals := {partmap string -> value}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition init_block h b n :=
  unionm (mkpartmapf (fun _ => VNum 0) [seq (b, Posz i) | i <- iota 0 n]) h.

Definition alloc_fun ls h n :=
  locked (let b := fresh (names (ls, h)) in (b, init_block h b n)).

Definition free_fun h i :=
  locked
  (if i \in domm (currym h) then
     Some (filterm (fun p _ => p.1 != i) h)
   else None).

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
  end%R.

(** Function [eval_expr] computes the value of an expression [e] given
a local store [ls]. It takes an additional argument [safe] which
determines how the cast operator is interpreted: when [safe = true],
cast is just the identity; when [safe = false], cast converts the
block identifier to an integer. *)

Fixpoint eval_expr safe ls e :=
  match e with
  | Var x => odflt VNil (ls x)
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr safe ls e1) (eval_expr safe ls e2)
  | ENil => VNil
  | Cast e =>
    let v := eval_expr safe ls e in
    if safe then v
    else if eval_expr safe ls e is VPtr p then VNum (val p.1) else VNil
  end.

Section Result.

Variable T : Type.

(** Type of results of computations. [Done x] indicates that a
computation successfully terminated, returning [x] as a
result. [Error] indicates that an error occurred. [NotYet] indicates
that the computation ran for too many steps and couldn't complete. *)

Inductive result :=
| Done of T
| Error
| NotYet.

Definition sum_of_result r :=
  match r with
  | Done x => inl x
  | Error => inr true
  | NotYet => inr false
  end.

Definition result_of_sum r :=
  match r with
  | inl x => Done x
  | inr true => Error
  | inr false => NotYet
  end.

Lemma sum_of_resultK : cancel sum_of_result result_of_sum.
Proof. by case. Qed.
Lemma result_of_sumK : cancel result_of_sum sum_of_result.
Proof. by do ![case=>//]. Qed.

Definition result_of_option r :=
  if r is Some x then Done x else Error.

End Result.

Arguments Error {_}.
Arguments NotYet {_}.

Definition result_eqMixin (T : eqType) :=
  CanEqMixin (@sum_of_resultK T).
Canonical result_eqType (T : eqType) :=
  Eval hnf in EqType (result T) (result_eqMixin T).
Definition result_choiceMixin (T : choiceType) :=
  CanChoiceMixin (@sum_of_resultK T).
Canonical result_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (result T) (result_choiceMixin T).
Definition result_partOrdMixin (T : partOrdType) :=
  CanPartOrdMixin (@sum_of_resultK T).
Canonical result_partOrdType (T : partOrdType) :=
  Eval hnf in PartOrdType (result T) (result_partOrdMixin T).
Definition result_ordMixin (T : ordType) :=
  CanOrdMixin (@sum_of_resultK T).
Canonical result_ordType (T : ordType) :=
  Eval hnf in OrdType (result T) (result_ordMixin T).
Definition result_nominalMixin (T : nominalType) :=
  BijNominalMixin (@sum_of_resultK T) (@result_of_sumK T).
Canonical result_nominalType (T : nominalType) :=
  Eval hnf in NominalType (result T) (result_nominalMixin T).

Lemma renamerE (T : nominalType) pm (r : result T) :
  rename pm r =
  match r with
  | Done x => Done (rename pm x)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: r. Qed.

Lemma result_of_option_omap T S f x :
  result_of_option (@omap T S f x) =
  match result_of_option x with
  | Done x => Done (f x)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: x. Qed.

(** Parametric semantics for our language. The [sem] record lists the
basic primitives we need to define the semantics over some type [T],
which are combined by the [eval_com] function below to compute the
effect of a command on a piece of state. *)

CoInductive sem T := Sem {
  assn : string -> expr -> T -> T;
  load : string -> expr -> T -> option T;
  store : expr -> expr -> T -> option T;
  alloc : string -> expr -> T -> option T;
  free : expr -> T -> option T;
  eval_cond : expr -> T -> option bool
}.

Fixpoint eval_com T (S : sem T) s c k :=
  if k is S k' then
    match c with
    | Assn x e => Done (assn S x e s)

    | Load x e => result_of_option (load S x e s)

    | Store e e' => result_of_option (store S e e' s)

    | Alloc x e => result_of_option (alloc S x e s)

    | Free e => result_of_option (free S e s)

    | Skip => Done s

    | Seq c1 c2 =>
      let r1 := eval_com S s c1 k' in
      if r1 is Done s' then
        eval_com S s' c2 k'
      else r1

    | If e ct ce =>
      if eval_cond S e s is Some b then
        eval_com S s (if b then ct else ce) k'
      else Error

    | While e c =>
      if eval_cond S e s is Some b then
        eval_com S s (if b then Seq c (While e c) else Skip) k'
      else Error
    end
  else NotYet.

(** The semantics defined as a function is consistent, in the sense
that increasing the maximum number of steps it can run for can only
cause it to produce a better result. *)

Definition refine_result (T : eqType) (r1 r2 : result T) :=
  (r1 == NotYet) || (r1 == r2).

Lemma eval_com_leq (T : eqType) (S : sem T) s c k k' :
  k <= k' ->
  refine_result (eval_com S s c k) (eval_com S s c k').
Proof.
move=> Pk; elim: k' k Pk s c => [|k' IH] [|k] // /IH {IH} IH s.
rewrite /refine_result.
case=> [x e|x e|e e'|x e|e| |c1 c2|e ct ce|e c] /=; try by rewrite eqxx ?orbT.
- case/orP: (IH s c1) => [/eqP -> //|/eqP ->].
  case: (eval_com _ _ c1 _) => [s'| |] //=.
  by eauto.
- by case: (eval_cond S e s) => [b|] //=; eauto.
by case: (eval_cond S e s) => [b|] //=; eauto.
Qed.

(** Basic, unstructured semantics for our language. *)

Definition basic_sem safe : sem (locals * heap) := {|
  assn x e s :=
    (setm s.1 x (eval_expr safe s.1 e), s.2);

  load x e := fun s : locals * heap =>
    if eval_expr safe s.1 e is VPtr p then
      if s.2 p is Some v then Some (setm s.1 x v, s.2)
      else None
    else None;

  store e e' s :=
    if eval_expr safe s.1 e is VPtr p then
      if updm s.2 p (eval_expr safe s.1 e') is Some h' then Some (s.1, h')
      else None
    else None;

  alloc x e s :=
    if eval_expr safe s.1 e is VNum (Posz n) then
      let res := alloc_fun s.1 s.2 n in
      Some (setm s.1 x (VPtr (res.1, 0 : int)), res.2)
    else None;

  free e s :=
    if eval_expr safe s.1 e is VPtr p then
      if p.2 == 0 then
        if free_fun s.2 p.1 is Some h' then Some (s.1, h')
        else None
      else None
    else None;

  eval_cond e s :=
    if eval_expr safe s.1 e is VBool b then Some b
    else None

|}.

(** Free variables that occur in a command or expression. *)

Fixpoint vars_e e :=
  match e with
  | Var x => fset1 x
  | Num _ => fset0
  | Binop _ e1 e2 => vars_e e1 :|: vars_e e2
  | ENil => fset0
  | Cast e => vars_e e
  end.

Fixpoint vars_c c :=
  match c with
  | Assn x e => x |: vars_e e
  | Load x e => x |: vars_e e
  | Store e e' => vars_e e :|: vars_e e'
  | Alloc x e => x |: vars_e e
  | Free e => vars_e e
  | Skip => fset0
  | Seq c1 c2 => vars_c c1 :|: vars_c c2
  | If e ct ce => vars_e e :|: vars_c ct :|: vars_c ce
  | While e c => vars_e e :|: vars_c c
  end.

(** Basic lemmas about the semantics *)

Lemma eval_expr_unionm safe ls1 ls2 e :
  fsubset (vars_e e) (domm ls1) ->
  eval_expr safe (unionm ls1 ls2) e =
  eval_expr safe ls1 e.
Proof.
elim: e => [x|n|b e1 IH1 e2 IH2| |e IH] //=.
- by rewrite fsub1set unionmE => /dommP [v ->].
- by rewrite fsubUset=> /andP [/IH1 {IH1} -> /IH2 {IH2} ->].
by case: safe IH=> // IH sub; rewrite IH.
Qed.

Lemma eval_binop_names b v1 v2 :
  fsubset (names (eval_binop b v1 v2)) (names (v1, v2)).
Proof.
case: b v1 v2=> [] [b1|n1|p1|] [b2|n2|p2|] //=; try by rewrite fsub0set.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
by rewrite fsubsetU //= !namesvE fsubsetxx.
Qed.

Lemma eval_expr_names safe ls e :
  fsubset (names (eval_expr safe ls e)) (names ls).
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2| |e IH] //=; try by rewrite fsub0set.
- case get_x: (ls x) => [[b|n|p|]|] //=; try by rewrite fsub0set.
  apply/fsubsetP=> i; rewrite namesvE => /fset1P -> {i}.
  apply/namesmP; eapply PMFreeNamesVal; eauto.
  by rewrite namesvE; apply/namesnP.
- by rewrite (fsubset_trans (eval_binop_names b _ _)) // fsubUset IH1 IH2.
case: safe IH=> //.
by case: (eval_expr _ _ _)=> [b|n|p|]; rewrite fsub0set.
Qed.

Lemma names_init_block h i n :
  fsubset (names (init_block h i n)) (i |: names h).
Proof.
rewrite (fsubset_trans (namesm_union _ _)) // fsetU1E fsetSU //.
apply/fsubsetP=> i'; case/namesmP=> [p v|p v]; rewrite mkpartmapfE;
case: ifP=> // /mapP [n' Pn'].
  by move=> -> {p} _; rewrite in_fsetU in_fset0 orbF.
by move=> _ [<-].
Qed.

Lemma init_block_unionm h1 h2 i n :
  init_block (unionm h1 h2) i n = unionm (init_block h1 i n) h2.
Proof. by rewrite /init_block unionmA. Qed.

Lemma fdisjoint_names_domm h1 h2 :
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  fdisjoint (domm h1) (domm h2).
Proof.
move=> /fdisjointP dis; apply/fdisjointP=> p Pp.
have /dis Pi: p.1 \in names (domm h1).
  by apply/namesfsP; exists p=> //=; apply/namesnP.
apply: contra Pi=> Pi; apply/namesfsP; exists p=> //.
by apply/namesnP.
Qed.

End Basic.

Arguments Error {_}.
Arguments NotYet {_}.
