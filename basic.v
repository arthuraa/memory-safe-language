Require Import Coq.Strings.String.

From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype choice seq ssrnum ssrint ssralg bigop.

From deriving Require Import deriving.
From extructures Require Import ord fset fmap fperm.

From CoqUtils Require Import nominal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Basic.

Local Open Scope fset_scope.

Definition int_ordMixin :=
  @PcanOrdMixin int _ _ _ pickleK.

Canonical int_ordType :=
  Eval hnf in OrdType int int_ordMixin.
Canonical int_nominalType :=
  Eval hnf in [nominalType for int by //].
Canonical int_trivialNominalType :=
  Eval hnf in [trivialNominalType for int].

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Definition nat_of_binop b :=
  match b with
  | Add => 0
  | Mul => 1
  | Sub => 2
  | Eq  => 3
  | Leq => 4
  | And => 5
  | Or  => 6
  end.

Definition binop_of_nat n :=
  match n with
  | 0 => Add
  | 1 => Mul
  | 2 => Sub
  | 3 => Eq
  | 4 => Leq
  | 5 => And
  | _ => Or
  end.

Lemma nat_of_binopK : cancel nat_of_binop binop_of_nat.
Proof. by case. Qed.

Definition binop_eqMixin := CanEqMixin nat_of_binopK.
Canonical binop_eqType := Eval hnf in EqType binop binop_eqMixin.
Definition binop_choiceMixin := CanChoiceMixin nat_of_binopK.
Canonical binop_choiceType := Eval hnf in ChoiceType binop binop_choiceMixin.
Definition binop_countMixin := CanCountMixin nat_of_binopK.
Canonical binop_countType := Eval hnf in CountType binop binop_countMixin.
Definition binop_ordMixin := CanOrdMixin nat_of_binopK.
Canonical binop_ordType := Eval hnf in OrdType binop binop_ordMixin.

Inductive expr :=
| Var of string
| Bool of bool
| Num of int
| Binop of binop & expr & expr
| Neg of expr
| ENil
| Offset of expr
| Size of expr
| Cast of expr.

Fixpoint tree_of_expr e :=
  match e with
  | Var x => GenTree.Node 0 [:: GenTree.Leaf (pickle x)]
  | Bool b => GenTree.Node 1 [:: GenTree.Leaf (pickle b)]
  | Num n => GenTree.Node 2 [:: GenTree.Leaf (pickle n)]
  | Binop b e1 e2 => GenTree.Node 3 [:: GenTree.Leaf (pickle b);
                                        tree_of_expr e1; tree_of_expr e2]
  | Neg e => GenTree.Node 4 [:: tree_of_expr e]
  | ENil => GenTree.Node 5 [::]
  | Offset e => GenTree.Node 6 [:: tree_of_expr e]
  | Size e => GenTree.Node 7 [:: tree_of_expr e]
  | Cast e => GenTree.Node 8 [:: tree_of_expr e]
  end.

Fixpoint expr_of_tree t :=
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf x & _] => Var (odflt String.EmptyString (unpickle x))
  | GenTree.Node 1 [:: GenTree.Leaf b & _] => Bool (odflt true (unpickle b))
  | GenTree.Node 2 [:: GenTree.Leaf n & _ ] => Num (odflt (0 : int) (unpickle n))
  | GenTree.Node 3 [:: GenTree.Leaf b, e1, e2 & _ ] =>
    Binop (odflt Add (unpickle b)) (expr_of_tree e1) (expr_of_tree e2)
  | GenTree.Node 4 [:: e & _] => Neg (expr_of_tree e)
  | GenTree.Node 5 _ => ENil
  | GenTree.Node 6 [:: e & _] => Offset (expr_of_tree e)
  | GenTree.Node 7 [:: e & _] => Size (expr_of_tree e)
  | GenTree.Node 8 [:: e & _] => Cast (expr_of_tree e)
  | _ => Var String.EmptyString
  end.

Lemma tree_of_exprK : cancel tree_of_expr expr_of_tree.
Proof.
rewrite /expr_of_tree [@unpickle]lock.
by elim=> /= [x|b|n|b e1 -> e2 ->|e -> | |e ->|e ->|e ->] //;
rewrite -lock pickleK.
Qed.

Definition expr_eqMixin := CanEqMixin tree_of_exprK.
Canonical expr_eqType := Eval hnf in EqType expr expr_eqMixin.
Definition expr_choiceMixin := CanChoiceMixin tree_of_exprK.
Canonical expr_choiceType := Eval hnf in ChoiceType expr expr_choiceMixin.
Definition expr_countMixin := CanCountMixin tree_of_exprK.
Canonical expr_countType := Eval hnf in CountType expr expr_countMixin.
Definition expr_ordMixin := PcanOrdMixin (@pickleK expr_countType).
Canonical expr_ordType := Eval hnf in OrdType expr expr_ordMixin.
Canonical expr_nominalType := Eval hnf in [nominalType for expr by //].
Canonical expr_trivialNominalType := Eval hnf in [trivialNominalType for expr].

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

Fixpoint tree_of_com c :=
  match c with
  | Assn x e => GenTree.Node 0 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Load x e => GenTree.Node 1 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Store e1 e2 => GenTree.Node 2 [:: GenTree.Leaf (pickle e1); GenTree.Leaf (pickle e2)]
  | Alloc x e => GenTree.Node 3 [:: GenTree.Leaf (pickle x); GenTree.Leaf (pickle e)]
  | Free e => GenTree.Node 4 [:: GenTree.Leaf (pickle e)]
  | Skip => GenTree.Node 5 [::]
  | Seq c1 c2 => GenTree.Node 6 [:: tree_of_com c1; tree_of_com c2]
  | If e c1 c2 => GenTree.Node 7 [:: GenTree.Leaf (pickle e);
                                     tree_of_com c1;
                                     tree_of_com c2]
  | While e c => GenTree.Node 8 [:: GenTree.Leaf (pickle e); tree_of_com c]
  end.

Fixpoint com_of_tree t :=
  let var x := odflt String.EmptyString (unpickle x) in
  let exp e := odflt (Num 0) (unpickle e) in
  match t with
  | GenTree.Node 0 [:: GenTree.Leaf x; GenTree.Leaf e] => Assn (var x) (exp e)
  | GenTree.Node 1 [:: GenTree.Leaf x; GenTree.Leaf e] => Load (var x) (exp e)
  | GenTree.Node 2 [:: GenTree.Leaf e1; GenTree.Leaf e2] => Store (exp e1) (exp e2)
  | GenTree.Node 3 [:: GenTree.Leaf x; GenTree.Leaf e] => Alloc (var x) (exp e)
  | GenTree.Node 4 [:: GenTree.Leaf e] => Free (exp e)
  | GenTree.Node 5 [::] => Skip
  | GenTree.Node 6 [:: c1; c2] => Seq (com_of_tree c1) (com_of_tree c2)
  | GenTree.Node 7 [:: GenTree.Leaf e; c1; c2] => If (exp e) (com_of_tree c1) (com_of_tree c2)
  | GenTree.Node 8 [:: GenTree.Leaf e; c] => While (exp e) (com_of_tree c)
  | _ => Skip
  end.

Lemma tree_of_comK : cancel tree_of_com com_of_tree.
Proof.
elim=> [x e|x e|e1 e2|x e|e| |c1 IH1 c2 IH2|e c1 IH1 c2 IH2|e c IH] //=;
rewrite ?pickleK ?IH ?IH1 ?IH2 //; f_equal;
by apply: Some_inj; rewrite -[RHS]pickleK.
Qed.

Definition com_eqMixin := CanEqMixin tree_of_comK.
Canonical com_eqType := Eval hnf in EqType com com_eqMixin.
Definition com_choiceMixin := CanChoiceMixin tree_of_comK.
Canonical com_choiceType := Eval hnf in ChoiceType com com_choiceMixin.
Definition com_countMixin := CanCountMixin tree_of_comK.
Canonical com_countType := Eval hnf in CountType com com_countMixin.
Definition com_ordMixin := PcanOrdMixin (@pickleK com_countType).
Canonical com_ordType := Eval hnf in OrdType com com_ordMixin.
Canonical com_nominalType := Eval hnf in [nominalType for com by //].
Canonical com_trivialNominalType := Eval hnf in [trivialNominalType for com].

(** Type of pointers. [name] corresponds to an atom, in the nominal set
    sense. *)
Definition ptr := (name * int)%type.

(* FIXME: If we don't declare these, then many lemmas on partial maps do not
   work when applied to heaps.  The file structured.v contains some examples. *)

Canonical ptr_eqType := Eval hnf in [eqType of ptr].
Canonical ptr_choiceType := Eval hnf in [choiceType of ptr].
Canonical ptr_ordType := Eval hnf in [ordType of ptr].
Canonical ptr_nominalType := Eval hnf in [nominalType of ptr].

(** Pointers values contain an additional immutable size field, initialized at
    allocation time. *)
Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of ptr & int
| VNil.

Definition sum_of_value v :=
  match v with
  | VBool b => inl b
  | VNum n => inr (inl n)
  | VPtr p sz => inr (inr (inl (p, sz)))
  | VNil => inr (inr (inr tt))
  end.

Definition value_of_sum v :=
  match v with
  | inl b => VBool b
  | inr (inl n) => VNum n
  | inr (inr (inl (p, sz))) => VPtr p sz
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
  | VPtr p sz => VPtr (rename pm p) sz
  | VNil => VNil
  end.
Proof. by case: v. Qed.

Lemma namesvE v :
  names v =
  match v with
  | VPtr p _ => fset1 p.1
  | _ => fset0
  end.
Proof.
by case: v=> [b|n|[i n] ?|] //=; rewrite -2![RHS]fsetU0.
Qed.

Global Instance VBool_eqvar : {eqvar VBool}.
Proof. by move=> s b _ <-. Qed.

Global Instance VNum_eqvar : {eqvar VNum}.
Proof. by move=> s n _ <-. Qed.

Global Instance VPtr_eqvar : {eqvar VPtr}.
Proof. by move=> s p _ <-; finsupp. Qed.

Global Instance VNil_eqvar : {eqvar VNil}.
Proof. by []. Qed.

Notation locals := {fmap string -> value}.
Notation heap := {fmap ptr -> value}.

Implicit Types (ls : locals) (h : heap) (s : locals * heap).

Definition mkblock (b : name) vs : heap :=
  uncurrym (setm emptym b
                 (mkfmapfp (fun i => if i is Posz n then
                                       Some (nth VNil vs n)
                                     else None)
                           [seq Posz n | n <- iota 0 (size vs)])).

Lemma mkblockE p b vs :
  mkblock b vs p =
  if p.1 == b then
    if p.2 is Posz n then
      if n < size vs then Some (nth VNil vs n)
      else None
    else None
  else None.
Proof.
rewrite /mkblock uncurrymE setmE.
case: ifP=> //= _; rewrite mkfmapfpE.
case: p.2=> [n|n] /=.
  rewrite mem_map; last by move=> ?? [->].
  by rewrite mem_iota /= add0n.
by case: ifP.
Qed.

Global Instance mkblock_eqvar : {eqvar mkblock}.
Proof.
move=> s i _ <- vs _ <-.
eapply getm_nomR => - [i' [n|n]] _ <-; rewrite !mkblockE /=; last by finsupp.
(* FIXME: All this rewriting should not be needed *)
rewrite -[size (rename s vs)]size_eqvar renameT; finsupp.
Qed.

Definition eval_binop b v1 v2 :=
  match b, v1, v2 with
  | Add, VNum n1, VNum n2 => VNum (n1 + n2)
  | Add, VPtr p sz, VNum n
  | Add, VNum n, VPtr p sz => VPtr (p.1, p.2 + n) sz
  | Add, _, _ => VNil
  | Sub, VNum n1, VNum n2 => VNum (n1 - n2)
  | Sub, VPtr p sz, VNum n => VPtr (p.1, p.2 - n) sz
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

(** Function [eval_expr] computes the value of an expression [e] given a local
store [ls]. It takes an additional argument [cast] which determines how the cast
operator is interpreted: when [cast = true], cast is just the identity; when
[cast = false], cast converts the block identifier to an integer. *)

Fixpoint eval_expr cast e ls :=
  match e with
  | Var x => odflt VNil (ls x)
  | Bool b => VBool b
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr cast e1 ls) (eval_expr cast e2 ls)
  | ENil => VNil
  | Neg e =>
    if eval_expr cast e ls is VBool b then VBool (~~ b)
    else VNil
  | Offset e =>
    if eval_expr cast e ls is VPtr p _ then VNum p.2 else VNil
  | Size e =>
    if eval_expr cast e ls is VPtr _ sz then VNum sz else VNil
  | Cast e =>
    let v := eval_expr cast e ls in
    if cast then v
    else if eval_expr cast e ls is VPtr p _ then VNum (val p.1) else VNil
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
Definition result_ordMixin (T : ordType) :=
  CanOrdMixin (@sum_of_resultK T).
Canonical result_ordType (T : ordType) :=
  Eval hnf in OrdType (result T) (result_ordMixin T).
Definition result_nominalMixin (T : nominalType) :=
  BijNominalMixin (@sum_of_resultK T) (@result_of_sumK T).
Canonical result_nominalType (T : nominalType) :=
  Eval hnf in NominalType (result T) (result_nominalMixin T).

Section Nominal.

Variable T : nominalType.

Global Instance Done_eqvar : {eqvar @Done T}.
Proof. by move=> s x _ <-. Qed.

Lemma renameresE pm (r : result T) :
  rename pm r =
  match r with
  | Done x => Done (rename pm x)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: r. Qed.

Lemma namesresE (r : result T) :
  names r = if r is Done x then names x else fset0.
Proof. by case: r. Qed.

End Nominal.

Section Restriction.

Variable T : restrType.

Definition hide_result A (r : result T) :=
  match r with
  | Done x => Done (hide A x)
  | Error => Error
  | NotYet => NotYet
  end.

Lemma hide_result_law : Restriction.law hide_result.
Proof.
rewrite /hide_result; constructor.
- move=> s A _ <- [x| |] _ <- //=; finsupp.
- by move=> A [x| |] //; rewrite hideI.
- by move=> ?? [x| |] //; rewrite hideU.
- by move=> [x| |] //; rewrite hide0.
by move=> ? [x| |] /=; rewrite ?hideP ?fdisjoints0.
Qed.

Definition result_restrMixin := RestrMixin hide_result_law.
Canonical result_restrType := RestrType (result T) result_restrMixin.

End Restriction.

Fixpoint eval_com cast c s k : result (locals * heap) :=
  if k is S k' then
    match c with
    | Assn x e =>
      Done (setm s.1 x (eval_expr cast e s.1), s.2)

    | Load x e =>
      if eval_expr cast e s.1 is VPtr p _ then
        if s.2 p is Some v then Done (setm s.1 x v, s.2)
        else Error
      else Error

    | Store e e' =>
      if eval_expr cast e s.1 is VPtr p _ then
        if updm s.2 p (eval_expr cast e' s.1) is Some h' then Done (s.1, h')
        else Error
      else Error

    | Alloc x e =>
      if eval_expr cast e s.1 is VNum (Posz n) then
        Done (let i := fresh (names s) in
              (setm s.1 x (VPtr (i, 0 : int) n),
               unionm (mkblock i (nseq n (VNum 0))) s.2))
      else Error

    | Free e =>
      if eval_expr cast e s.1 is VPtr p _ then
        if p.2 == 0 then
          if p.1 \in domm ((@currym _ _ _ : heap -> _) s.2) then
            Done (s.1, filterm (fun (p' : ptr) _ => p'.1 != p.1) s.2)
          else Error
        else Error
      else Error

    | Skip => Done s

    | Seq c1 c2 =>
      match eval_com cast c1 s k' with
      | Done s' => eval_com cast c2 s' k'
      | Error => Error
      | NotYet => NotYet
      end

    | If e ct ce =>
      if eval_expr cast e s.1 is VBool b then
        eval_com cast (if b then ct else ce) s k'
      else Error

    | While e c =>
      if eval_expr cast e s.1 is VBool b then
        eval_com cast (if b then Seq c (While e c) else Skip) s k'
      else Error
    end
  else NotYet.

Section Monotonicity.

(** The semantics defined as a function is consistent, in the sense
that increasing the maximum number of steps it can run for can only
cause it to produce a better result. *)

Definition refine_result (T : eqType) (r1 r2 : result T) :=
  (r1 == NotYet) || (r1 == r2).

Lemma eval_com_leq cast s c k k' :
  k <= k' ->
  refine_result (eval_com cast c s k) (eval_com cast c s k').
Proof.
move=> Pk; elim: k' k Pk s c => [|k' IH] [|k] // /IH {IH} IH s.
rewrite /refine_result.
case=> [x e|x e|e e'|x e|e| |c1 c2|e ct ce|e c] /=; try by rewrite eqxx ?orbT.
- case/orP: (IH s c1) => [/eqP -> //|/eqP ->].
  case: (eval_com _ c1 _ _) => [s'| |] //=.
  by eauto.
- by case: eval_expr=> //= b; eauto.
by case: eval_expr=> //= b; eauto.
Qed.

End Monotonicity.

(** Free variables that occur in a command or expression. *)

Fixpoint vars_e e :=
  match e with
  | Var x => fset1 x
  | Bool _ => fset0
  | Num _ => fset0
  | Binop _ e1 e2 => vars_e e1 :|: vars_e e2
  | ENil => fset0
  | Neg e => vars_e e
  | Offset e => vars_e e
  | Size e => vars_e e
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

(** Potentially modified variables in a command. *)

Fixpoint mod_vars_c c :=
  match c with
  | Assn x _   => fset1 x
  | Load x _   => fset1 x
  | Store _ _  => fset0
  | Alloc x _  => fset1 x
  | Free _     => fset0
  | Skip       => fset0
  | Seq c1 c2  => mod_vars_c c1 :|: mod_vars_c c2
  | If _ c1 c2 => mod_vars_c c1 :|: mod_vars_c c2
  | While _ c  => mod_vars_c c
  end.

Lemma mod_vars_cP cast s s' c x k :
  eval_com cast c s k = Done s' ->
  x \notin mod_vars_c c ->
  s'.1 x = s.1 x.
Proof.
elim: k s s' c=> [|k IH] //= [ls h] s'.
case=> [x' e|x' e|e e'|x' e|e| |c1 c2|e c1 c2|e c] /=; rewrite 1?in_fset1.
- by move=> [<-] {s'}; rewrite setmE => /negbTE ->.
- case: eval_expr=> // p sz.
  case: getm=> //= v [<-] {s'}.
  by rewrite setmE => /negbTE ->.
- case: eval_expr=> // p sz.
  by case: updm=> //= h' [<-] {s'} _.
- case: eval_expr=> [| [n|] | |] //= [<-] {s'}.
  by rewrite setmE => /negbTE ->.
- case: eval_expr=> // p sz.
  by case: ifP=> // Hp; case: ifP=> //= Hp' [<-].
- by move=> [<-].
- case e1: eval_com => [s''| |] //= e2.
  rewrite in_fsetU=> /norP [nc1 nc2].
  by rewrite (IH _ _ _ e2) // (IH _ _ _ e1).
- rewrite in_fsetU.
  by case: eval_expr => [[] | | | ] //= he /norP [nc1 nc2];
  rewrite (IH _ _ _ he).
- by case: eval_expr=> [[] | | | ] //= he hx;
  rewrite (IH _ _ _ he) //= fsetUid.
Qed.

Lemma mod_vars_c_subset c : fsubset (mod_vars_c c) (vars_c c).
Proof.
elim: c=> [x e|x e|e e'|x e|e| |c1 IH1 c2 IH2|e c1 IH1 c2 IH2|e c IH] /=;
rewrite ?fsub0set ?fsub1set ?in_fsetU1 ?eqxx //.
- by rewrite fsetUSS.
- by rewrite -fsetUA; apply: fsubsetU; rewrite fsetUSS // orbT.
by rewrite fsubsetU // IH orbT.
Qed.

(** Basic lemmas about the semantics *)

Lemma eval_expr_unionm cast ls1 ls2 e :
  fsubset (vars_e e) (domm ls1) ->
  eval_expr cast e (unionm ls1 ls2) =
  eval_expr cast e ls1.
Proof.
elim: e => [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=.
- by rewrite fsub1set unionmE => /dommP [v ->].
- by rewrite fsubUset=> /andP [/IH1 {IH1} -> /IH2 {IH2} ->].
- by case: cast IH=> // IH sub; rewrite IH.
- by case: cast IH=> // IH sub; rewrite IH.
- by case: cast IH=> // IH sub; rewrite IH.
by case: cast IH=> // IH sub; rewrite IH.
Qed.

Lemma eval_binop_names b v1 v2 :
  fsubset (names (eval_binop b v1 v2)) (names (v1, v2)).
Proof.
case: b v1 v2=> [] [b1|n1|p1 sz1|] [b2|n2|p2 sz2|] //=;
  try by rewrite fsub0set.
- by rewrite fsubsetU //= !namesvE fsubsetxx orbT.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
by rewrite fsubsetU //= !namesvE fsubsetxx.
Qed.

Lemma eval_expr_names cast ls e :
  fsubset (names (eval_expr cast e ls)) (names ls).
Proof.
elim: e=> [x|b|n|b e1 IH1 e2 IH2|e IH| |e IH|e IH|e IH] //=;
  try by rewrite fsub0set.
- case get_x: (ls x) => [[b|n|p|]|] //=; try by rewrite fsub0set.
  apply/fsubsetP=> i; rewrite namesvE => /fset1P -> {i}.
  apply/namesmP; eapply PMFreeNamesVal; eauto.
  by rewrite namesvE; apply/namesnP.
- by rewrite (fsubset_trans (eval_binop_names b _ _)) // fsubUset IH1 IH2.
- by case: eval_expr => // *; rewrite fsub0set.
- by case: eval_expr => // *; rewrite fsub0set.
- by case: eval_expr => // *; rewrite fsub0set.
case: cast IH=> //.
by case: (eval_expr _ _ _)=> [b|n|p|]; rewrite fsub0set.
Qed.

Lemma domm_mkblock i vs :
  domm (mkblock i vs) = fset [seq (i, Posz n) | n <- iota 0 (size vs)].
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP => /= - [i' n].
  move=> /dommP [v].
  rewrite mkblockE /= in_fset.
  have [-> {i'}|] //= := altP eqP.
  case: n=> [n|] //=.
  case: ifP=> [n_vs|] //= [e].
  apply/mapP; exists n=> //.
  by rewrite mem_iota.
rewrite in_fset=> /mapP /= [n'].
rewrite mem_iota /= add0n => n_vs [-> ->].
apply/dommP; exists (nth VNil vs n').
by rewrite mkblockE /= eqxx n_vs.
Qed.

Lemma names_domm_mkblock i vs :
  names (domm (mkblock i vs)) = if nilp vs then fset0 else fset1 i.
Proof.
case: ifP=> [/nilP ->|nnil_vs].
  rewrite (_ : mkblock i [::] = emptym) ?domm0 ?namesfs0 //.
  apply/eq_fmap=> p; rewrite mkblockE /= emptymE.
  by case: ifP=> //; case: p.2.
rewrite domm_mkblock names_fset.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> i'.
  case/namessP=> /= [[i'' n] /mapP [n' ?] [-> ?]].
  by rewrite in_fsetU /= namesT in_fset0 orbF namesnE.
move=> /fset1P ->.
apply/namessP; exists (i, Posz 0).
  apply/mapP; exists 0=> //.
  rewrite mem_iota /= add0n.
  by case: vs nnil_vs.
by rewrite in_fsetU /= namesT in_fset0 orbF namesnE in_fset1 eqxx.
Qed.

Lemma codomm_mkblock i vs : codomm (mkblock i vs) = fset vs.
Proof.
apply/eqP; rewrite eqEfsubset; apply/andP; split; apply/fsubsetP=> v.
  case/codommP=> /= - [i' n].
  rewrite mkblockE /=.
  have [_ {i'}|] //= := altP eqP.
  case: n=> [n|] //=.
  case: ifP=> [n_vs|] //= [<-].
  rewrite in_fset.
  by apply/mem_nth.
rewrite in_fset => v_vs.
apply/codommP.
exists (i, Posz (index v vs)).
by rewrite mkblockE /= eqxx index_mem v_vs nth_index.
Qed.

Lemma names_codomm_mkblock i vs :
  names (codomm (mkblock i vs)) = names vs.
Proof. by rewrite codomm_mkblock names_fset. Qed.

Lemma names_mkblock i vs :
  names (mkblock i vs) = if nilp vs then fset0 else i |: names vs.
Proof.
rewrite namesmE names_domm_mkblock names_codomm_mkblock.
case: vs=> //=.
by rewrite fset0U namessE.
Qed.

Lemma names_mkblock_fsubset i vs :
  fsubset (names (mkblock i vs)) (i |: names vs).
Proof.
by rewrite names_mkblock fun_if if_arg fsub0set fsubsetxx if_same.
Qed.

Lemma fdisjoint_names_domm h1 h2 :
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  fdisjoint (domm h1) (domm h2).
Proof.
move=> /fdisjointP dis; apply/fdisjointP=> p Pp.
have /dis Pi: p.1 \in names (domm h1).
  by apply/namesfsP; exists p=> //=; apply/fsetUP; left; apply/namesnP.
apply: contra Pi=> Pi; apply/namesfsP; exists p=> //.
by apply/fsetUP; left; apply/namesnP.
Qed.

Definition stateu s1 s2 : locals * heap :=
  (unionm s1.1 s2.1, unionm s1.2 s2.2).

Lemma eval_com_vars safe s s' c k :
  fsubset (vars_c c) (domm s.1) ->
  eval_com safe c s k = Done s' ->
  domm s'.1 = domm s.1.
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=;
rewrite ?fsubU1set ?fsubUset.
- case/andP=> [Px Pe] [<-]; rewrite domm_set /=.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case/andP=> [Px Pe].
  case: eval_expr => // p sz; case: getm=> [v|] //= [<-] {s'}.
  rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsubsetUr.
- case/andP=> Pe Pe'.
  by case: eval_expr => // p sz; rewrite /updm; case: getm=> [v|] //= [<-] {s'}.
- case: eval_expr => [|[n|]| |] // /andP [Px Pe] [<-] /=.
  rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split; last exact: fsubsetUr.
  by rewrite fsubUset fsubsetxx andbT fsub1set.
- case: eval_expr => // p sz.
  by have [|]:= altP eqP=> // _; case: ifP=> //= in_h1 sub [<-] {s'}.
- by move=> _ [<-] {s'}.
- case/andP=> vars_c1 vars_c2.
  case ev_c1: (eval_com _ _ _) => [s''| |] //= ev_c2.
  move: vars_c2; rewrite -(IH _ _ _ vars_c1 ev_c1) => vars_c2.
  by rewrite -(IH _ _ _ vars_c2 ev_c2).
- case: eval_expr=> // - b.
  by rewrite -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eapply IH; eauto.
case: eval_expr=> // - [] P; apply: IH; try by rewrite fsub0set.
by rewrite /= fsetUC -fsetUA fsetUid fsubUset.
Qed.

End Basic.

Arguments Error {_}.
Arguments NotYet {_}.

Infix "∪" := stateu (at level 40, left associativity) : state_scope.

Instance stateu_eqvar : {eqvar stateu}.
Proof. by rewrite /stateu; finsupp. Qed.
