Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Definition int_partOrdMixin :=
  (@PartOrdMixin int <=%R (@Num.Theory.lerr _) (@Num.Theory.ler_trans _)
                          (@Num.Theory.ler_anti _))%R.

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

Lemma renamevE pm v :
  rename pm v =
  match v with
  | VBool b => VBool b
  | VNum n => VNum n
  | VPtr p => VPtr (rename pm p)
  | VNil => VNil
  end.
Proof. by case: v. Qed.

Definition locals := {partmap string -> value}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition alloc ls h n :=
  locked
  (let b := fresh (names (ls, h)) in
   (b, unionm (mkpartmapf (fun _ => VNum 0) [seq (b, Posz i) | i <- iota 0 n]) h)).

Definition free h i :=
  locked
  (if fpick (fun p => p.1 == i) (domm h) then
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
        let res := alloc ls h n in
        Done (setm ls x (VPtr (res.1, 0 : int))) res.2
      else Error

    | Free e =>
      if eval_expr ls e is VPtr p then
        if free h p.1 is Some h' then
          Done ls h'
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

Lemma rename_eval_binop pm b v1 v2 :
  rename pm (eval_binop b v1 v2) =
  eval_binop b (rename pm v1) (rename pm v2).
Proof.
case: b v1 v2 => [] [b1|n1|p1|] [b2|n2|p2|] //=.
by rewrite (can_eq (renameK pm)).
Qed.

Lemma rename_eval_expr pm ls e :
  rename pm (eval_expr ls e) =
  eval_expr (rename pm ls) e.
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2|] //=.
  rewrite renamemE /= [rename _ x]/rename /= /trivial_rename /=.
  by case: (ls x)=> [v|] //=.
by rewrite rename_eval_binop IH1 IH2.
Qed.

Lemma renamerE pm r :
  rename pm r =
  match r with
  | Done ls h => Done (rename pm ls) (rename pm h)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: r. Qed.

Lemma rename_free pm h i :
  rename pm (free h i) = free (rename pm h) (rename pm i).
Proof.
rewrite /free; unlock.
case: fpickP=> [p' /eqP Pp' in_domm'|] //;
case: fpickP=> [p'' /eqP Pp'' in_domm''|] //=; try subst i.
- rewrite renameoE /= renamem_filter; congr Some.
  apply: eq_filterm=> p _ /=.
  by rewrite (can2_eq (renameKV pm) (renameK pm)).
- move=> /(_ (rename pm p')); rewrite domm_rename renamefsE.
  rewrite (mem_imfset_inj _ _ (@rename_inj _ pm)) => /(_ in_domm').
  by rewrite renamepE /= eqxx.
move=> /(_ (rename (pm^-1)%fperm p'')).
rewrite domm_rename renamefsE in in_domm''.
case/imfsetP: in_domm'' => [p' Pp' ?]; subst p''.
rewrite renameK => /(_ Pp').
rewrite renamepE /= in Pp''; move/rename_inj in Pp''; subst i.
by rewrite eqxx.
Qed.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Lemma renaming ls h c k pm :
  exists pm',
    eval_com (rename pm ls) (rename pm h) c k =
    rename pm' (eval_com ls h c k).
Proof.
elim: k ls h c pm => [//=|k IH] ls h c pm; first by exists fperm_one.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c].
- by exists pm; rewrite /= renamerE renamem_set rename_eval_expr.
- exists pm=> /=.
  rewrite -rename_eval_expr; case: (eval_expr ls e)=> //= p.
  rewrite renamemE renameK; case Pp: (h p)=> [v|] //=.
  by rewrite renamerE renamem_set.
- exists pm=> /=.
  rewrite -rename_eval_expr; case: (eval_expr ls e)=> //= p.
  rewrite /updm renamemE renameK -rename_eval_expr -renamem_set.
  by case: (h p) => [v|] //= [<- <-] //=.
- rewrite /= -rename_eval_expr.
  case: (eval_expr ls e) => [|[n|]| |]; try by exists pm.
  rewrite renamevE /alloc -2!lock /=.
  set i := fresh (names (ls, h)).
  set i' := fresh (names _).
  set i'' := fresh (supp pm :|: names (ls, h) :|: names (rename pm (ls, h))).
  pose pm' := fperm2 i' i'' * pm * fperm2 i i''; exists pm'.
  have Pi: pm' i = i'.
    do 2![rewrite fpermM /=]; apply: (canLR (fpermKV _)).
    rewrite fperm2V 2!fperm2L; apply/suppPn.
    move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
    by apply: contra=> Pi''; rewrite 3!in_fsetU Pi''.
  have Pj: forall j, j \in names (ls, h) -> pm' j = pm j.
    move=> j Pj {Pi}; rewrite {}/pm'; do 2![rewrite fpermM /=].
    rewrite [in pm _]fperm2D ?fperm2D //.
    + move: (freshP (names (rename pm ls, rename pm h))).
      apply: contra => /eqP; rewrite /i' => <-.
      move: (mem_imfset (rename pm) Pj).
      by rewrite -names_rename.
    + move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
      apply: contra => /eqP; rewrite /i'' => <-.
      rewrite in_fsetU; move: (mem_imfset (rename pm) Pj).
      by rewrite -names_rename renamenE => ->; rewrite orbT.
    + move: (freshP (names (ls, h))).
      by apply: contra => /eqP; rewrite /i => <-.
    move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
    apply: contra => /eqP; rewrite /i'' => <-.
    by rewrite 2!in_fsetU Pj orbT.
  rewrite renamerE renamem_set renamevE renamepE /=; congr Done.
    congr setm.
      by apply: eq_in_rename=> j Pj'; rewrite Pj // in_fsetU /= Pj'.
    by rewrite renamenE Pi.
  apply/eq_partmap=> p; rewrite unionmE 2!renamemE unionmE 2!mkpartmapfE.
  rewrite (_ : [seq (i, Posz n') | n' <- iota 0 n] =
               map (rename pm'^-1) [seq (i', Posz n') | n' <- iota 0 n]).
    rewrite (mem_map (@rename_inj _ _)).
    case: (ifP (p \in _))=> //= _; rewrite -2!renamemE; congr getm; move{p}.
    apply: (@eq_in_rename _ pm pm' h)=> p Pp; rewrite Pj //.
    by rewrite in_fsetU Pp orbT.
  rewrite -[in RHS]map_comp /=; apply: eq_map => n' /=; rewrite renamepE /=.
  by rewrite renamenE -Pi fpermK.
- exists pm; rewrite /eval_com -rename_eval_expr.
  case: (eval_expr ls e) => // p; rewrite renamevE.
  by rewrite renamepE /= -rename_free; case: (free _ _) => [h'|] //=.
- by exists pm.
- have /= [pm' ->] := IH ls h c1 pm.
  case: (eval_com _ _ c1 _)=> [ls' h'| |]; try by exists pm'.
  by have /= [pm'' ->] := IH ls' h' c2 pm'; eauto.
- rewrite /= -rename_eval_expr.
  by case: (eval_expr ls e) => [[]| | |] //=; exists pm.
- rewrite /= -rename_eval_expr.
  by case: (eval_expr ls e) => [[]| | |] //=; exists pm.
Qed.

End Def.
